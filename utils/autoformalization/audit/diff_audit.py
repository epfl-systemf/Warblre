#!/usr/bin/env python3
"""
Diff-based comment/code audit for Rocq/Coq definitions.

Inspired by comment_code_audit.py, but instead of auditing every definition in
a fixed list of files, this script:
  1. Runs `git diff` against HEAD~N (N configurable via --commits)
  2. Determines which .v files in mechanization/spec/ were modified
  3. Extracts only the Definition / Fixpoint blocks whose line ranges overlap
     with the changed lines
  4. Sends those blocks to the configured LLM(s) for review
  5. Saves JSON + HTML results under results/<date>/<model>/

Run this script from the audit directory (same place as comment_code_audit.py)
or from anywhere inside the git repository.
"""

import os
import sys
import json
import datetime
import argparse
import re
import html
import subprocess
from dotenv import load_dotenv
from openai import OpenAI

# ------------------------------
#  Config
# ------------------------------
KEYWORDS = [
    "Definition",
    "Fixpoint",
]

pattern = re.compile(rf"^\s*({'|'.join(KEYWORDS)})\b")
result_folder = "results"


# ------------------------------
#  Git helpers
# ------------------------------
def get_repo_root():
    """Return the absolute path of the current git repository root."""
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True
    )
    return result.stdout.strip()


def get_changed_files_and_lines(num_commits, repo_root):
    """
    Return a dict:
        relative_filepath -> list of (start_line, end_line) tuples
    where each tuple describes a contiguous chunk of changed lines in the
    *new* version of the file (i.e. the line numbers you would see if you
    opened the file right now).
    """
    if num_commits <= 0:
        return {}

    diff_name = subprocess.run(
        ["git", "diff", "--name-only", f"HEAD~{num_commits}"],
        capture_output=True, text=True, check=True,
        cwd=repo_root
    )
    changed_files = [
        f.strip()
        for f in diff_name.stdout.strip().split("\n")
        if f.strip()
    ]

    file_changes = {}
    for rel_path in changed_files:
        # Only consider specification files (ignore proofs / semantics)
        if not rel_path.endswith(".v") or "spec/" not in rel_path:
            continue

        diff_text = subprocess.run(
            ["git", "diff", "-U0", f"HEAD~{num_commits}", "--", rel_path],
            capture_output=True, text=True, check=True,
            cwd=repo_root
        ).stdout

        ranges = []
        for line in diff_text.split("\n"):
            if line.startswith("@@"):
                # e.g. @@ -10,5 +20,7 @@  →  +20,7 means start=20 count=7
                m = re.search(r'\+(\d+)(?:,(\d+))?', line)
                if m:
                    start = int(m.group(1))
                    count = int(m.group(2)) if m.group(2) is not None else 1
                    if count > 0:
                        ranges.append((start, start + count - 1))

        if ranges:
            file_changes[rel_path] = ranges

    return file_changes


# ------------------------------
#  Definition extraction
# ------------------------------
def extract_defs_with_ranges(filepath):
    """
    Parse a Rocq file and return two parallel lists:
        defs  – strings of the extracted blocks (including preceding comments)
        ranges – (start_line, end_line) tuples, 1-indexed
    """
    defs = []
    ranges = []
    current = []
    last_added_index = 0

    with open(filepath) as fh:
        lines = fh.readlines()

    i = 0
    inside_comment = False
    while i < len(lines):
        line = lines[i]

        if pattern.match(line):
            start_idx = last_added_index

            while i < len(lines):
                stripped = lines[i].strip()
                current.append(lines[i])

                if stripped.startswith("(*"):
                    inside_comment = True

                if stripped.endswith(".") and not inside_comment:
                    break

                if stripped.endswith("*)"):
                    inside_comment = False

                i += 1

            defs.append("".join(current))
            ranges.append((start_idx + 1, i + 1))   # convert to 1-indexed
            current = []
            last_added_index = i + 1

        i += 1

    return defs, ranges


def ranges_overlap(def_start, def_end, changed_ranges):
    """Return True iff [def_start, def_end] intersects any changed range."""
    for c_start, c_end in changed_ranges:
        if def_end >= c_start and def_start <= c_end:
            return True
    return False


def extract_changed_defs(num_commits, repo_root):
    """
    Walk the files changed in the last `num_commits` commits and extract
    every Definition / Fixpoint block that overlaps with a changed line.
    Returns a list of dicts with keys: file, start_line, end_line, content.
    """
    changed_files = get_changed_files_and_lines(num_commits, repo_root)
    all_defs = []

    for rel_path, change_ranges in changed_files.items():
        full_path = os.path.join(repo_root, rel_path)
        if not os.path.exists(full_path):
            continue            # file was deleted in the diff window

        defs, ranges = extract_defs_with_ranges(full_path)
        for d, (s, e) in zip(defs, ranges):
            if ranges_overlap(s, e, change_ranges):
                all_defs.append({
                    "file": rel_path,
                    "start_line": s,
                    "end_line": e,
                    "content": d,
                })

    return all_defs


# ------------------------------
#  Format helpers (same as comment_code_audit.py)
# ------------------------------
def format_question(prompt: str, code: str) -> str:
    return f"""
{prompt}

{code}
""".strip()


def extract_json_from_answer(answer: str):
    cleaned = answer.strip()
    cleaned = re.sub(r"^```json\s*", "", cleaned)
    cleaned = re.sub(r"^```", "", cleaned)
    cleaned = re.sub(r"\s*```$", "", cleaned)

    try:
        return json.loads(cleaned)
    except json.JSONDecodeError:
        pass

    json_match = re.search(r'\{.*\}', cleaned, re.DOTALL)
    if json_match:
        try:
            return json.loads(json_match.group())
        except json.JSONDecodeError:
            pass

    return {"match": False, "reason": "Failed to parse JSON response"}


# ------------------------------
#  Main
# ------------------------------
def main():
    parser = argparse.ArgumentParser(
        description="Audit Rocq definitions changed in the last N commits."
    )
    parser.add_argument(
        "--commits", "-n",
        type=int,
        default=1,
        help="Number of commits to look back (default: 1)"
    )
    parser.add_argument(
        "--files",
        nargs="*",
        help="Restrict audit to these specific files (paths relative to repo root)"
    )
    parser.add_argument(
        "--start",
        type=int,
        default=0,
        help="Start at definition index X (0-based)"
    )
    parser.add_argument(
        "--end",
        type=int,
        default=None,
        help="End at definition index X (exclusive)"
    )

    args = parser.parse_args()

    repo_root = get_repo_root()
    print(f"Repository root : {repo_root}")
    print(f"Commits back    : {args.commits}")

    defs = extract_changed_defs(args.commits, repo_root)

    # Optional file filter
    if args.files:
        allowed = set(args.files)
        defs = [d for d in defs if d["file"] in allowed]

    print(f"Changed definitions found: {len(defs)}")
    if not defs:
        print("Nothing to audit – exiting.")
        return

    # Apply slice
    start = args.start
    end = args.end if args.end is not None else len(defs)
    defs = defs[start:end]
    print(f"Auditing definitions {start}–{end - 1}  ({len(defs)} item(s)).\n")

    # Load local configs (relative to this script's directory)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = os.path.join(script_dir, "config.json")
    prompt_path = os.path.join(script_dir, "prompts.json")

    with open(config_path, "r") as fh:
        model_configs = json.load(fh)
    with open(prompt_path, "r") as fh:
        prompt_data = json.load(fh)

    system_prompt = prompt_data["system"]
    prompts = prompt_data["prompts"]

    load_dotenv()
    api_key = os.getenv("API_KEY")

    # =============================
    #  Loop over models  &  prompts
    # =============================
    for model_config in model_configs:
        results = []
        model_name = model_config["model"]
        base_url = model_config["base_url"]
        gen_config = model_config["generation"]

        client = OpenAI(base_url=base_url, api_key=api_key)

        for prompt in prompts:
            for idx, definition in enumerate(defs, start=1):
                meta = (
                    f"{definition['file']}:{definition['start_line']}"
                    f"-{definition['end_line']}"
                )
                print(
                    f"[MODEL: {model_name}] "
                    f"definition {idx}/{len(defs)}  –  {meta}"
                )

                header = f"--- {meta} ---"
                question = format_question(prompt, f"{header}\n\n{definition['content']}")

                try:
                    response = client.chat.completions.create(
                        model=model_name,
                        messages=[
                            {"role": "system", "content": system_prompt},
                            {"role": "user", "content": question},
                        ],
                        **gen_config
                    )
                    answer = response.choices[0].message.content

                    results.append({
                        "question": question,
                        "answer": answer,
                        "file": definition["file"],
                        "start_line": definition["start_line"],
                        "end_line": definition["end_line"],
                    })
                except Exception as exc:
                    print(f"  ERROR: {exc}")
                    results.append({
                        "question": question,
                        "answer": None,
                        "error": str(exc),
                        "file": definition["file"],
                        "start_line": definition["start_line"],
                        "end_line": definition["end_line"],
                    })

        # ------------------------------
        #  Persist results
        # ------------------------------
        now = datetime.datetime.now()
        timestamp = now.strftime("%Y-%m-%d_%H-%M-%S")
        date_folder = now.strftime("%Y-%m-%d")
        json_name = f"diff_results_{timestamp}.json"

        output = {
            "timestamp": timestamp,
            "model": model_name,
            "generation_config": gen_config,
            "prompt_file": "prompts.json",
            "commits_back": args.commits,
            "results": results,
        }

        out_dir = os.path.join(result_folder, date_folder, model_name)
        os.makedirs(out_dir, exist_ok=True)

        json_path = os.path.join(out_dir, json_name)
        with open(json_path, "w") as fh:
            json.dump(output, fh, indent=2)
        print(f"\nDone. JSON saved to {json_path}")

        # ---- HTML ----
        html_content = """\
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Coq Diff-Based Mechanization Review</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        h2 { color: #2c3e50; }
        pre { background-color: #f4f4f4; padding: 10px; border-radius: 5px; overflow-x: auto; }
        .question { margin-bottom: 30px; }
        .answer { margin-top: 10px; background-color: #e8f5e9; padding: 10px; border-radius: 5px; }
        .meta { color: #666; font-size: 0.9em; margin-bottom: 5px; }
    </style>
</head>
<body>
<h1>Diff-Based Coq Mechanization Review Results</h1>
"""

        for i, item in enumerate(output.get("results", []), start=1):
            meta = (
                f"{item.get('file', '')}:"
                f"{item.get('start_line', '')}-{item.get('end_line', '')}"
            )
            q_html = html.escape(item.get("question", ""))
            a_html = html.escape(str(item.get("answer") or ""))
            html_content += f"""
<div class="question">
    <h2>Sample {i}</h2>
    <div class="meta">{meta}</div>
    <h3>Code / Comments:</h3>
    <pre>{q_html}</pre>
    <h3>Review / Answer:</h3>
    <div class="answer"><pre>{a_html}</pre></div>
</div>
"""

        html_content += "</body>\n</html>\n"

        html_name = f"diff_results_{timestamp}.html"
        html_path = os.path.join(out_dir, html_name)
        with open(html_path, "w", encoding="utf-8") as fh:
            fh.write(html_content)
        print(f"HTML saved to {html_path}\n")


if __name__ == "__main__":
    main()
