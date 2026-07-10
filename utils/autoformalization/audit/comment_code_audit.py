import os
import json
import datetime
import argparse
import re
import html
import json
from dotenv import load_dotenv
from openai import OpenAI
import argparse

KEYWORDS = [
    "Definition",
    "Fixpoint",
]

pattern = re.compile(rf"^\s*({'|'.join(KEYWORDS)})\b")


def extract_defs(filename):
    defs = []
    current = []
    last_added_index = 0

    with open(filename) as f:
        lines = f.readlines()
    
    i = 0
    insideComment = False
    while i < len(lines):
        line = lines[i]

        if pattern.match(line):
            # Include everything from last_added_index up to current line
            current = lines[last_added_index:i]

            # Start collecting the current definition
            while i < len(lines):
                line = lines[i].strip()
                current.append(lines[i])
                if line.startswith("(*"):
                    insideComment = True
                
                if line.endswith(".") and not insideComment:
                    break

                if line.endswith("*)"):
                    insideComment = False
                i += 1

            defs.append("".join(current))
            current = []

            # Save the index of the last line added
            last_added_index = i + 1

        i += 1

    return defs

result_folder = "results"

# -----------------------------
# Format Helper
# -----------------------------
def format_question(prompt: str, code: str) -> str:
    #remarks_block = format_remarks(remarks)
    #context = context[-4000:] if len(context) > 4000 else context
    # You are verifying strict structural consistency between a specification comment and its implementation.
    return f"""
     
{prompt}

{code}

""".strip()

def format_remarks(remarks: list[str]) -> str:
    return "\n".join(f"- {r}" for r in remarks)

def extract_json_from_answer(answer: str):
    # Remove markdown fences if present
    cleaned = answer.strip()

    # Remove ```json or ``` wrappers
    cleaned = re.sub(r"^```json\s*", "", cleaned)
    cleaned = re.sub(r"^```", "", cleaned)
    cleaned = re.sub(r"\s*```$", "", cleaned)

    # Try direct parsing first
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError:
        pass

    # If still failing, try extracting JSON object manually
    json_match = re.search(r'\{.*\}', cleaned, re.DOTALL)
    if json_match:
        try:
            return json.loads(json_match.group())
        except json.JSONDecodeError:
            pass

    # Fallback
    return {"match": False, "reason": "Failed to parse JSON response"}


# -----------------------------
# Load secrets from .env
# -----------------------------
load_dotenv()
API_KEY = os.getenv("API_KEY")

# -----------------------------
# Load model config
# -----------------------------
with open("config.json", "r") as f:
    model_configs = json.load(f)


prompt_file = "prompts.json"

# -----------------------------
# Load prompts
# -----------------------------
with open(prompt_file, "r") as f:
    prompt_data = json.load(f)


systemPrompt = prompt_data["system"]
prompts = prompt_data["prompts"]



parser = argparse.ArgumentParser()
parser.add_argument(
    "--files",
    nargs="*",
    help="List of files to process (override default)"
)

parser.add_argument(
    "--start",
    nargs=1,
    help="Start at question X"
)

parser.add_argument(
    "--end",
    nargs=1,
    help="End at question X"
)

args = parser.parse_args()

files = [
    "../../../mechanization/spec/API.v",
    "../../../mechanization/spec/Frontend.v",
    "../../../mechanization/spec/Node.v",
    "../../../mechanization/spec/Notation.v",
    "../../../mechanization/spec/Patterns.v",
    "../../../mechanization/spec/RegExpRecord.v",
    "../../../mechanization/spec/StaticSemantics.v",
    "../../../mechanization/spec/Semantics.v",
]

files = args.files if args.files else files

for file in files:
    defs_file = extract_defs(file)
    defs = defs + defs_file if 'defs' in locals() else defs_file


start = 0
end = len(defs)
if args.start:
    start = int(args.start[0])
if args.end:
    end = int(args.end[0])

defs = defs[start:end]


# =============================
# LOOP OVER MODELS
# =============================
for model_config in model_configs:
    results = []
    MODEL_NAME = model_config["model"]
    BASE_URL = model_config["base_url"]
    GEN_CONFIG = model_config["generation"]

    # -----------------------------
    # Initialize client
    # -----------------------------
    client = OpenAI(
        base_url=BASE_URL,
        api_key=API_KEY
    )

    tp = fp = tn = fn = 0
    for prompt in prompts:
        i = 0
        for definition in defs:
            i = i+1
            print(
                f"[MODEL: {MODEL_NAME}] question : {i} / {len(defs)}"
            )
            question = format_question(prompt, definition)

            try:
                response = client.chat.completions.create(
                    model=MODEL_NAME,
                    messages=[
                        {"role": "system", "content": systemPrompt},
                        {"role": "user", "content": question}
                    ],
                    **GEN_CONFIG  # unpack generation parameters
                )

                answer = response.choices[0].message.content              

                results.append({
                    "question": question,
                    "answer": answer,
                })

            except Exception as e:
                print(f"Error on question: {question}")
                results.append({
                    "question": question,
                    "answer": None,
                    "error": str(e)
                })



    # -----------------------------
    # Create timestamped filename
    # -----------------------------
    now = datetime.datetime.now()

    timestamp = now.strftime("%Y-%m-%d_%H-%M-%S")
    date_folder = now.strftime("%Y-%m-%d")

    filename = f"results_{timestamp}.json"


    output = {
        "timestamp": timestamp,
        "model": MODEL_NAME,
        "generation_config": GEN_CONFIG,
        "prompt_file": prompt_file,
        "results": results
    }


    # Create full directory path: result_folder/date/model
    fullDir = os.path.join(result_folder, date_folder, MODEL_NAME)

    # Create directory if it doesn't exist
    os.makedirs(fullDir, exist_ok=True)

    fullPath = os.path.join(fullDir, filename)

    with open(fullPath, "w") as f:
        json.dump(output, f, indent=2)

    print(f"Done. Results saved to {fullPath}")

    
    # Start HTML content
    html_content = """
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <title>Coq Mechanization Review</title>
        <style>
            body { font-family: Arial, sans-serif; margin: 20px; }
            h2 { color: #2c3e50; }
            pre { background-color: #f4f4f4; padding: 10px; border-radius: 5px; overflow-x: auto; }
            .question { margin-bottom: 30px; }
            .answer { margin-top: 10px; background-color: #e8f5e9; padding: 10px; border-radius: 5px; }
        </style>
    </head>
    <body>
    <h1>Coq Mechanization Review Results</h1>
    """

    # Loop through the results
    for i, item in enumerate(output.get("results", []), start=1):
        question_html = html.escape(item.get("question", ""))
        answer_html = html.escape(str(item.get("answer") or ""))
        html_content += f"""
        <div class="question">
            <h2>Sample {i}</h2>
            <h3>Code / Comments:</h3>
            <pre>{question_html}</pre>
            <h3>Review / Answer:</h3>
            <div class="answer"><pre>{answer_html}</pre></div>
        </div>
        """

    # Close HTML tags
    html_content += """
    </body>
    </html>
    """

    filename = f"results_{timestamp}.html"
    fullPath = os.path.join(fullDir, filename)

    # Write to file
    with open(fullPath, "w", encoding="utf-8") as f:
        f.write(html_content)

    print("HTML file 'review.html' created successfully.")

