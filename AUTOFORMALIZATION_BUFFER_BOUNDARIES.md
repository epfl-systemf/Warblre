# Case Study: Autoformalizing the RegExp Buffer Boundaries Proposal in Warblre

This document is a complete walkthrough of how the proposal-regexp-buffer-boundaries feature (\A and \z assertions) was added to the Warblre mechanization using an LLM-based agentic pipeline. It describes every step, every agent invocation, the exact changes produced, and the manual decisions taken along the way.

---

## 1. Background: What Is an Agent?

An agent in this context is a specialized system prompt exposed to the OpenCode CLI through the @agent-name syntax. Each agent is defined by two files stored in the repository under .opencode/agents/\<agent-name>/

- description.md: A short summary that OpenCode uses to decide when to invoke the agent.
- prompt.md: The full system prompt the LLM follows when the agent is triggered.
  

When the user types
```bash
@annotate_rocq proposals/buffer_boundaries
```
OpenCode:
1. Loads <a href="https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/.opencode/agents/annotate_rocq/description.md"> description.md </a> to confirm the agent is appropriate. 
2. Loads <a href="https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/.opencode/agents/annotate_rocq/prompt.md"> prompt.md </a> and passes the user's arguments as input.
3. The LLM executes the task autonomously using the available tools (bash, grep, read, edit, rocq-mcp, etc.).

All agents used below are described on the <a href="https://github.com/LindenRegex/Warblre/tree/vs/autoformalization/agent-config">vs/autoformalization/agent-config</a> branch
and referenced in the pipeline documentation at: <a href="https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/agent-config/utils/autoformalization/README.md"> Readme </a>

---

## 2. Prerequisites

Before running the pipeline, the following were installed and configured:

- OpenCode CLI: Installed via
  ```bash
  curl -fsSL https://opencode.ai/install | bash
  ```
- EPFL RCP Provider: Configured in ~/.config/opencode/opencode.json with endpoints for moonshotai/Kimi-K2.5 and moonshotai/Kimi-K2.6
  ```bash
  mkdir -p ~/.config/opencode
  cat > ~/.config/opencode/opencode.json << 'EOF'
  {
    "$schema": "https://opencode.ai/config.json",
    "provider": {
      "myprovider": {
        "npm": "@ai-sdk/openai-compatible",
        "name": "EPFL RCP",
        "options": {
          "baseURL": "https://inference.rcp.epfl.ch/v1"
        },
        "models": {
          "moonshotai/Kimi-K2.6": {
            "name": "moonshotai/Kimi-K2.6",
            "max_tokens": 1000
          }
        }
      }
    }
  }
  EOF
  ```
- rocq-mcp: Interactive Rocq MCP server that gives the agents access to the proof state.  It must be installed separately (e.g. in a conda environment) and registered in the workspace .opencode/opencode.json:
  ```json
  {
    "mcp": {
      "rocq-mcp": {
        "enabled": true,
        "type": "local",
        "command": [
          "/path/to/rocq-mcp"
        ],
        "environment": {
          "ROCQ_WORKSPACE": "/path/to/warblre",
          "ROCQPATH": "_build/default/mechanization",
          "ROCQ_COQC_BINARY": "/path/to/coqc",
          "ROCQ_PET_BINARY": "/path/to/pet",
          "ROCQ_PET_TIMEOUT": "30",
          "ROCQ_COQC_TIMEOUT": "60",
          "ROCQ_VERIFY_TIMEOUT": "120"
        }
      }
    }
  }
  ```
  The server exposes tools such as rocq_compile_file, rocq_check, rocq_step_multi, rocq_start, rocq_query, and rocq_verify, which the fix_proofs agent uses to navigate proof states and synthesize tactics.
- Build system: dune and opam dependencies for the OCaml / Rocq codebase:
  ```bash
  opam install . --deps-only
  ```

---

## 3. Proposal Preparation

The buffer-boundaries proposal introduces two new regex assertions: \A (start of string, regardless of multiline mode) and \z (end of string, regardless of multiline mode).

The following resources were downloaded into a local folder:

- Rendered proposal (for understanding context):
  <a href="https://tc39.es/proposal-regexp-buffer-boundaries/"> proposal </a>
  
- ECMA diff (the formal specification): <a href = "https://github.com/tc39/proposal-regexp-buffer-boundaries"> diff </a>
  

To get the proposal, both the rendered proposal page and the ECMA diff page were downloaded as static HTML.  We used a browser extension (<a href="https://chromewebstore.google.com/detail/web-page-downloader/aeojmgngnebhbjpncamiplkimkbnmpmk"> Web Page Downloader </a> for Chrome) that fetches the page and all needed assets into a single folder.  They are therefore not a raw git diff, but full HTML pages, downloaded from the browser.

These were placed in the repository under:
```
proposals/buffer_boundaries/
├── ecma/
└── proposal/
```

The ECMA diff is the primary source used by the agents; the rendered proposal serves only as optional background reading.

---

## 4. Step 1: Specification Comment Annotation (@annotate_rocq)

### 4.1 Agent Role

The annotate_rocq agent is a documentation specialist only. Its prompt strictly forbids it from writing or modifying any Rocq code. Its sole purpose is to:

1. Parse the ECMA HTML page (proposals/buffer_boundaries/ecma/index.html).
2. Extract every modified/added section (grammar productions, abstract operations, algorithm steps).
3. Insert specification comments in the exact format used in the codebase:
   - Section headers: (** >> Section Number Name <<*)
   - Algorithm steps: (*>> N. Step text <<*)
   - Grammar productions: (*>> production :: <<*) and (*>> element <<*)
4. Map each section to the correct .v file (Patterns.v for grammar, Semantics.v for runtime semantics, etc.).

If a section needs code that does not yet exist, the agent leaves a mechanization note:
```coq
(* + NEEDS: Description of what's needed +*)
```

### 4.2 Invocation

```
@annotate_rocq implement the comments for the following proposal: proposals/buffer_boundaries
```

### 4.3 What the Agent Did

The agent scanned the ECMA diff and identified changes to:
- Grammar productions: adding \A and \z as new Assertion alternatives.
- Runtime Semantics: CompileAssertion: two new algorithm blocks for compiling \A and \z.

It then inserted spec comments into:
- mechanization/spec/Patterns.v: grammar comments for the new assertions.
- mechanization/spec/Semantics.v: step-by-step algorithm comments for compiling \A and \z.

The agent reported a summary confirming that all sections from the proposal were annotated and didn't add any code there.

Result: The commit <a href="https://github.com/LindenRegex/Warblre/commit/f6e7713">f6e7713</a> "Agent added comments".

---

## 5. Step 2: Code Implementation from Comments (@implement_from_comments)

### 5.1 Agent Role

The implement_from_comments agent is the implementation specialist. Its prompt instructs it to:

1. Read the ECMA diff for context.
2. Locate spec comments added by annotate_rocq in the latest commit.
3. Implement the corresponding Rocq definitions, fixpoints, and algorithms directly below each spec comment.
4. Follow existing code patterns and conventions from the codebase.
5. Must not modify spec comment content (text between (*>> and <<*)).
6. May use Admitted. to bypass proofs if needed, but must not change existing lemma statements or theorem signatures.
7. Ensure dune build @all succeeds. If it does not, iterate and/or add Admitted. where necessary until compilation passes.

### 5.2 Invocation

```
@implement_from_comments add the code for the following proposal: proposals/buffer_boundaries
```

### 5.3 What the Agent Did

The agent found the spec comments from commit <a href="https://github.com/LindenRegex/Warblre/commit/f6e7713">f6e7713</a> and proceeded to implement:

#### 5.3.1 mechanization/spec/Patterns.v
Added two new constructors to the Regex inductive type:
```coq
(*>> [+UnicodeMode] \ A <<*)
| BufferStart
(*>> [+UnicodeMode] \ z <<*)
| BufferEnd
```

https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/mechanization/spec/Patterns.v

#### 5.3.2 mechanization/spec/Semantics.v
Added two new branches to the Assertion compilation logic, implementing \A and \z as matchers:
- BufferStart: Returns success only if endIndex = 0.
- BufferEnd: Returns success only if endIndex = inputLength.

https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/mechanization/spec/Semantics.v

#### 5.3.3 Ripple Effects Across the Codebase
Adding new constructors to Regex naturally broke pattern matches and proofs across the project. The agent updated the following files to handle the two new cases:

| File | What was updated |
|------|-----------------|
| mechanization/spec/StaticSemantics.v | countLeftCapturingParensWithin_impl, earlyErrors_rec |
| mechanization/props/NodeProps.v | Zipper walk, node inductive principle, indexing proofs |
| mechanization/props/StrictlyNullable.v | strictly_nullable fixpoint; compile cases for both assertions |
| engines/common/Printers.ml | OCaml pretty-printer for \A and \z |
| tests/fuzzer/Fuzzer.ml | Fuzzer pattern match update |

#### 5.3.4 Proofs Admitted
Two large proofs failed to rebuild after the new constructors were added:

1. EarlyErrors.Completeness.rec (≈ 40 lines): The automated tactic script could not adapt on its own.
2. Match.MatcherInvariant.matcher_invariant (≈ 120 lines): Core proof showing that compilation preserves matcher invariants. Again, The proof structure was too complex for the implementation agent to repair.

Both proofs were deleted and replaced with Proof. Admitted. to allow compilation to succeed.

Result: The commit <a href="https://github.com/LindenRegex/Warblre/commit/091285f946dbfdd516797a1ca814b20848868693">091285f</a> "Agent added code".


---

## 6. Step 3: Audit (diff_audit.py)

After the spec comments were in place and the code was implemented, the next step in the pipeline is to audit for consistency between the ECMA diff and the Rocq implementation.

The audit tool is a standalone Python script living in utils/autoformalization/audit/ called diff_audit.py. On the current workflow, it works as follows:

1. Runs git diff against HEAD~N (default N=1, configurable via --commits). Only files changed in the last commit(s) are considered.
2. Determines which .v files in mechanization/spec/ were modified by looking at the diff output.
3. Extracts Definition and Fixpoint blocks from those files, but only the ones whose line ranges overlap with the changed lines from the diff. Unaffected definitions are skipped entirely.
4. Sends each selected block (comments + code) to the LLM using the same prompt loaded from prompts.json (a few-shot example of a correct, human-verified sample).
5. Saves results as JSON and HTML under results/YYYY-MM-DD/<MODEL_NAME>/ with filenames prefixed diff_results_.

The prompt explicitly instructs the model to look for:
- Typos or missing steps in the translation
- Syntactic mismatches between comments and code

and not to report:
- Type errors, semantic subtleties, or compilation issues
- Missing conversions between nat, int, positive, etc.
- Fused recursive functions or extraneous functional-language copies

Because the script is diff-driven, it naturally focuses the audit on the definitions the implementation agent actually touched, making it fast and precise rather than re-auditing the entire specification.

### 6.1 Running the Audit

```bash
cd utils/autoformalization/audit
python diff_audit.py --commits 1
```

(If the implementation spans multiple commits, adjust --commits N accordingly.)

### 6.2 Result: Nothing Reported

The audit tool ran successfully and reported no issues.

Since no mismatches were found, the subsequent filtering and fixing agents (filter_audit, fix_audit_batch) were not needed in this case. This jump from audit to fix_proofs is a valid and common shortcut in the pipeline when the implementation agent already aligned code with comments correctly.

---

## 7. Step 4: Proof Repair (@fix_proofs)

### 7.1 Agent Role

The fix_proofs agent is a proof synthesis specialist. Its prompt instructs it to:

1. Discover all Proof. Admitted. instances in mechanization/**/*.v files.
2. For each admitted proof:
   - Read the lemma statement and surrounding context.
   - Use git to retrieve the original proof before it was admitted.
   - Extract the proof pattern (induction principle, tactics, helper lemmas).
   - Synthesize a new proof script using rocq-mcp tools (rocq_start, rocq_check, rocq_step_multi).
   - Verify with dune build @all.
3. Apply the fix only if compilation succeeds.

### 7.2 Invocation

```
@fix_proofs fix the admitted proofs
```

### 7.3 What the Agent Did

The fix_proofs agent discovered all Proof. Admitted. instances in the mechanization and synthesized proof scripts for each one, using rocq-mcp for interactive navigation and git to retrieve historical proof patterns.

- EarlyErrors.Completeness.rec: Rebuilt the structural induction proof, added trivial constructor. cases for BufferStart/BufferEnd, and fixed a residual issue in the named-backref case where lia needed an extra rewrite -> Zipper.Zip.id in *. to finish.
- Match.MatcherInvariant.matcher_invariant: Rebuilt the node-induction proof, added cases for BufferStart/BufferEnd, and fixed a residual issue where an extraneous zip call caused a type mismatch (GroupName vs RegexContext).

See the restored proofs:
- mechanization/props/EarlyErrors.v: https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/mechanization/props/EarlyErrors.v
- mechanization/props/Match.v: https://github.com/LindenRegex/Warblre/blob/vs/autoformalization/rewriting-agent-buffer-boundaries-fixed/mechanization/props/Match.v

Result: No remaining Admitted. proofs in mechanization/. dune build @all and dune test both pass.

---

## 8. What the Pipeline Achieved

This case study demonstrates the happy-path flow of the Warblre autoformalization pipeline:

1. Annotate → 2. Implement → 3. Audit (clean) → 4. Fix proofs → Done.

The pipeline is designed so that:
- Implementation and annotation are strictly separated agents (prevents hallucinated code replacing correct comments).
- The audit catches mismatches before proof repair, so proof fixes are not wasted on buggy code.
- Proof repair is the final step because Admitted. is the only remaining gate to a fully verified feature.

In this case, the audit reported nothing, so filtering and batch-fixing were skipped. For proposals with more complex semantics, the filter_audit and fix_audit_batch agents would be invoked after the audit to correct mismatches found by the LLM reviewer.

---

*End of case study.*
