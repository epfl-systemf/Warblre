# OpenCode Agentic Pipeline Configuration

> Complete setup guide for the Warblre autoformalization pipeline, including LLM provider, MCP server, and audit tool configuration.

---

## 1. Installation

Install the OpenCode CLI using the official installer:

```bash
curl -fsSL https://opencode.ai/install | bash
```

After installation, **restart your terminal** and verify that `opencode` is available.

link : <a href="https://opencode.ai/"> `opencode` </a>

---

## 2. Provider Setup

### 2.1 Create Configuration File

Save the provider configuration to `~/.config/opencode/opencode.json`

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
        "moonshotai/Kimi-K2.5": {
          "name": "moonshotai/Kimi-K2.5",
          "max_tokens": 1000
        },
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

### 2.2 Select a Model

Models are available via `Ctrl + P` → **Change Model** inside OpenCode.

---

## 3. Authentication

Store your EPFL RCP API key in `~/.local/share/opencode/auth.json`:

```bash
mkdir -p ~/.local/share/opencode
cat > ~/.local/share/opencode/auth.json << 'EOF'
{
  "myprovider": {
    "type": "api",
    "key": "<Your key here>"
  }
}
EOF
```

> Replace `<Your key here>` with your actual API key before running any agents.

---

## 4. MCP Server Configuration

The pipeline relies on **rocq-mcp** for interactive proof checking, compilation, and code navigation. This server must be running before you execute the agent that fix the proofs.

### 4.1 Prerequisites

- **Rocq / Coq** — `coqc` must be on your `PATH` (version 9.0.0 or 9.1.0)
- **Python 3.11+**
- **rocq-mcp** — to be download from <a href="https://github.com/LLM4Rocq/rocq-mcp"> rocq-mcp </a> installed in a virtual environment (e.g., `~/rocq-mcp`), follow the instructions there

### 4.2 Create MCP Configuration

Modify the paths on `.opencode/opencode.json` (inside this project) ***I have put this /Users/valentinschneeberger because ~ was not working!!***

### 4.3 Verify the Server

1. In OpenCode, check that rocq-mcp tools are available. A quick test is:
   ```
   @fix_proofs verify that you can access the mcp server
   ```

### 4.4 rocq-mcp Tools Reference

| Tool | Purpose |
|------|---------|
| `rocq_compile_file` | Batch-compile a `.v` file |
| `rocq_check` | Fast iterative proof checking with cached imports |
| `rocq_step_multi` | Try multiple tactics at once (does not advance state) |
| `rocq_start` | Start an interactive proof session |
| `rocq_query` | Search lemmas, check types, inspect definitions |
| `rocq_toc` | Get the structure of a `.v` file |
| `rocq_assumptions` | Check axioms a theorem depends on |
| `rocq_verify` | Verify a proof proves the original statement |

---

## 5. Audit Tool Configuration

The audit tool checks consistency between specification comments and Rocq implementations. It lives in `utils/autoformalization/audit/`.

### 5.1 Install Dependencies

```bash
cd utils/autoformalization/audit
conda env create -f environment.yml
conda activate coq-audit
```

### 5.2 Configure the Model

Edit `utils/autoformalization/audit/config.json`:

```json
[
  {
    "model": "moonshotai/Kimi-K2.6",
    "base_url": "https://inference.rcp.epfl.ch/v1",
    "generation": {
      "temperature": 0,
      "top_p": 1,
      "max_tokens": 20000,
      "presence_penalty": 0.0,
      "frequency_penalty": 0.0
    }
  }
]
```

> Multiple models can be listed; they will be evaluated sequentially.

### 5.3 Set the API Key

Create `utils/autoformalization/audit/.env`:

```env
API_KEY=your_api_key_here
```

### 5.4 Customize Prompts (Optional)

Edit `utils/autoformalization/audit/prompts.json` to adjust the audit prompts:

```json
{
  "system": "You are verifying consistency between specification comments and implementation.",
  "prompts": [
    "Check whether the implementation follows the steps described in the comments."
  ]
}
```

### 5.5 Run the Audit

Execute the audit from the `utils/autoformalization/audit/` directory:

```bash
python comment_code_audit.py
```

Limit the definition range if needed:

```bash
python comment_code_audit.py --start 10 --end 50
```

**Output location:**

```
results/
  YYYY-MM-DD/
    MODEL_NAME/
      results_TIMESTAMP.json
      results_TIMESTAMP.html
```

---

## 6. Autoformalization Pipeline

Execute the following steps in order. Each step feeds the next.

```
annotate_rocq  ──►  implement_from_comments  ──►  audit  ──►  fix_audit_batch  ──►  fix_proofs
```

### 6.1 Prepare Proposal

Before starting, download the proposal and the ECMA diff into:

```
proposals/<your-proposal-name>/
```

> See existing proposal folders for the expected structure.

---

### 6.2 Step 1 — Generate Specification Comments

Insert ECMA specification comments into the Rocq mechanization.

```
@annotate_rocq implement the comments for the following proposal : proposals/<your proposal>
```

**Output:** Annotated `.v` files with `(*>> ... <<*)` spec comments.

---

### 6.3 Step 2 — Implement Code from Comments

Generate Rocq definitions and algorithms from the spec comments inserted in Step 1.

```
@implement_from_comments add the code for the following proposal : proposals/<your proposal>
```

**Output:** Implemented definitions, fixpoints, and (possibly admitted) proofs.

---

### 6.4 Step 3 — Audit

Run the audit tool on the files that changed in `mechanization/spec/`.

```bash
cd utils/autoformalization/audit
python comment_code_audit.py
```

**Output:** Raw audit results (`results/YYYY-MM-DD/MODEL/`).

---

### 6.5 Step 4 — Filter Audit Results

Keep only actionable mismatches (syntax errors, missing steps, etc.).

```
@filter_audit filter the audit just generated
```

**Output:** Filtered JSON of concrete issues.

---

### 6.6 Step 5 — Apply Fixes

Automatically repair the issues identified in Step 4.

```
@fix_audit_batch use the latest filter result created and the other subagent on your prompt to solve all of those problems
```

**Output:** Corrected `.v` files.

---

### 6.7 Step 6 — Fix Admitted Proofs

Ensure `rocq-mcp` is running, then synthesize proofs for all remaining `Admitted.` obligations.

```
@fix_proofs fix the admitted proofs
```

**Output:** Complete, compiled proofs.

---

## 7. Quick Reference

| Step | Agent / Tool | Input | Output |
|------|-------------|-------|--------|
| 1 | `annotate_rocq` | `proposals/<name>/` | Spec comments in `.v` files |
| 2 | `implement_from_comments` | Annotated `.v` files | Implemented definitions |
| 3 | `comment_code_audit.py` | Changed spec files | Audit JSON / HTML |
| 4 | `filter_audit` | Raw audit results | Filtered issues |
| 5 | `fix_audit_batch` | Filtered issues | Fixed `.v` files |
| 6 | `fix_proofs` | Admitted proofs | Completed proofs |

---

## 8. Agent Reference & Extending the Pipeline

### 8.1 What Each Agent Does

The pipeline is driven by specialized agents stored in `.opencode/agents/`. Below is a quick summary of every agent and its role.

| Agent | What it does |
|-------|-------------|
| `annotate_rocq` | Reads an ECMA proposal diff and inserts specification comments (`(*>> … <<*)`) into Rocq `.v` files. **Comments only — never writes code.** |
| `implement_from_comments` | Implements the Rocq definitions,Fixpoints and algorithms that correspond to the spec comments added by `annotate_rocq`. |
| `implement_proposal` | End-to-end implementation of a proposal (syntax + semantics + tests) in one shot. |
| `run_local_audit` | Runs the audit tool **only on uncommitted changes**, restricting analysis to modified definitions for fast feedback. |
| `filter_audit` | Cleans raw audit results, keeping only entries that report concrete syntactic mismatches or missing steps. |
| `fix_audit_entry` | Fixes a **single** audited Coq snippet based on the reported issues and commits if the build passes. |
| `fix_audit_batch` | Orchestrates `fix_audit_entry` over many snippets **sequentially** (one at a time). |
| `fix_proofs` | Scans the entire mechanization for `Proof. Admitted.`, synthesizes missing proof scripts using `rocq-mcp` and existing patterns, and verifies with `dune build`. |
| `test262_converter` | Converts a **whole** Test262 branch into a fresh OCaml expect-test file (`tests/tests/Test262_<Feature>.ml`). |
| `fix_test262_batch` | Orchestrates conversion of all JS test files in a branch by calling `fix_test262_file` sequentially. |
| `fix_test262_file` | Generates complete OCaml expect-tests for a **single** JavaScript test file from Test262. |

### 8.2 How to Add a New Agent

To extend the pipeline with a new agent:

1. **Create the agent directory**
   ```bash
   mkdir -p .opencode/agents/<agent-name>
   ```

2. **Add the files**

   - **`description.md`** — Short summary (1 paragraph) of what the agent does, its inputs/outputs, and constraints. OpenCode uses this to decide when to invoke the agent.
   - **`prompt.md`** — Detailed system prompt that the LLM will follow when the agent is called. Include task description, constraints, step-by-step workflow, output format, and error-handling rules.

3. **Invoke it**
   Once the folder exists, the agent is automatically available in OpenCode via:
   ```
   @<agent-name> <your prompt>
   ```

> **Tip:** Follow the style of existing agents. Keep prompts concrete, give examples where possible, and always state whether the agent is allowed to modify code, run builds, or commit changes.

---

## 9. Verification Checklist

After completing the pipeline, ensure the following before committing:

- [ ] `dune build @all` succeeds without errors
- [ ] `dune test` passes
- [ ] `rocqchk` validates the compiled libraries
- [ ] No `Admitted.` proofs remain
- [ ] Code follows the repository naming conventions
- [ ] Spec comments reference the correct ECMAScript sections
