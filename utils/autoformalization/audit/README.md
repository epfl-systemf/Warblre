# Coq Spec–Implementation Audit Tool

This project provides a tool to automatically audit **Coq (.v) mechanization code** against its **specification comments** using Large Language Models (LLMs).

The tool extracts definitions from Coq files and asks an LLM to verify whether the **implementation is consistent with the specification comments** that accompany it.

Results are saved as **JSON logs** and **HTML reports** for easy inspection.

---

## Overview

The workflow is:

1. Extract Coq definitions (`Definition`, `Fixpoint`, etc.) from `.v` files.
2. Send each definition (including comments/spec steps) to an LLM.
3. Ask the model to review whether the **code matches the specification comments**.
4. Store results in structured JSON.
5. Generate an HTML report for visual review.

This tool is intended for **auditing** and **spec–code consistency analysis**.

---

## Features

- Extracts definitions from `.v` files automatically
- Supports multiple LLM providers via configurable API endpoints
- Customizable prompts
- Batch evaluation across multiple models
- Generates JSON result logs
- Generates HTML review reports
- Supports partial evaluation (`--start`, `--end`)

---

## Installation

Clone the repository:

```bash
git clone https://github.com/LindenRegex/Warblre
cd Warblre/utils/autoformalization/audit
```

Install dependencies:

```bash
# Create the conda environment and install dependencies
conda env create -f environment.yml

# Activate the environment
conda activate coq-audit
```

---

## Configuration

### API Key

Create a `.env` file in the project root:

```env
API_KEY=your_api_key_here
```

### Model Configuration

Models are defined in `config.json`.

Example:

```json
[
  {
    "model": "gpt-4.1",
    "base_url": "https://api.openai.com/v1",
    "generation": {
      "temperature": 0,
      "max_tokens": 2000
    }
  }
]
```

Multiple models can be listed in the configuration file and will be evaluated sequentially.

### Prompts

Prompts are defined in `prompts.json`.

Example structure:

```json
{
  "system": "You are verifying consistency between specification comments and implementation.",
  "prompts": [
    "Check whether the implementation follows the steps described in the comments."
  ]
}
```

---

## Usage

Run the script:

```bash
python comment_code_audit.py
```

To restrict the range of definitions analyzed:

```bash
python comment_code_audit.py --start 10 --end 50
```

This will only evaluate definitions in the specified range.

---

## Input

The tool extracts definitions from a Coq file.

Currently the script processes:

```
mechanization/spec/Semantics.v
```

Supported constructs include:

- `Definition`
- `Fixpoint`

The extraction logic collects the comments and code associated with each definition so that the LLM can evaluate the consistency between them.

---

## Output

Results are written to the `results/` directory.

Directory structure:

```
results/
  YYYY-MM-DD/
    MODEL_NAME/
      results_TIMESTAMP.json
      results_TIMESTAMP.html
```

Example:

```
results/
  2026-03-16/
    gpt-4.1/
      results_2026-03-16_14-23-11.json
      results_2026-03-16_14-23-11.html
```

### JSON Output Format

Example result structure:

```json
{
  "timestamp": "2026-03-16_14-23-11",
  "model": "gpt-4.1",
  "generation_config": {
    "temperature": 0,
    "max_tokens": 2000
  },
  "results": [
    {
      "question": "...definition and comments...",
      "answer": "...model review..."
    }
  ]
}
```

---

## HTML Report

The HTML report provides a visual interface showing:

- The extracted Coq definition and comments
- The model’s analysis of the implementation
- The full prompt sent to the model

This allows quick manual inspection of potential inconsistencies between the specification and the implementation.

---