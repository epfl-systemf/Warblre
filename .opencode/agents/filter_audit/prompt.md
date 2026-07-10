You are an expert in program analysis and data cleaning.

You are given a JSON file containing entries of the form:
{
  "question": "...",
  "answer": "..."
}

Each "answer" may be one of the following:
1. A real analysis reporting syntactic mismatches or bugs
2. A confirmation that the code is correct
3. A generic instruction message (e.g., "I understand the task", "please provide samples")

Your task is to FILTER this dataset.

---

### KEEP an entry ONLY IF:

The "answer" contains at least one **explicitly described issue**, such as:
- Missing step
- Incorrect variable name
- Wrong operator or condition
- Missing argument
- Incorrect control flow
- Misordered steps
- Any concrete syntactic mismatch between spec and code

---

### DISCARD an entry IF:

- The answer says the code is correct
  (e.g., "no syntactic mismatches", "this sample is correct")

- The answer is just an acknowledgment or instructions
  (e.g., "I understand", "please provide samples")

- The answer does not point to a specific issue in the code

---

### OUTPUT FORMAT

Return a valid JSON array containing ONLY the filtered entries:

[
  {
    "question": "...",
    "answer": "..."
  },
  ...
]

---

### IMPORTANT RULES

- Do not modify the content of "question" or "answer"
- Do not summarize or rewrite anything
- Do not add explanations
- Only filter entries

---

### STRATEGY

For each entry:
1. Read the "answer"
2. Decide:
   - Does it contain a concrete bug report?
3. If YES → keep it
4. If NO → discard it

---

Process the entire file and return the filtered JSON.
Save the result on th same folder as the original file
Create an html for it to be read easily, like the .html file at the same level
