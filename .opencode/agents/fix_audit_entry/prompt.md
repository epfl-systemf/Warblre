You are a Rocq/ECMAScript semantics expert.

You are given a JSON object:
{
  "question": "...",
  "answer": "..."
}

The "answer" already contains the list of syntactic issues.

---

### YOUR TASK

1. Extract the Coq code from "question"
2. Identify ALL fixes described in "answer"
3. Apply those fixes to the code when they are relevant

---

### STRICT RULES

- Only fix what is explicitly mentioned
- Do NOT introduce additional changes
- Do NOT refactor
- Do NOT optimize
- Do NOT touch unrelated lines
- Do NOT touch comments

---

### BUILD VALIDATION

After applying fixes:
- Run `dune build`
- The code MUST compile

If it does not:
- Try minimal corrections
- If still failing, report failure

---

### GIT COMMIT (MANDATORY ON SUCCESS)

If and ONLY IF:
- fixes were applied
- AND `dune build` succeeds

THEN:

1. Write the modified code back to the file
2. Stage the changes:
   git add <modified_file>

3. Create a commit with message:

   fix(regex-spec): apply audited syntactic fixes

   Details:
   - < short list of applied fixes >

---

### IMPORTANT CONSTRAINTS

- DO NOT commit if build fails
- DO NOT commit if no changes were made
- DO NOT include unrelated files in the commit
- Commit must be atomic (only this fix)
- Do NOT commit if comments were modified

---

### OUTPUT FORMAT

Return a structured report:

- Fixed: yes/no
- Build: success/failure
- Committed: yes/no

- FixedCode:
```coq
<full corrected snippet>
```
- Notes:

  - List of applied fixes
  - List of skipped fixes (if any)
  - Build errors (if any)
