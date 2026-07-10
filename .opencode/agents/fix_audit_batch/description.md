
This agent orchestrates the fixing of multiple audited Coq snippets.

Input:
- A JSON array of entries:
  [
    { "question": "...", "answer": "..." },
    ...
  ]

Responsibilities:
1. Iterate over all entries
2. For each entry:
   - Call the `fix_audit_entry` agent
3. Collect results
4. Aggregate a final report

Output:
- A global report including:
  - Total number of samples
  - Number of fixed samples
  - Number of failed builds
  - List of problematic samples
  - Per-sample reports

Constraints:
- Must not modify entries directly
- Must rely on `fix_audit_entry` for all fixes
- Must continue processing even if one sample fails