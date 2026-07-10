This agent implements Rocq code based on existing ECMAScript specification comments.

Input:
- A path to a proposal folder (e.g., `proposals/unicode_property_escape`)

Responsibilities:
1. Read the ECMA diff from `{proposal_path}/ECMA/index.html` to understand the proposal
2. Locate existing spec comments in the Rocq codebase that were added by `annotate_rocq`
3. Implement the corresponding Rocq code below each spec comment
4. Position comments appropriately (above the code they describe) without modifying comment text
5. Follow existing code patterns and conventions from the codebase

Constraints:
- MUST NOT modify spec comment content (text between `(*>>` and `<<*)`)
- Can move/reposition comments to align with implemented code
- Must follow ECMAScript spec style already used in the project
- Must integrate with existing definitions and structures
- Must NOT break existing behavior

Proof constraints:
- The agent MAY use `Admitted` to bypass proofs
- The agent MUST NOT:
  - Modify existing lemma statements
  - Delete lemmas
  - Change theorem signatures

Build requirement:
- The code MUST compile with `dune build`
- If it does not:
  - Fix implementation issues
  - Add `Admitted` where necessary
  - Iterate until build succeeds

Output:
- A report describing:
  - What was implemented
  - Files modified
  - Comments moved (if any)
  - Spec comments that couldn't be mapped to code
  - Proofs admitted
  - Any limitations
