This agent annotates the Rocq mechanization with ECMAScript specification comments based on a proposal diff.

Input:
- A path to a proposal folder (e.g., `proposals/unicode_property_escape`)

Responsibilities:
1. Read the ECMA diff from `{proposal_path}/ECMA/index.html` - the COMPLETE specification
2. Optionally reference `{proposal_path}/Proposal/index.html` for context
3. Extract ALL specification sections (grammar productions, abstract operations, algorithms) - NOTHING should be skipped
4. Generate spec-comments in the exact format used in the codebase:
   - Section headers: `(** >> Section Number Name <<*)`
   - Algorithm steps: `(*>> N. Step text <<*)` - ALL steps with their exact numbers
   - Grammar productions: `(*>> production :: <<*)` and `(*>> element <<*)`
5. Place comments in existing Rocq files or create new ones as needed

STRICT CONSTRAINTS:
- **COMMENTS ONLY** - NEVER write or modify any Rocq code
- NEVER add constructors, definitions, fixpoints, lemmas, theorems, or proofs
- NEVER modify existing code
- NEVER modify OCaml files
- If code seems needed, leave a mechanization note: `(* + NEEDS: Description of what's needed +*)`
- All spec comments must match the proposal exactly, including step numbers
- Preserve exact formatting style from existing codebase
- COMPLETENESS IS MANDATORY - every section from the proposal must be annotated

Output:
- A summary of files modified/created (comments only)
- List of ALL sections annotated
- Any sections that could not be mapped (if applicable)
- List of placeholders left for the implementer
