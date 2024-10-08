Require Import Ltac2.Ltac2.
From Ltac2 Require Import Control Pattern List.

(*  LATER:
    once updated to a newer version (8.20?) supporting https://github.com/coq/coq/pull/18690,
    remove and use builtin.
*)
Ltac2 numgoals (_: unit): int :=
  1.

(** A tactic to retrieve an hypothesis by the shape of its type. *)
Ltac2 retrieve (pat: pattern) (into: ident): unit :=
  let hyp_patterns := (None, (Pattern.MatchPattern, pat)) :: [] in
  let goal_pattern := (Pattern.MatchPattern, pat:(_)) in
  (* LATER: change to lazy match, if possible *)
  let (a, _, _, _, _) := Pattern.matches_goal false hyp_patterns goal_pattern in
  if Bool.neg (Int.equal (numgoals ()) 1) then Control.throw_invalid_argument "Multiple hypothese match the pattern" else ();
  let h := Array.get a 0 in
  Std.rename ((h, into) :: []).
Ltac2 Notation "retrieve" pat(pattern) "as" into(ident) := retrieve pat into.