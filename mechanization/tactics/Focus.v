From Warblre Require Import Result.

Inductive focus :=
| Here
| AppL (f: focus)
| AppR (f: focus)
| ArrowL (f: focus)
| ArrowR (f: focus)
| IteCond (f: focus)
| LetBound (f: focus)
| FunR (f: focus).

Fixpoint focus_insert (f inserted: focus) := match f with
| Here => inserted
| AppL f' => AppL (focus_insert f' inserted)
| AppR f' => AppR (focus_insert f' inserted)
| ArrowL f' => ArrowL (focus_insert f' inserted)
| ArrowR f' => ArrowR (focus_insert f' inserted)
| IteCond f' => IteCond (focus_insert f' inserted)
| LetBound f' => LetBound (focus_insert f' inserted)
| FunR f' => FunR (focus_insert f' inserted)
end.


(* Ltac red_tl_beta t := (eval simpl ((fun _ => _) _) at 1 in t).
Ltac red_tl_ite t := (eval simpl (if _ then _ else _) at 1 in t). *)



Ltac assert_type t T := lazymatch type of t with
| T => idtac
| ?T' => fail 99 "Epected type" T "got" T'
end.

Ltac focus_excise f t :=
  let _ := assert_type f focus in
  let rec iter f t := lazymatch f with
  | Here => lazymatch t with ?g => g end
  | AppL ?f' => lazymatch t with ?t' _ => iter f' t' end
  | AppR ?f' => lazymatch t with _ ?t' => iter f' t' end
  | ArrowL ?f' => lazymatch t with ?t' -> _ => iter f' t' end
  | ArrowR ?f' => lazymatch t with _ -> ?t' => iter f' t' end
  | IteCond ?f' => lazymatch t with if ?t' then _ else _ => iter f' t' end
  | LetBound ?f' => lazymatch t with let _ := ?t' in _ => iter f' t' end
  | FunR ?f' => lazymatch t with fun x => ?t' => iter f' t' end
  | _ => fail 100 "Unknown focus" f
  end in
  iter f t.

Ltac focus_replace f t r :=
  let _ := assert_type f focus in
  let rec iter f t r := lazymatch f with
  | Here => let t' := r t in t'
  | AppL ?f' => lazymatch t with ?t' ?o => let t'' := iter f' t' r in constr:(t'' o) end
  | AppR ?f' => lazymatch t with ?o ?t' => let t'' := iter f' t' r in constr:(o t'') end
  | ArrowL ?f' => lazymatch t with ?t' -> ?o => let t'' := iter f' t' r in constr:(t'' -> o) end
  | ArrowR ?f' => lazymatch t with ?o -> ?t' => let t'' := iter f' t' r in constr:(o -> t'') end
  | IteCond ?f' => lazymatch t with if ?t' then ?thenn else ?elze => let t'' := iter f' t' r in constr:(if t'' then thenn else elze) end
  | LetBound ?f' => lazymatch t with let x := ?t' in ?o => 
    let t'' := iter f' t' r in
    let s := constr:(let x := t'' in o) in
    s
    end
  | FunR ?f' => lazymatch t with fun x => ?t' => 
    let t'' := iter f' t' r in
    let s := constr:(fun x => t'') in
    s
    end
  | _ => fail 100 "Unknown focus" f
  end in
  iter f t r.

Ltac focus_get_goal := lazymatch goal with [ |- ?g ] => g end.
Ltac focus_get_hypothesis H := match type of H with ?T => T end.
Ltac focus_get_focus := match goal with
| [ _ := [?f] : focus |- _ ] => f
end.
Ltac focus_clear_focus := match goal with
| [ focus := [?f] : focus |- _ ] => clear focus
| [ |- _ ] => idtac
end.

(*  Replace has the bad habit of applying some transformation (cbn? hnf?)
    to the replacement, so we apply the same transformation to the goal to ensure
    perfect matching. *)
Ltac focus_replace_goal With By :=
  cbn;
  let g := focus_get_goal in
  replace g with With;
  [ idtac | By ].
Ltac focus_replace_hypothesis H With By :=
  cbn in H;
  let g := focus_get_hypothesis H in
  replace g with With in H;
  [ idtac | By ].

Ltac destruct_or_rewrite t := lazymatch goal with
| [ H: t = ?v |- _ ] => rewrite -> H
| [ |- _ ] => let Eq := fresh "AutoDest_" in destruct t eqn:Eq
end.

Ltac auto_destruct t := lazymatch t with
| Result.bind ?c _ => 
    destruct_or_rewrite c;
    match goal with
    | [ _: c = ?v |- _ ] => simpl (Result.bind v _) in *
    end
| match ?c with | _ => _ end => destruct_or_rewrite c
| if ?c then _ else _ => destruct_or_rewrite c
| ?l _ => auto_destruct l
end; try discriminate.

Tactic Notation "focus" constr(f) "do" tactic(t) := (
  assert_type f focus;
  let g := focus_get_goal in
  let focused := focus_excise f g in
  t focused).
Tactic Notation "focus" constr(f) "print" := (
  let t := (fun t => idtac t) in
  focus f do t).
Tactic Notation "focus" constr(f) "replace" "using" tactic(t) "by" tactic(s) := (
  assert_type f focus;
  let g := focus_get_goal in
  let replacement := focus_replace f g t in
  focus_replace_goal replacement ltac:(solve [ s ])).
Tactic Notation "focus" constr(f) "replace" "using" tactic(t) := (
  assert_type f focus;
  let g := focus_get_goal in
  let replacement := focus_replace f g t in
  focus_replace_goal replacement ltac:(try reflexivity)).
Tactic Notation "focus" constr(f) "replace" "with" constr(r) := (
  let r' := (fun _ => r) in
  focus f replace using r').
Tactic Notation "focus" constr(f) "replace" "with" constr(r) "by" tactic(s) := (
  let r' := (fun _ => r) in
  focus f replace using r' by s).
Tactic Notation "focus" constr(f) "auto" "destruct" := (
  assert_type f focus;
  repeat(
    let g := focus_get_goal in
    let t := focus_excise f g in
    auto_destruct t)).

Tactic Notation "focus" constr(f) "do" tactic(t) "in" hyp(H) := (
  assert_type f focus;
  let g := focus_get_hypothesis H in
  let focused := focus_excise f g in
  t focused).
Tactic Notation "focus" constr(f) "print" "in" hyp(H) := (
  let t := (fun t => idtac t) in
  focus f do t in H).
Tactic Notation "focus" constr(f) "replace" "using" tactic(t) "by" tactic(s) "in" hyp(H) := (
  assert_type f focus;
  let g := focus_get_hypothesis H in
  let replacement := focus_replace f g t in
  focus_replace_hypothesis H replacement ltac:(solve [ s ])).
Tactic Notation "focus" constr(f) "replace" "using" tactic(t) "in" hyp(H) := (
  assert_type f focus;
  let g := focus_get_hypothesis H in
  let replacement := focus_replace f g t in
  focus_replace_hypothesis H replacement ltac:(try reflexivity)).
Tactic Notation "focus" constr(f) "replace" "with" constr(r) "in" hyp(H) := (
  let r' := (fun _ => r) in
  focus f replace using r' in H).
Tactic Notation "focus" constr(f) "remember" "as" simple_intropattern(I) "in" hyp(H) := (
  let r := (fun t => remember t as I) in
  focus f do r in H).
Tactic Notation "focus" constr(f) "replace" "with" constr(r) "by" tactic(s) "in" hyp(H) := (
  let r' := (fun _ => r) in
  focus f replace using r' by s in H).
Tactic Notation "focus" constr(f) "auto" "destruct" "in" hyp(H) := (
  assert_type f focus;
  repeat(
    let g := focus_get_hypothesis H in
    let t := focus_excise f g in
    auto_destruct t)).

Tactic Notation "focused" "set" constr(f) := (
  assert_type f focus;
  focus_clear_focus;
  set (focus := f)).


Tactic Notation "focused" "do" tactic(t) := (
  let f := focus_get_focus in
  focus f do t).
Tactic Notation "focused" "print" := (
  let f := focus_get_focus in
  focus f print).
Tactic Notation "focused" "replace" "using" tactic(t) "by" tactic(s) := (
  let f := focus_get_focus in
  focus f replace using t by s).
Tactic Notation "focused" "replace" "using" tactic(t) := (
  let f := focus_get_focus in
  focus f replace using t).
Tactic Notation "focused" "replace" "with" constr(r) := (
  let f := focus_get_focus in
  focus f replace with r).
Tactic Notation "focus" constr(f) "remember" "as" simple_intropattern(I) := (
  let r := (fun t => remember t as I) in
  focus f do r).
Tactic Notation "focused" "replace" "with" constr(r) "by" tactic(s) := (
  let f := focus_get_focus in
  focus f replace with r by s).


Declare Custom Entry focus.
Notation "'§' e '§'" := e (e custom focus at level 99).
Notation "'[]'" := Here (in custom focus at level 0).
Notation "'(' f ')'" := f (in custom focus at level 0, f at level 99).
Notation "'if' f 'then' '_' 'else' '_'" := (IteCond f) (in custom focus at level 99).
Notation "f '_'" := (AppL f) (in custom focus at level 50, left associativity).
Notation "'_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity).
Notation "f -> '_'" := (ArrowL f) (in custom focus at level 70, right associativity).
Notation "'_' -> f" := (ArrowR f) (in custom focus at level 70, right associativity).
Notation "'_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity).
Notation "'_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'_' '_' '_' '_' '_' '_' '_' '_' '_' '_' f" := (AppR f) (in custom focus at level 50, f at level 49, left associativity, only parsing).
Notation "'fun' '_' '=>' f" := (FunR f) (in custom focus at level 99, right associativity).
Notation "'fun' '_' '_' '=>' f" := (FunR (FunR f)) (in custom focus at level 99, right associativity).
Notation "'fun' '_' '_' '_' '=>' f" := (FunR (FunR (FunR f))) (in custom focus at level 99, right associativity).
Notation "'fun' '_' '_' '_' '_' '=>' f" := (FunR (FunR (FunR (FunR f)))) (in custom focus at level 99, right associativity).
Notation "'fun' '_' '_' '_' '_' '_' '=>' f" := (FunR (FunR (FunR (FunR (FunR f))))) (in custom focus at level 99, right associativity).
Notation "'fun' '_' '_' '_' '_' '_' '_' '=>' f" := (FunR (FunR (FunR (FunR (FunR (FunR f)))))) (in custom focus at level 99, right associativity).