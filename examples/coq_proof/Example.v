From Coq Require Import ZArith List.
From Warblre Require Import Parameters.
From Warblre Require Import Patterns RegExpRecord.
From Warblre Require Import EarlyErrors.
From Warblre Require Import Result Semantics Compile.
From Warblre Require Import Errors Typeclasses.
Import Patterns Coercions.Coercions Notation.Notation.

(** * A simple example of representation-parametric matching **)

(** This file demonstrates how our specification can be used to reason about regular expressions.

    Specifically, we prove an extremely simple property: the fact that for any [a], the regexp [/(?:a+?)+?/] matches the string ["aaa"] (the paper describes more complex proofs, and the global README links to the corresponding Coq code). **)

Section AbstractMatching.
  (** We start by assuming a concrete (yet arbitrary) instantiation of the engine. **)
  Context `{engineParameters: Parameters}.

  (** We then define a regex and an input string.  The character [a] is left unspecified: we want to prove the matching property for any choice of [a]. **)
  Context {a: Character}.

  (** The regex for this example is /(?:a+?)+?/ **)
  Definition regex_of_interest :=
    Quantified
      (Quantified (Char a) (Lazy Plus))
      (Lazy Plus).

  (** To run, the specification requires a configuration object.
      Its contents are not relevant in this example, _except_ for the fact that the last argument must be equal to the number of groups in the regex under consideration (per the spec). **)
  Definition rer: RegExpRecord :=
    {|
      RegExpRecord.ignoreCase := true;
      RegExpRecord.multiline := true;
      RegExpRecord.dotAll := true;
      RegExpRecord.unicode := tt;
      RegExpRecord.capturingGroupsCount := 0
    |}.

  (** We represent the input as a sequence of characters. **)
  Definition input_of_interest :=
    a :: a :: a :: nil.

  (** Let's first show that this regex is valid, i.e. it passes the early errors phase. **)

  (* About EarlyErrors.Pass_Regex. *)

  Lemma passes_early_errors:
    EarlyErrors.Pass_Regex regex_of_interest nil.
  Proof.
    (** We have a concrete regex, so we can just analyze it. **)
    repeat constructor.
  Qed.

  (** Then let's show that the compilation succeeds. **)

  Definition compilation_result :=
    Semantics.compilePattern regex_of_interest rer.

  Lemma compiles_successfully:
     exists m, compilation_result = Result.Success m.
  Proof.
    (** Again, since the regex is concrete, we can just compute. **)
    eexists. cbn. reflexivity.

    (** But we can also use some theorems from the development, which would work even if the regex was left more abstract. **)
    Restart.

    (* Search Semantics.compilePattern Result.Success. *)

    (** We use the theorem listed in section 4.2.1 in the paper, [compilePattern_success], which states that compilation always succeeds if a regex passes early error checks. **)
    apply compilePattern_success.
    - (** We have to show that the number of groups per [rer] matches the actual number
          of groups in the regex… **)
      reflexivity.
    - (** … and that the early-errors check passes, as we proved above: **)
      exact passes_early_errors.
  Qed.

  (** Finally, let's show that the matching succeeds. **)
  Lemma matching_succeeds:
    forall m, compilation_result = Success m ->
         exists pos,
           m input_of_interest 0 = match_state input_of_interest pos nil.
  Proof.
    (** We start by extracting the compiled [m]. **)
    injection 1; intros; subst.

    (** Then, we try the computational route again. **)
    eexists.
    cbn.
    (** Stuck! The computation blocks on functions that we left abstract — specifically [CharSet.exist_canonicalized] which checks whether the set [{a}] contains the character [a].  Thankfully, set axioms are enough to make progress. *)

    rewrite -> Parameters.CharSet.exist_canonicalized_equiv.
    rewrite -> Parameters.CharSet.singleton_exist.

    (** [==?] is reflexive, which allows us to progress further… **)

    rewrite EqDec.reflb.

    (** What we now see is that the computation of the compiled matcher [m] completed and returned a [match_state] object.  This object stores the original string and the current position of the matcher.  A match was found after one character, which allows us to conclude. **)

    reflexivity.
  Qed.

  (** All done!  For excited readers, here's an exercise.  You can try to prove that the regex does *not* match on a different string.  Here are two more assumptions that you will need: a character, and an assumption that this new character isn't equal to the original one. **)

  Context {b: Character}.
  Context {NEQ: (Character.canonicalize rer a ==? Character.canonicalize rer b)%wt = false}.

  (** Here is your theorem! **)
  Lemma matching_terminates':
    forall m, compilation_result = Success m ->
         m (b :: b :: b :: nil) 0 = None.
  Proof.
  Abort.

  (** Here is the solution, obfuscated in [base64]:

      <<
ICAgICAgICBQcm9vZi4KICAgICAgICAgIGluamVjdGlvbiAxOyBpbnRyb3M7IHN1YnN0LgogICAg
ICAgICAgY2JuLgogICAgICAgICAgcmV3cml0ZSAtPiBQYXJhbWV0ZXJzLkNoYXJTZXQuZXhpc3Rf
Y2Fub25pY2FsaXplZF9lcXVpdi4KICAgICAgICAgIHJld3JpdGUgLT4gUGFyYW1ldGVycy5DaGFy
U2V0LnNpbmdsZXRvbl9leGlzdC4KICAgICAgICAgIHJld3JpdGUgTkVRLgogICAgICAgICAgZWFz
eS4KICAgICAgICBRZWQuCg==
      >> **)
End AbstractMatching.
