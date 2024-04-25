From Coq Require Import Bool PeanoNat Structures.OrderedType FSets.FSetAVL NArith ZArith.
From Warblre Require Import Typeclasses Tactics Numeric Characters Patterns RegExpRecord StaticSemantics Semantics List Result Notation Frontend.

Parameter host_string: Type.

Module Type EngineParameters.
  Parameter character : Type.
  Parameter unicode : bool.

  Module Character.
    Parameter eq: forall (l r: character), {l=r} + {l<>r}.
    Parameter from_numeric_value: nat -> character.
    Parameter numeric_value: character -> nat.
    Parameter canonicalize: RegExpRecord -> character -> character.

    Axiom numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
    Axiom numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r)).

    Parameter list_from_string: String -> list character.
    Parameter list_to_string: list character -> String.
    Parameter to_host: String -> host_string.
    Parameter from_host: host_string -> String.
  End Character.

  Parameter unicode_property: Type.
  Parameter unicode_property_eqdec: forall (l r: unicode_property), {l=r} + {l<>r}.
  Parameter code_points_for: unicode_property -> list character.

  (** CharSet *)
  Parameter char_set: Type.

  Module CharSet.
    Parameter empty: char_set.
    Parameter from_list: list character -> char_set.
    Parameter union: char_set -> char_set -> char_set.
    Parameter singleton: character -> char_set.
    Parameter size: char_set -> nat.
    Parameter remove_all: char_set -> char_set -> char_set.
    Parameter is_empty: char_set -> bool.
    Parameter contains: char_set -> character -> bool.
    Parameter range: character -> character -> char_set.

    Parameter unique: forall (F: Type) (_: Result.AssertionError F), char_set -> Result character F.
    Parameter filter: char_set -> (character -> bool) -> char_set.
    Parameter exist: char_set -> (character -> bool) -> bool.

    Axiom singleton_size: forall c, size (singleton c) = 1.
    Axiom singleton_unique: forall (F: Type) (af: Result.AssertionError F) c, @unique F af (singleton c) = Success c.
  End CharSet.

  Module CharSets.
    Parameter all: list character.
    Parameter line_terminators: list character.
    Parameter digits: list character.
    Parameter white_spaces: list character.
    Parameter ascii_word_characters: list character.
  End CharSets.
End EngineParameters.


Module Engine (parameters: EngineParameters).
  Definition character := parameters.character.

  (* Instanciation *)
  Definition char_instance: CharacterInstance character := Character.make character
    (EqDec.make _ parameters.Character.eq)
    parameters.Character.from_numeric_value
    parameters.Character.numeric_value
    parameters.Character.canonicalize
    parameters.Character.numeric_pseudo_bij
    parameters.Character.numeric_round_trip_order
    parameters.Character.list_from_string
    (CharSet.make parameters.character parameters.char_set
      parameters.CharSet.empty
      parameters.CharSet.from_list
      parameters.CharSet.union
      parameters.CharSet.singleton
      parameters.CharSet.size
      parameters.CharSet.remove_all
      parameters.CharSet.is_empty
      parameters.CharSet.contains
      parameters.CharSet.range
      parameters.CharSet.unique
      parameters.CharSet.filter
      parameters.CharSet.exist
      parameters.CharSet.singleton_size
      parameters.CharSet.singleton_unique
    )
    parameters.CharSets.all
    parameters.CharSets.line_terminators
    parameters.CharSets.digits
    parameters.CharSets.white_spaces
    parameters.CharSets.ascii_word_characters
    parameters.unicode_property
    (EqDec.make _ parameters.unicode_property_eqdec)
    parameters.code_points_for
  .

  (* Utils *)
  Definition countGroups r := @StaticSemantics.countLeftCapturingParensWithin_impl _ char_instance r.

  (* API *)
  Definition compilePattern := @Semantics.compilePattern _ char_instance.

  Definition initialize := @Frontend.regExpInitialize _ char_instance.
  Definition setLastIndex := @Frontend.RegExpInstance.setLastIndex _ char_instance.
  Definition exec := @Frontend.regExpExec _ char_instance.
End Engine.
