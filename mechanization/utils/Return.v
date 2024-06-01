From Warblre Require Import Result.

(** Facilities used to implement functions which mix general recursion and imperative return. *)

Module Return.
  (* Continue means that the the computation has not yet returned; Returned mean that no more computations should be done. *)
  Inductive Return (S R: Type) :=
  | Continue: S -> Return S R
  | Returned : R -> Return S R.
  Arguments Continue {_} {_}.
  Arguments Returned {_} {_}.

  Definition continue {S R: Type} (v: S) := @Continue S R v.
  Definition ret {S R: Type} (r: R) := @Returned S R r.

  Definition bind {S T R} (m: Return S R) (f: S -> Return T R): Return T R :=
    match m with
    | Continue s => f s
    | Returned r => Returned r
    end.

  Definition map {S T R} (m: Return S R) (f: S -> T): Return T R :=
    match m with
    | Continue s => Continue (f s)
    | Returned r => Returned r
    end.

  (* Exit by either getting the returned value, or by taking the computed expression as the result. *)
  Definition exit {S} (m: Return S S): S :=
    match m with
    | Continue s => s
    | Returned s => s
    end.

  (** Fuel based recursion, allowing imperative return. *)

  Definition loop {S T R F} (out_of_fuel: F) (fuel: nat) (init: S) (step: S -> Result (Return (S + T) R) F): Result (Return T R) F :=
    let fix iter (fuel: nat) (current: S + T): Result (Return T R) F :=
      match fuel with
      | 0 => Error out_of_fuel
      | S fuel' =>
        match current with
        | inl s =>
          Result.bind (step s) (fun s =>
            match s with
            | Continue c => iter fuel' c
            | Returned r => Success (Returned r)
            end
          )
        | inr t => Success (Continue t)
        end
      end
    in
    iter fuel (inl init).

  Definition while {S R F} (out_of_fuel: F) (fuel: nat) (init: S) (stop: S -> bool) (step: S -> Result (Return S R) F): Result (Return S R) F :=
    loop out_of_fuel fuel init (
      fun s => if negb (stop s) then Success (Continue (inr s)) else Result.map (step s) (fun m => map m inl)
    ).
End Return.