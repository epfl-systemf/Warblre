Declare Scope result_flow.

Module Result.
  Inductive Result (S F: Type) :=
  | Success (s: S)
  | Failure (f: F).
  Arguments Success {S F} s.
  Arguments Failure {S F} f.

  Class AssertionError (F: Type) := { f: F }.

  Definition from_option {S F: Type} (o: option S) (f: F): Result S F := match o with
  | Some x => Success x
  | None => Failure f
  end.

  Definition map { S T F: Type } (r: Result S F) (f: S -> T): Result T F := match r with
  | Success s => Success (f s)
  | Failure f => Failure f
  end.

  Definition flatMap { S T F: Type } (r: Result S F) (f: S -> Result T F): Result T F := match r with
  | Success s => f s
  | Failure f => Failure f
  end.

  Definition assertion_failed {S F: Type} {failure: AssertionError F}: Result S F :=
    let (f) := failure in
    Failure f.

  Module Notations.
    Notation "'let!' r '<-' y 'in' z" := (match y with 
      | Success v => Success ((fun r => z) v)
      | Failure f => Failure f
      end)
      (at level 20, r pattern, y at level 100, z at level 200): result_flow.
    Notation "'let!' r '=<<' y 'in' z" := (match y with 
      | Success v => ((fun r => z): _ -> Result _ _) v
      | Failure f => Failure f
      end)
      (at level 20, r pattern, y at level 100, z at level 200): result_flow.

    Notation "'assert!' b ';' z" := (if (negb b) then assertion_failed else z) (at level 20, b at level 100, z at level 100): result_flow.

    Notation "'destruct!' r '<-' y 'in' z" := (match y with
      | r => z
      | _ =>assertion_failed (* Otherwise, consider the failure as an assertion failure *)
      end)
      (at level 20, r pattern, y at level 100, z at level 200): result_flow.
  End Notations.
End Result.
Export Result(Result, Success, Failure).