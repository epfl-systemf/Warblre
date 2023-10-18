Declare Scope result_flow.

Module Result.
  Inductive Result (S F: Type) :=
  | Success (s: S)
  | Failure (f: F)
  | AssertionError.
  Arguments Success {S F} s.
  Arguments Failure {S F} f.
  Arguments AssertionError {S F}.

  Definition map { S T F: Type } (r: Result S F) (f: S -> T): Result T F := match r with
  | Success s => Success (f s)
  | Failure f => Failure f
  | AssertionError => AssertionError
  end.

  Definition flatMap { S T F: Type } (r: Result S F) (f: S -> Result T F): Result T F := match r with
  | Success s => f s
  | Failure f => Failure f
  | AssertionError => AssertionError
  end.
  
  Module Notations.
    Notation "'let!' r '<-' y 'in' z" := (match y with 
      | Success v => (fun r => z) v
      | Failure f => Failure f
      | AssertionError => AssertionError
      end)
      (at level 20, r pattern, y at level 100, z at level 200) : result_flow.

    Notation "'assert!' b ';' z" := (if b then z else AssertionError) (at level 20, b at level 100, z at level 100): result_flow.

    Notation "'destruct!' r '<-' y ';' z" := (match y with
      | r => z
      | _ => AssertionError
      end)
      (at level 20, r pattern, y at level 100, z at level 200) : result_flow.
  End Notations.
End Result.
Export Result.