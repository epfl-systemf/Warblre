Declare Scope option_flow.

Notation "'let!' r '<-' y 'in' z" := (match y with 
  | Some v => (fun r => z) v
  | None => None
  end)
  (at level 20, r pattern, y at level 100, z at level 200) : option_flow.

(* Notation "'if!' b 'then' z" := (if b then z else None) (at level 20, only parsing) : option_flow. *)

Notation "'assert!' b 'in' z" := (if b then z else None) (at level 20, b at level 100, z at level 100): option_flow.

Notation "'destruct!' r '<-' y 'in' z" := (match y with
  | r => z
  | _ => None
  end)
  (at level 20, r pattern, y at level 100, z at level 200) : option_flow.

Notation "'!!' v" := (Some v) (at level 20, only parsing) : option_flow.