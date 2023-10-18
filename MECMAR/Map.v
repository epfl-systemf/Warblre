Module DMap.
  Record type := make_map {
    map: forall (A B: Type), Type;
    add: forall (A B: Type), map A B -> A -> B -> map A B;
    get: forall (A B: Type), map A B -> A -> option B;
  }.
End DMap.

Module DSet.
  Record type := make_set {
    set: forall (A: Type), Type;
    add: forall (A: Type), set A -> A -> set A;
    contains: forall (A: Type), set A -> bool;
  }.
End DSet.