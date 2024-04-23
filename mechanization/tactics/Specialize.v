Inductive Specialized {A B: Type} (a: A) (b: B) :=
| AlreadySpecialized: Specialized a b.
Ltac auto_specialize := repeat match goal with
| [ a: _, b: _ |- _ ] => lazymatch goal with
  | [ _: Specialized a b |- _ ] => fail
  | [ |- _ ] =>
    pose proof (AlreadySpecialized a b);
    let H := fresh a b in
    pose proof a as H;
    specialize H with (1 := b)
  end
end.

Ltac specialize_once := match goal with
| [ H: _, H': _ |- _ ] => specialize H with (1 := H')
end.