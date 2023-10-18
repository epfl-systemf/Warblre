Require Import ZArith.

(* 5.2.5 Mathematical Operations
   «  Mathematical values: Arbitrary real numbers, used as the default numeric type. »
   «  When the term integer is used in this specification, it refers to a mathematical 
      value which is in the set of integers, unless otherwise stated. When the term integral 
      Number is used in this specification, it refers to a Number value whose mathematical
      value is in the set of integers. »
   ... so, that should be a Real? (note that "integers" redirects to the second definition).
*)
Definition integer := Z.
Definition non_neg_integer := nat.
Definition non_neg_integer_or_inf := option nat.

Notation "'+∞'" := (@None nat).

(* Notation "x '<=' y" := (Z.compare x y = Lt \/ Z.compare x y = Eq). *)
