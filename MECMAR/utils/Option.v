Module Option.
  Definition eqb{T: Type}(teqb: T -> T -> bool)(l r: option T): bool := match l, r with
  | Some l', Some r' => teqb l' r'
  | None, None => true
  | _, _ => false
  end.
End Option.