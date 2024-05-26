type integer = BigInt.t
let of_int: int -> integer = BigInt.of_int
let to_int: integer -> int = BigInt.to_int
let incr: integer -> integer = BigInt.Nat.succ
let sub: integer -> integer -> integer = BigInt.sub
let to_string: integer -> string = BigInt.to_string