(*
  API to use JavaScript's BigInt
  See https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt
*)

type t = Z.t

let zero: t = Z.zero
let one: t = Z.one

let of_int: int -> t = Z.of_int
let to_int: t -> int = Z.to_int
let to_string: t -> string = Z.to_string

let neg: t -> t = Z.neg

let add: t -> t -> t = Z.add
let sub: t -> t -> t = Z.sub
let mult: t -> t -> t = Z.mul
let rem: t -> t -> t = Z.rem
let equal: t -> t -> bool = Z.equal


let le: t -> t -> bool = Z.leq
let lt: t -> t -> bool = Z.lt
let ge: t -> t -> bool = Z.geq
let gt: t -> t -> bool = Z.gt


let max: t -> t -> t = Z.max
let min: t -> t -> t = Z.min

let shift_left: t -> int -> t = Z.shift_left

(* Operations preventing their result from going below zero. *)
module Nat = struct
  let succ: t -> t = fun n -> (assert (n >= Z.zero); Z.succ n)
  let pred: t -> t = fun n -> (assert (n >= Z.zero); if Z.equal n Z.zero then Z.zero else Z.pred n)
  let min: t -> t -> t = (fun l r -> assert (l >= Z.zero); assert (r >= Z.zero); if Z.lt l r then Z.zero else Z.sub l r)
end