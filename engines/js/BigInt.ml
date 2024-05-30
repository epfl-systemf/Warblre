(*
  API to use JavaScript's BigInt
  See https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt
*)

type t = Js.Bigint.t

let zero: t = [%mel.raw {| BigInt(0) |}]
let one: t = [%mel.raw {| BigInt(1) |}]

let of_int: int -> t = [%mel.raw {| function (i) { return BigInt(i); } |}]
let to_int: t -> int = [%mel.raw {| function (i) { return Number(i); } |}]
let of_float: Js.Float.t -> t = [%mel.raw {| function (i) { return BigInt(Math.trunc(i)); } |}]
let to_string: t -> Js.String.t = [%mel.raw {| function (i) { return i.toString(); } |}]

let neg: t -> t = [%mel.raw {| function (i) { return -i; } |}]

let add: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l + r;
  } }
|}]
let sub: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l - r;
  } }
|}]
let mult: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l * r;
  } }
|}]
let rem: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l % r;
  } }
|}]
let equal: t -> t -> bool = [%mel.raw {|
  function (l) { return function (r) {
    return l === r;
  } }
|}]


let le: t -> t -> bool = [%mel.raw {|
  function (l) { return function (r) {
    return l <= r;
  } }
|}]
let lt: t -> t -> bool = [%mel.raw {|
  function (l) { return function (r) {
    return l < r;
  } }
|}]
let ge: t -> t -> bool = [%mel.raw {|
  function (l) { return function (r) {
    return l >= r;
  } }
|}]
let gt: t -> t -> bool = [%mel.raw {|
  function (l) { return function (r) {
    return l > r;
  } }
|}]


let max: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l > r ? l : r;
  } }
|}]
let min: t -> t -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l < r ? l : r;
  } }
|}]

let shift_left: t -> int -> t = [%mel.raw {|
  function (l) { return function (r) {
    return l << BigInt(r);
  } }
|}]

(* Operations preventing their result from going below zero. *)
module Nat = struct
  let succ: t -> t = [%mel.raw {|
    function (n) {
      return n + BigInt(1);
    }
  |}]
  let pred: t -> t = [%mel.raw {|
    function (n) {
      let p = n - BigInt(1);
      return p < BigInt(0) ? BigInt(0) : p;
    }
  |}]
  let min: t -> t -> t = [%mel.raw {|
    function (l) { return function(r) {
      let p = l - r;
      return p < BigInt(0) ? BigInt(0) : p;
    } }
  |}]
end