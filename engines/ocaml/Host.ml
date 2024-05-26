type integer = int
let of_int: int -> integer = fun i -> i
let to_int: integer -> int = fun i -> i
let incr: integer -> integer = (+) 1
let sub: integer -> integer -> integer = Int.sub
let to_string: integer -> string = string_of_int