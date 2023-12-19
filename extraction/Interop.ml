exception NotImplemented of string

let line_terminators = '\n' :: '\r' :: []
let all_chars = List.init 128 (Char.chr)

let code_point c = c
let to_upper_case c = Char.uppercase_ascii c
let code_points_to_string c = c :: []
let case_fold _ = raise (NotImplemented "case_fold")