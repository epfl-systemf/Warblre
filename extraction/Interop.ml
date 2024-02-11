exception NotImplemented of string

let parse_hex d1 d2 = int_of_string ("0x" ^ (String.make 1 d1) ^ (String.make 1 d2))

let all_chars = List.init 128 (Char.chr)
let line_terminators = '\n' :: '\r' :: []
let white_spaces = List.map (Char.chr) ( 11 :: 13 :: 14 :: [])
let digits = '0' :: '1' :: '2' :: '3' :: '4' :: '5' :: '6' :: '7' :: '8' :: '9' :: []
let ascii_word_characters = 
  let str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_" in
  List.init (String.length str) (String.get str)

let numeric_value c = Char.code c
let ascii_letter c = c
let code_point c = c
let to_upper_case c = Char.uppercase_ascii c
let code_points_to_string c = c :: []
let case_fold _ = raise (NotImplemented "case_fold")