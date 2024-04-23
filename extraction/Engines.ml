open Extracted

module type Engine = sig
  include Encoding.Character

  val countGroups: character Patterns.coq_Regex -> int

  val compilePattern :
    character Patterns.coq_Regex -> RegExpRecord.coq_type ->
    (character list -> non_neg_integer -> character
    Notation.coq_MatchResult, CompileError.coq_type) Result.coq_Result
 end

module Utf16Engine : Engine
  with type character = Unsigned.uint16
= struct
  include Encoding.Utf16
  include Extracted.Utf16Engine
end

module UnicodeEngine : Engine
  with type character = int
= struct
  include Encoding.Unicode
  include Extracted.UnicodeEngine
end