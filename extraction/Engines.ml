open Extracted

module type Engine = sig
  include Encoding.Character

  val unicode: bool

  val countGroups: character Patterns.coq_Regex -> int

  val compilePattern :
    character Patterns.coq_Regex -> RegExpRecord.coq_type ->
    (character list -> non_neg_integer -> character
    Notation.coq_MatchResult, CompileError.coq_type) Result.coq_Result


  val initialize :
    character Patterns.coq_Regex -> RegExpFlags.coq_type ->
    (character RegExpInstance.coq_type,
    CompileError.coq_type) Result.coq_Result

  val setLastIndex :
    character RegExpInstance.coq_type -> integer ->
    character RegExpInstance.coq_type

  val exec :
    character RegExpInstance.coq_type ->
    (Unsigned.uint16 list) -> (character
    execResult, MatchError.coq_type) Result.coq_Result
 end

module Utf16Engine : Engine
  with type character = Unsigned.uint16
= struct
  let unicode = false

  include Encoding.Utf16
  include Extracted.Utf16Engine
end

module UnicodeEngine : Engine
  with type character = int
= struct
  let unicode = true

  include Encoding.Unicode
  include Extracted.UnicodeEngine
end