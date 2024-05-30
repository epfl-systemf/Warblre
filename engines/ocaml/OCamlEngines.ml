open OCamlEngineParameters

module Utf16Engine = Engines.Engine(Utf16Parameters)
module UnicodeEngine = Engines.Engine(UnicodeParameters)

module Utf16Notations = Notations.CharNotations(Utf16Parameters)(Utf16StringLike)
module UnicodeNotations = struct
  open Patterns
  module Base = Notations.CharNotations(UnicodeParameters)(Utf16StringLike)
  include Base

  let uprop n = AtomEsc (ACharacterClassEsc (UnicodeProp (Obj.magic (UnicodeProperty.Predicate n))))
end

module Utf16Printer = Printers.Printer(Utf16Parameters)(Utf16StringLike)
module UnicodePrinter = Printers.Printer(UnicodeParameters)(Utf16StringLike)

module Utf16Tester = Testing.Tester(Utf16Parameters)(Utf16StringLike)
module UnicodeTester = Testing.Tester(UnicodeParameters)(Utf16StringLike)