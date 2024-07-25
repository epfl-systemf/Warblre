# 2024 Additions --- a.k.a. the `v` flag

# Background

The change set w.r.t the previous edition can be seen [here](https://arai-a.github.io/ecma262-compare/?from=1c5ca183844ab453f939f1ee6165747c8b1c64ee&to=6ec325c22e9b3c47397c95c6b301491e76edb768&id=sec-regexp-regular-expression-objects&secAll=true&secSubtree=true).
The discussion before merge can be seen [here](https://github.com/tc39/ecma262/pull/2418).
Some more discussions can be found in the original [google doc](https://docs.google.com/document/d/1Tbv3hfX9CxQtzH9r-JdxJsQZhmmDsidRUKKxg345JV0/edit#heading=h.kijenta0fu5k).

This edition incorporates two proposals:
1. [« Support properties of strings (a.k.a. “sequence properties”) in Unicode property escapes »](https://github.com/tc39/proposal-regexp-unicode-sequence-properties?tab=readme-ov-file)
2. [« RegExp v flag with set notation + properties of strings »](https://github.com/tc39/proposal-regexp-unicode-sequence-properties?tab=readme-ov-file).

The latter technically subsumes the former,
but these can be seen as two separate additions:
1. String properties;
2. Set notations.

# Discussion of the new features

## String properties

The biggest impact of this feature is the change of definition of `CharSet`.
Whereas previously a character class was being compiled to a set of character (hence the name `CharSet`),
it can now be compiled to a set of strings (or sequence of characters), depending on the presence of `v`.

This change could prove problematic, since the operations available on `CharSetElement` differ wildly depending on the flags.
A solution might be to abstract the logic manipulating `CharSet`s in `CompileAtom`, like we handled `Canonicalize`.

## Set notations

These new features should require minimal changes.
Character classes should be changed to accommodate nesting.
Most of the work to implement the new operators can be delegated to operations on sets.

# The changes, section per section

Note that the table numbers have been shifted.

## 22.2.1 Patterns

The changes here will cause some irrelevant changes in the subsequent sections,
as some variables will be renamed accordingly.

## 22.2.1.1 Static Semantics: Early Errors

- Safeguard preventing string properties if `v` is not toggled;
- Negated character classes (`[^...]`, `\P{...}`) are rejected.


## 22.2.1.6 Static Semantics: CharacterValue

- New rules for special characters/escapes in `ClassSetCharacter`

## 22.2.1.7 Static Semantics: MayContainStrings

New analysis: detects whether a character class might match strings,
i.e. whether it might consume more than one character from the input.

## 22.2.2.1 Notation

- `CaptureRange` and `MatchState` are now said to be record rather than tuples; note that they were already being used
  (and were mechanized) as if they were records.
   Note that this make the diff look more bigger than it actually is.
- `CharSetElement` is now defined "dependently" of the `v` flag as either a `Character` (as before) or a `list Character`.

## 22.2.2.1.1 RegExp Records

Add `v` flag to record.

## 22.2.2.3 Runtime Semantics: CompileSubpattern

Modularize `Disjunction`, `Empty`, `Sequence` matchers into functions (sections 22.2.2.3.[2-4])

## 22.2.2.7 Runtime Semantics: CompileAtom

- `AllCharacters` is now a function
- `Atom :: CharacterClass` and `AtomEscape :: CharacterClassEscape` become way more complex, mostly in order to 
   implement the longest-match semantics of string properties.
   The behavior being wildly different depending on the flag
   (which is amplified by the wide difference on the definition of `CharSetElement`) make these functions candidates
   for abstraction. Additionally, the two implement the exact same logic.
   The differences are concentrated in the very first steps (`-` is `Atom :: CharacterClass` and `+` `AtomEscape :: CharacterClassEscape`):
   ```
    + 1. Let cs be CompileToCharSet of CharacterClassEscape with argument rer.

    - 1. Let cc be CompileCharacterClass of CharacterClass with argument rer.
    - 2. Let cs be cc.[[CharSet]].

    + 2. If rer.[[UnicodeSets]] is false, or if every CharSetElement of cs consists of a single character (including if cs is empty), return CharacterSetMatcher(rer, cs, false, direction).
    - 3. If rer.[[UnicodeSets]] is false, or if every CharSetElement of cs consists of a single character (including if cs is empty), return CharacterSetMatcher(rer, cs, cc.[[Invert]], direction).

    - 4. Assert: cc.[[Invert]] is false.
    ```

## 22.2.2.7.1 CharacterSetMatcher ( rer, A, invert, direction )

New assertions at the beginning if `v`; should hold by new early errors.

## 22.2.2.7.3 Canonicalize ( rer, ch )

Unicode mode check changed to use the new `HasEitherUnicodeFlag` function.

## 22.2.2.8 Runtime Semantics: CompileCharacterClass

Use `CharacterComplement` with `v` flag.

## 22.2.2.9 Runtime Semantics: CompileToCharSet

- Use `CharacterComplement`.
- Use `MaybeSimpleCaseFolding`.
- Implement new set operators.
- Implement new character classes.

## 22.2.2.9.2 HasEitherUnicodeFlag ( rer )

New function.

## 22.2.2.9.3 WordCharacters ( rer )

Unicode mode check changed to use the new `HasEitherUnicodeFlag` function.

## 22.2.2.9.[4-6] AllCharacters ( rer )

New functions.

## 22.2.2.9.7 UnicodeMatchProperty ( rer, p )

Add lookup into string properties table.

## 22.2.2.10 Runtime Semantics: CompileClassSetString

New function.

## 22.2.[3-...]

Not covered.

# Comments and questions

- What happens when `v` is enabled but not `u` (yes, it's valid; see this [issue](https://github.com/tc39/proposal-regexp-v-flag/issues/23))?
- The fact that the the `MayContainStrings` analysis is done before compiling the set forces it to be extremely pessimistic,
  e.g. `[\p{emoji}--\p{emoji}]` is analyzed as potentially containing strings, despite being empty.
- In positive lookarounds: from `Let y be r's MatchState.` to `Assert: r is a MatchState.`.
  Makes more sense from spec perspective, but the previous wording was better for us.
- `AllCharacters` has a special case for `vi` flags; why? Seems like the answer might be in this [discussion](https://github.com/tc39/proposal-regexp-v-flag/issues/30).
