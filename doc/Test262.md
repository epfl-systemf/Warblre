# Testing the extracted engine against Test262

[Test262](https://github.com/tc39/test262) is the standard test suite for JavaScript implementations.
Among other things, it contains [tests for regex engines](https://github.com/tc39/test262/tree/main/test/built-ins/RegExp) compliant to the ECMAScript specification.

Tests however take the form of JavaScript programs (e.g.
[this](https://github.com/tc39/test262/blob/main/test/built-ins/RegExp/unicode_full_case_folding.js)
or [this](https://github.com/tc39/test262/blob/main/test/built-ins/RegExp/CharacterClassEscapes/character-class-non-word-class-escape-flags-u.js)),
which means that the tests are not suited to test a standalone engine like our extracted engine.

As such, the engine must be tested by modifying a fully-featured regex engine (such as [V8](https://v8.dev/)).
This is achieved by the Test262 wrapper (in the `test262` directory), which is a tiny program which modifies the JavaScript runtime it is run in such that it will then use the extracted engine.
This wrapper also implements some quirks of the JavaScript regex engine which only make sense in the context of a JavaScript runtime (e.g. value coercions; see the implementation for details).

Note that Test262 doesn't do versioning, and that commits which are too recent might contain tests for features we do not support.
We recommend using the commit [4d44acb](https://github.com/tc39/test262/commit/4d44acbc033c8aa38896f41fb3bdc96d6aeee2b8), which is known to only test features defined in the 14th edition.

## Example script

Assuming that
- The wrapper was compiled into a standalone JavaScript file (`dune build test262`);
- That [Node.js](https://nodejs.org/en) was installed, as well as [Test262-Harness](https://github.com/bterlson/test262-harness) (`npm install -g test262-harness`);
- That the environment variables `WARBLRE` and `TEST262` contain respectively the absolute path of the root of this repository and the root of the test262 repository;

this script should run the relevant tests against V8 modified to use our extracted engine.

```bash
#!/usr/bin/env bash

set -e

#############
# Variables #
#############

# Check variables
if [ -z "${WARBLRE}" ]; then
    echo "WARBLRE is unset (or empty)."
    exit -1
fi
WARBLRE=$(realpath ${WARBLRE})

if [ -z "${TEST262}" ]; then
    echo "TEST262 is unset (or empty)."
    exit -1
fi
TEST262=$(realpath ${TEST262})

# Resolve some basic paths
NODE=$(which node)
HARNESS=$(which test262-harness)
OUTPUT=test262.out.txt

# Stack size; the engine consumes a lot of stack space
STACK_kBytes=$((800*1024))

# Exclude experimental features
FEATURES_EXCL=--features-exclude="regexp-v-flag,regexp-duplicate-named-groups"

##################
# Category setup #
##################

# Test timeout
TIMEOUT_SEC=30
TIMEOUT_MIN=0
TIMEOUT_HRS=0
# Timeout must be in ms
TIMEOUT=$(( (($TIMEOUT_HRS*60 + $TIMEOUT_MIN)*60 + $TIMEOUT_SEC) * 1000 ))

# property-escapes tests are slow and for the most part not supported
TESTS=$(cd ${TEST262} && find test/built-ins/RegExp -name '*.js' \
       ! -regex '.*/property-escapes/.*')
echo Found "$(echo "${TESTS}" | wc -w)" tests before filtering.

# Number of tests run in parallel
THREADS_COUNT=4

##############
# Test setup #
##############

ulimit -s $STACK_kBytes
echo "Setting stack size limit to ${STACK_kBytes}KiB."
echo "Timeout is set to $TIMEOUT milliseconds (${TIMEOUT_HRS}h ${TIMEOUT_MIN}min ${TIMEOUT_SEC}sec)."
echo "Work output in ${OUTPUT}."
echo "${THREADS_COUNT} tests will run in parallel."

#################
# Run the tests #
#################

echo "Running test262..."
(cd ${TEST262} &&
    time "${HARNESS}" \
        --timeout="${TIMEOUT}" \
        --threads="${THREADS_COUNT}" \
        --host-type=node --host-path="${NODE}" \
        --host-args=--stack-size="${STACK_kBytes}" \
        --prelude="${WARBLRE}/_build/default/test262/warblre-node-redirect.js" \
        "${FEATURES_EXCL}" ${TESTS} > "${OUTPUT}")
echo "... done."
```

A virtual machine is [available](https://zenodo.org/records/11494317),
which contains a previous version of this repository,
a clone of the Test262 repository
with everything setup as to allow to test the engine against Test262.
The suggested script above is inspired from the one included in that VM.

## Requirements to pass some tests

Here are some conditions and optimizations which are implemented in order to pass some tests.
Each one is prefixed (in brackets) with the location where it is implemented.
If *(optimization)* is also present, it means that it is not strictly required for correctness of the engine,
but allows tests to be passed in more reasonable time.

- [Extraction] Numeric values must be unbounded, i.e. `BigInt` must be used;
- [Test262 wrapper (optimization)] Regex compilation must be cached (but caching to many regexes might result in out-of-memory errors);
- [OCaml module instantiation (optimization)] The [following operation](https://tc39.es/ecma262/2024/multipage/text-processing.html#sec-runtime-semantics-charactersetmatcher-abstract-operation)
  ```
  l. If there exists a CharSetElement in A containing exactly one character a such that Canonicalize(rer, a) is cc, let found be true. Otherwise, let found be false.
  ```
  must be optimized so that the set is not being fully traversed every time.
  This is achieved by using `CachedCharSet` in the JavaScript engine (defined in `engines/js/JsEngineParameters.ml`).

## Slow & failing tests

The following tables document tests which are known to be either slow or fail.
These results were obtained by using our engine in combination with Node.js, and some of the failing tests reflect that fact.

| Slow test                                                                                      | Category                |
| ---------------------------------------------------------------------------------------------- | ----------------------- |
| `S15.10.2_A1_T1.js`                                                                            | Slow (magnitude: hours) |
| `named-groups/unicode-match.js`                                                                | Slow (magnitude: hours) |
| `named-groups/unicode-property-names-valid.js`                                                 | Slow (magnitude: hours) |
| `CharacterClassEscapes/character-class-non-digit-class-escape-plus-quantifier.js`              | Slow (magnitude: hours) |
| `CharacterClassEscapes/character-class-non-whitespace-class-escape-plus-quantifier.js`         | Slow (magnitude: hours) |
| `CharacterClassEscapes/character-class-non-word-class-escape-plus-quantifier.js`               | Slow (magnitude: hours) |
| `CharacterClassEscapes/character-class-non-digit-class-escape-plus-quantifier-flags-u.js`      | Never ran to completion |
| `CharacterClassEscapes/character-class-non-whitespace-class-escape-plus-quantifier-flags-u.js` | Never ran to completion |
| `CharacterClassEscapes/character-class-non-word-class-escape-plus-quantifier-flags-u.js`       | Never ran to completion |

| Failing test                                                | Category       | Explanation                                                                                                                                                                                                                                              |
| ----------------------------------------------------------- | -------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `prototype/Symbol.match/flags-tostring-error.js`            | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.match/get-flags-err.js`                   | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.match/get-unicode-error.js`               | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.replace/flags-tostring-error.js`          | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.replace/get-flags-err.js`                 | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.replace/get-unicode-error.js`             | Node issue     | [Known issue](https://issues.chromium.org/issues/42203113)                                                                                                                                                                                               |
| `prototype/Symbol.replace/fn-invoke-args-empty-result.js`   | Node issue     | [Known issue](https://issues.chromium.org/issues/42200389)                                                                                                                                                                                               |
| `prototype/Symbol.replace/poisoned-stdlib.js`               | Prototype test | This test ensures that the engine does not rely on JavaScript's standard library; our engine does, and hence fails this test.                                                                                                                            |
| `prototype/exec/not-a-constructor.js`                       | Prototype test | `Regex.prototype.exec` should not be a [constructor](https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#constructor); to our knowledge, that is not possible from JavaScript user space when adding the need to access `this`. |
| `prototype/Symbol.match/builtin-infer-unicode.js`           | Prototype test | Passing this test would require our engine to have access to [internal slots](https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-object-internal-methods-and-internal-slots), which is not possible from  user space.      |
| `prototype/Symbol.match/builtin-success-g-set-lastindex.js` | Prototype test | Passing this test would require our engine to have access to [internal slots](https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-object-internal-methods-and-internal-slots), which is not possible from  user space.      |
