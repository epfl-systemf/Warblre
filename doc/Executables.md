# Executables

## Examples \[Both\]

## Fuzzer \[JavaScript\]

## Tests \[OCaml\]

## Test262 \[JavaScript\]

Implement logic which replaces the regex engine provided by a JavaScript host with our JavaScript engine.

If using [test262-harness](https://github.com/bterlson/test262-harness), one can use its `--prelude` option to use our engine, e.g.
```
test262-harness --host-type=node --host-path=$(which node) --prelude=path/to/warblre-node-redirect.js test/**/u180e.js
```
where `warblre-node-redirect.js ` is built using
```
dune build test262
```
and is located (by default) under `_build/default/test262/warblre-node-redirect.js`
