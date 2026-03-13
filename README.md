# Phi

A Haskell-like functional language that compiles directly to Erlang [BEAM](https://www.erlang.org/blog/a-brief-beam-primer/) bytecode. Written in Rust.

## What It Is

Phi is a statically typed, purely functional language with Haskell-style syntax — type classes, do-notation, list comprehensions, pattern matching, guards, where-clauses — that targets the Erlang VM without going through Erlang source. The compiler reads `.phi` source files and writes `.beam` files directly.

```haskell
module HelloWorld (main) where

import System.IO (println)

main :: IO ()
main = println "Hello World from Phi!"
```

## Features

- **Hindley-Milner type inference** with type class constraints
- **Pattern matching** — constructors, literals, tuples, list `[x|xs]` patterns, guards
- **Type classes** — `class`/`instance`/`where`, dictionary passing, multi-parameter classes with functional dependencies
- **Do-notation** and monadic `>>=` / `>>` / `pure`
- **List comprehensions** — `[f x | x <- xs, pred x]`
- **`receive`/`after` syntax** for Erlang message passing
- **Where-clauses** and local `let` bindings (including multi-clause function-style)
- **Lambda lifting** with free-variable capture (`make_fun3`)
- **Foreign Function Interface** — `foreign import` maps to companion `.erl` modules
- **QuickCheck**-style property-based testing
- **194 stdlib modules** — Data.List, Data.Map, Data.Array, Control.Monad, System.IO, Text.Json, Text.Parsec, Test.QuickCheck, and more

## Architecture

The compiler is a single Rust binary with four sequential passes:

```
.phi files
  │
  ▼
[Pass 1] Lexer (logos)
  │  Token stream
  ▼
[Pass 2] Layout resolver
  │  Inserts { } ; for indentation-sensitive syntax
  ▼
[Pass 3] Parser (chumsky)
  │  AST: Module { declarations: Vec<Decl> }
  ▼
[Pass 4] Typechecker
  │  Hindley-Milner + type class constraint solving
  │  Builds global Env (bindings, instances, aliases)
  ▼
[Pass 5] BEAM codegen (beam_writer)
  │  Emits BEAM bytecode directly (no erlc involved)
  ▼
ebin/*.beam
```

Passes 1–3 run **in parallel** via [rayon](https://github.com/rayon-rs/rayon). Pass 4 is sequential (shared `Env`). Pass 5 runs in parallel; companion `.erl` (FFI) files are compiled by `erlc` concurrently in a background thread.

## Project Structure

```
src/
  ast.rs            — AST types: Decl, Expr, Binder, Type, ...
  lexer.rs          — Logos-based tokenizer
  layout.rs         — Haskell layout rule (indentation → braces)
  parser.rs         — Chumsky parser → AST
  type_sys.rs       — MonoType / PolyType definitions
  env.rs            — Type environment (bindings, classes, instances)
  typechecker.rs    — HM inference + type class constraint solving
  beam_writer.rs    — Direct BEAM bytecode emitter
  main.rs           — Driver: orchestrates all passes
  stdlib/           — 180+ standard library .phi modules + FFI .erl files
  tests/            — ~58 test .phi modules
```

## Building

**Requirements:** Rust 1.85+ (edition 2024), Erlang/OTP 25+

```bash
cargo build --release
```

## Running

Compile all stdlib and test modules to `ebin/`:

```bash
cargo run
# or: cargo run -- src/stdlib src/tests
```

Expected output:
```
--- Batch Parsing ---
Summary: 194/194 files parsed successfully.

--- Typechecking ---
Typechecking done: 194/194 ok

--- Codegen (.phi → .beam directly) ---
  Direct .beam: 194 | failed: 0
```

Run the compiled modules in Erlang:

```bash
erl -pa ebin
> F = 'Phi.HelloWorld':main(), F().
Hello World from Phi!
```

Note: IO actions are lazy — `main/0` returns a `fun`; calling it executes the effect.

Run the generated test BEAMs:

```bash
# compile stdlib + test modules into ebin/
cargo run -- src/stdlib src/tests

# start Erlang with generated beams on the code path
erl -pa ebin
```

Then, in the Erlang shell, run:

```erlang
'Phi.Test':main().
```

Notes:

- `src/tests/Test.phi` is the main test entrypoint and is emitted as `ebin/Phi.Test.beam`.
- Companion Erlang FFI modules are also compiled into `ebin/` as `Phi.*.FFI.beam` during `cargo run`.
- If you only want to rebuild generated BEAMs before rerunning tests, rerun `cargo run -- src/stdlib src/tests` and restart `erl -pa ebin`.
- The current README documents a known limitation: `Phi.Test:main/0` runtime constructor dispatch is not yet fully complete.

## Language Reference

### Types

```haskell
data List a = Nil | Cons a (List a)
data Either a b = Left a | Right b

type Name = String
newtype Wrapper a = Wrap { unwrap :: a }
```

### Type Classes

```haskell
class Eq a where
  eq :: a -> a -> Boolean

instance Eq Integer where
  eq x y = x == y
```

### Pattern Matching

```haskell
head :: [a] -> a
head (x:_) = x

zip :: [a] -> [b] -> [(a, b)]
zip []     _      = []
zip _      []     = []
zip (x:xs) (y:ys) = (x, y) : zip xs ys
```

### Do-notation

```haskell
main :: IO ()
main = do
  line <- readLine
  println line
```

### Receive

```haskell
loop :: IO ()
loop = do
  msg <- receive
    { "stop" -> pure ()
    ; x      -> do println x; loop
    } after 5000 -> pure ()
```

### Foreign Import

```haskell
foreign import length "erlang" "length" :: forall a. [a] -> Integer
```

Backed by a companion `Phi.Module.FFI.erl` file for non-trivial FFI.

## BEAM Codegen Notes

The BEAM emitter (`beam_writer.rs`) directly constructs binary `.beam` chunks:
- `Code` chunk: instructions (allocate, move, call, call_ext, call_fun, put_list, put_tuple2, …)
- `Atom`/`AtU8` chunk: intern table
- `ImpT` chunk: external call table  
- `ExpT` chunk: export table
- `FunT` chunk: lambda table (for `make_fun3`)
- `LocT` chunk: local function table

Lambda lifting: free variables are captured at `make_fun3` creation and passed as extra X-register arguments to the lifted function body.

Where-clauses with binders become lifted local functions. Zero-arity where bindings and `PatBind` where-clauses are inlined directly into the parent function body.

## Known Limitations

- Typechecker is permissive (prototype mode): unification failures are silently accepted to maximise compilation success across the full stdlib
- `Phi.Test:main/0` runtime: constructor dispatch for `TestGroup` not yet complete
- No incremental compilation — full rebuild on every `cargo run`
- No source maps or line-number information in generated BEAM files
