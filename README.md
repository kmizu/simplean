# Simplean

A tiny imperative language — `Int`, `String`, `List[T]`, `if`/`while`, functions, variables — with a
**fuel-based reference interpreter**, a **stack VM**, a **compiler**, and **machine-checked proofs** in
Lean 4 (v4.34.1, no Mathlib):

- type soundness (`Simplean.soundness`),
- soundness of the type checker (`Simplean.checkProg_sound`),
- compiler correctness as a forward simulation (`Simplean.compile_correct`, `Simplean.main_correct`),
- fuel monotonicity and determinism (`Simplean.evalProg_det`, `Simplean.run_det`),
- and the combined theorem `Simplean.final`.

The proofs depend only on `propext`, `Classical.choice`, `Quot.sound` (checked with `#guard_msgs in #print axioms`).

**Tutorial (Japanese):** https://kmizu.github.io/simplean/ — a Lean 4 beginner's guide that walks through every
file of this repository.

## 日本語

Int / String / List[T]、if / while、関数と変数だけの小さな言語 **Simplean** の、fuel 付き参照インタプリタ・
スタック VM・コンパイラと、Lean 4 による証明（型健全性、型検査器の健全性、コンパイラ正当性、決定性）です。
Lean 4 初心者向けのチュートリアルを mdBook で公開しています：https://kmizu.github.io/simplean/

## Build

```sh
lake build --wfail          # library + proofs + decide tests, warnings are errors
lake build Exercises        # exercise stubs (sorry allowed)
mdbook build docs           # the tutorial (mdBook 0.4.40)
python3 scripts/check_includes.py
```

## Layout

| Path | Contents |
|---|---|
| `Simplean/Syntax.lean`, `Ops.lean`, `AList.lean` | AST, values, `HasType`, operators, environments |
| `Simplean/Typing.lean`, `Checker.lean` | typing rules (spec) and type checker (impl) + soundness |
| `Simplean/Res.lean`, `Semantics.lean` | fuel-based definitional interpreter |
| `Simplean/Soundness.lean` | type soundness by induction on fuel |
| `Simplean/VM.lean`, `VMLemmas.lean`, `Compiler.lean` | stack VM, its lemmas, compiler |
| `Simplean/Correctness/*.lean` | forward simulation, `main_correct` |
| `Simplean/Determinism.lean` | fuel monotonicity, determinism, `final` |
| `Simplean/Examples.lean`, `Tests.lean` | example programs, `decide` tests, axiom guards |
| `Exercises/` | exercise stubs |
| `docs/` | mdBook tutorial (Japanese) |
