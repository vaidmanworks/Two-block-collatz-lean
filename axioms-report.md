# Axioms report

Lean 4 version 4.27.0 (commit `db93fe1`), Mathlib commit `a3a10db`. Produced 2026-10-31.

## Result

Each of the 48 main results was checked with Lean's `#print axioms`. Between them they use three axioms and no
others:

```lean
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
```

47 results use all three. One uses only `propext` and `Quot.sound`.

`#print axioms` follows every lemma a proof uses, down to Lean's core library, so the list also covers the Mathlib
lemmas the proofs call.

## Why these are legitimate

These are Lean's three standard axioms, declared in Lean's own core library. Mathlib's theorems rest on the same three.

- `propext`: propositional extensionality. Two propositions that imply each other are equal.
- `Classical.choice`: the axiom of choice, the basis of classical logic in Lean.
- `Quot.sound`: two elements related by a relation are equal in its quotient. Function extensionality is derived
  from it.

## What does not appear

- `sorryAx`: Lean adds it to any proof with a gap left open (`sorry`). It is absent, so every proof is complete.
- Any axiom declared in the project itself. The sources contain no `axiom` declaration. Outside inputs, such as
  cited theorems and published computations, enter as explicit hypotheses of the theorems, never as axioms.
- `Lean.ofReduceBool` and `Lean.trustCompiler`: these appear when a proof trusts compiled code (`native_decide`).
  They are absent, so every step was checked by Lean's kernel.

## How to confirm

Someone with the proof files can reproduce this report: build them with `lake build`, then run `#print axioms` on
each result. Without the proof files, this report is a statement of what that check printed, not a proof of it.
