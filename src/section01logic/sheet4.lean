/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro h,
  cases h with hP hQ,
  exact hP,
end

example : P ∧ Q → Q :=
begin
  intro h,
  cases h with hP hQ,
  exact hQ,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intro PQR,
  intro PaQ,
  cases PaQ with hP hQ,
  apply PQR,
  exact hP,
  exact hQ,
end

example : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  exact hP,
  exact hQ,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hP hQ,
  split,
  exact hQ,
  exact hP,
end

example : P → P ∧ true :=
begin
  intro hP,
  split,
  exact hP,
  trivial,
end

example : false → P ∧ false :=
begin
  intro hf,
  split,
  exfalso,
  exact hf,
  exact hf,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  intro hQaR,
  cases hQaR with hQ hR,
  split,
  exact hP,
  exact hR,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro hh,
  intro hP,
  intro hQ,
  apply hh,
  split,
  exact hP,
  exact hQ,
end



