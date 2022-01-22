/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hP,
  left,
  exact hP,
end

example : Q → P ∨ Q :=
begin
  intro hQ,
  right,
  exact hQ,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro hPoQ,
  intro hPR,
  intro hQR,
  cases hPoQ with hP hQ,
  apply hPR,
  exact hP,
  apply hQR,
  exact hQ,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ,
  right,
  exact hP,
  left,
  exact hQ,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  intros h,
  cases h with hPQ hR,
  cases hPQ with hP hQ,
  left,
  exact hP,
  right,
  left,
  exact hQ,
  right,
  right,
  exact hR,
  intros h,
  cases h with hP hQR,
  left,left,
  exact hP,
  cases hQR with hQ hR,
  left,right,exact hQ,
  right, exact hR,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros PR QS PoQ,
  cases PoQ with hP hQ,
  left,
  apply PR,
  exact hP,
  right,
  apply QS,
  exact hQ,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros hPQ PoR,
  cases PoR with hP hR,
  left, apply hPQ, exact hP,
  right, exact hR,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros PeR QeS,
  split,
  intro PoQ,
  cases PoQ with hP hQ,
  left,
  cases PeR with PR _,
  apply PR, exact hP,
  right,
  cases QeS with QS _,
  apply QS, exact hQ,
  intro RoS,
  cases RoS with hR hS,
  left,
  cases PeR with _ RP,
  apply RP, exact hR,
  right,
  cases QeS with _ SQ,
  apply SQ, exact hS,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  intro nPoQ,
  split,
  by_contra hP,
  apply nPoQ,
  left, exact hP,
  by_contra hQ,
  apply nPoQ,
  right, exact hQ,
  intro nPanQ,
  cases nPanQ with nP nQ,
  by_contra PoQ,
  cases PoQ with hP hQ,
  apply nP, exact hP,
  apply nQ, exact hQ,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  intro nPaQ,
  by_contra nn,
  apply nPaQ,
  split,
  exfalso,
  apply nn,
  left,
  by_contra hP,
  apply nn,
  right,
  by_contra hQ,
  apply nPaQ,
  split,
  exact hP, exact hQ,
  exfalso,
  apply nn,
  left,
  by_contra hP,
  apply nn,
  right,
  by_contra hQ,
  apply nPaQ,
  split,
  exact hP, exact hQ,
-- ← direction
  intro nPonQ,
  cases nPonQ with nP nQ,
  by_contra PaQ,
  apply nP,
  cases PaQ with hP _,
  exact hP,
  by_contra PaQ,
  apply nQ,
  cases PaQ with _ hQ,
  exact hQ,
end
