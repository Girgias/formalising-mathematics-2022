/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro PQ,
  rw PQ,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro hPQ,
  rw hPQ,
  intro hQP,
  rw hQP,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro PQ,
  intro QR,
  rw PQ,
  exact QR,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  intro paq,
  cases paq with hp hq,
  split,
  exact hq,
  exact hp,
  intro qap,
  cases qap with hq hp,
  split,
  exact hp,
  exact hq,
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intro PQR,
  cases PQR with PQ R,
  cases PQ with P Q,
  split,
  exact P,
  split,
  exact Q,
  exact R,
  intro PQR,
  cases PQR with P QR,
  cases QR with Q R,
  split,
  split,
  exact P,
  exact Q,
  exact R,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro hP,
  split,
  exact hP,
  triv,
  intro hPt,
  cases hPt with hP,
  exact hP,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro hf,
  exfalso,
  exact hf,
  intro hPf,
  cases hPf with _ hf,
  exact hf,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro pq,
  intro rs,
  split,
  intro PaR,
  cases PaR with hP hR,
  split,
  cases pq with hPQ hQP,
  apply hPQ,
  exact hP,
  cases rs with hRS hSR,
  apply hRS,
  exact hR,
  intro QS,
  cases QS with hQ hS,
  split,
  cases pq with hPQ hQP,
  apply hQP,
  exact hQ,
  cases rs with hRS hSR,
  apply hSR,
  exact hS,
end

example : ¬ (P ↔ ¬ P) :=
begin
  by_contra,
  cases h with hPnP hnPP,
  apply hPnP,
  by_contra hnp,
  apply hPnP,
  apply hnPP,
  exact hnp,
  apply hnPP,
  exact hnp,
  by_contra hnP,
  apply hPnP,
  apply hnPP,
  exact hnP,
  apply hnPP,
  exact hnP,
end
