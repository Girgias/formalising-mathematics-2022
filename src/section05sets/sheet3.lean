/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → false` are all equal *by definition*
in Lean. 

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`. 

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `false`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : x ∉ A → (x ∈ A → false) :=
begin
  intro h1,
  intro h2,
  apply h1,
  exact h2,
end

example : x ∈ A → (x ∉ A → false) :=
begin
  intro h1,
  intro h2,
  apply h2,
  exact h1,
end

example : (A ⊆ B) → x ∉ B → x ∉ A :=
begin
  intro hAB,
  change x ∈ Bᶜ → x ∈ Aᶜ,
  have hBcAc : Bᶜ ⊆ Aᶜ,
  simp,
  exact hAB,
  intro hB,
  apply hBcAc,
  exact hB,
end

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : set X):=
begin
  -- explains what ``simp`` does
  squeeze_simp,
  --simp,
end

example : x ∈ Aᶜ → x ∉ A :=
begin
  intro h,
  exact h,
end

example : (∀ x, x ∈ A) ↔ ¬ (∃ x, x ∈ Aᶜ) :=
begin
  split,
  {
    intro hax,
    intro he,
    cases he with X x,
    apply x,
    apply hax,
  },
  {
    intro he,
    simp only [not_exists_not, mem_compl_eq] at he,
    exact he,
  },
end

example : (∃ x, x ∈ A) ↔ ¬ (∀ x, x ∈ Aᶜ) :=
begin
  split,
  {
    intro he,
    rw not_forall,
    simp only [mem_compl_eq, not_not_mem],
    exact he,
  }, {
    intro ha,
    rw not_forall at ha,
    simp only [mem_compl_eq, not_not_mem] at ha,
    exact ha,
  }
end
