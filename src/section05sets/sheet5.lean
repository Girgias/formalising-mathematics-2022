/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext,
  split,
  intro hA,
  cases hA with hxA hxA,
  exact hxA, exact hxA,
  intro hxA,
  left,exact hxA,
end

example : A ∩ A = A :=
begin
  ext,
  split,
  {
    intro hxA,
    cases hxA with xa xa,
    exact xa,
  }, {
    intro hxa,
    split,
    exact hxa, exact hxa,
  }
end

example : A ∩ ∅ = ∅ :=
begin
  ext,
  split,
  intro hxae,
  cases hxae with hxa he,
  exact he,
  intro he,
  rw inter_empty,
  exact he,
end

example : A ∪ univ = univ :=
begin
  ext,
  split, {
    intro hxaU,
    cases hxaU with hxa hU,
    apply mem_univ,
    exact hU,
  }, {
    intro hxU,
    right,
    exact hxU,
  }
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intros hAB hBA,
  ext,
  split, {
    intro hxA,
    apply hAB,
    exact hxA,
  }, {
    intro hxB,
    apply hBA,
    exact hxB,
  }
end

example : A ∩ B = B ∩ A :=
begin
  ext,
  split, {
    intro hxAB,
    cases hxAB with hxA hxB,
    split,
    exact hxB,
    exact hxA,
  }, {
    intro hxBA,
    cases hxBA with hxB hxA,
    split,
    exact hxA,
    exact hxB,
  }
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext,
  split, {
    intro hxA_BC,
    cases hxA_BC with hxA hxBC,
    cases hxBC with hxB hxC,
    split, split,
    exact hxA,
    exact hxB,
    exact hxC,
  }, {
    intro hxAB_C,
    cases hxAB_C with hxAB hxC,
    cases hxAB with hxA hxB,
    split, exact hxA, split,
    exact hxB, exact hxC,
  }
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext,
  split,
  {
    intro hxA_BC,
    cases hxA_BC with hxA hxBC,
    left, left, exact hxA,
    cases hxBC with hxB hxC,
    left, right, exact hxB,
    right, exact hxC,
  }, {
    intro hxAB_C,
    cases hxAB_C with hAB hC,
    cases hAB with hA hB,
    left, exact hA,
    right, left, exact hB,
    right, right, exact hC,
  }
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  ext,
  split,
  {
    intro hAuBiC,
    split,
    {
      cases hAuBiC with hA hBiC,
      left, exact hA,
      cases hBiC with hB hC,
      right, exact hB,
    }, {
      cases hAuBiC with hA hBiC,
      left, exact hA,
      cases hBiC with hB hC,
      right, exact hC,
    },
  }, {
    intro hAuBiAuC,
    cases hAuBiAuC with hAB hAC,
    cases hAB with hA hB,
    left, exact hA,
    cases hAC with hA hC,
    left, exact hA,
    right, split, exact hB, exact hC,
  }
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  split, {
    intro hAi_BuC,
    cases hAi_BuC with hA hBC,
    cases hBC with hB hC,
    left, split, exact hA, exact hB,
    right, split, exact hA, exact hC,
  }, {
    intro hAiB_AiC,
    cases hAiB_AiC with hAB hAC,
    {
      cases hAB with hA hB,
      split, exact hA, left, exact hB,
    }, {
      cases hAC with hA hC,
      split, exact hA, right, exact hC,
    }
  }
end

