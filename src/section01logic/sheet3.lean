/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ P → (P → false) :=
begin
  intro nP,
  intro hP,
  apply nP,
  exact hP,
end

example : ¬ true → false :=
begin
  intro hnt,
  apply hnt,
  trivial,
end

example : false → ¬ true :=
begin
  intro hf,
  by_contra,
  exact hf,
end

example : ¬ false → true :=
begin
  intro hnf,
  trivial,
end

example : true → ¬ false :=
begin
  intro ht,
  by_contra hf,
  apply hf,
end

example : false → ¬ P :=
begin
  intro hf,
  exfalso,
  exact hf,
end

example : P → ¬ P → false :=
begin
  intro hP,
  by_contra,
  apply h,
  apply hP,
end

example : P → ¬ (¬ P) :=
begin
  intro hP,
  by_contra;
  apply h,
  exact hP,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hPQ,
  intro hnPQ,
  by_contra hP,
  apply hnPQ,
  apply hPQ,
  exact hP,
end

example : ¬ ¬ false → false :=
begin
  intro hnnf,
  by_contra hnf,
  apply hnnf,
  exact hnf,
end

example : ¬ ¬ P → P :=
begin
  intro hnnP,
  by_contra hnP,
  apply hnnP,
  exact hnP,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro hnQnP,
  intro hP,
  by_contra hnQ,
  apply hnQnP,
  exact hnQ,
  exact hP,
end