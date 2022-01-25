/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tendsto` from a previous sheet

-- you can maybe do this one now
theorem tendsto_neg {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  rw tendsto_def,
  intros ε ε_pos,

  rw tendsto_def at ha,
  specialize ha ε ε_pos,
  cases ha with B h,
  use B,

  intros n b_leq_n,
  specialize h n b_leq_n,
  have m : -(a n - t) = -a n - -t,
  norm_num,
  rw ← m,
  rw abs_neg,
  exact h,
end

/-
`tendsto_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful. 
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsto_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  rw tendsto_def,
  intros ε ε_pos,

  rw tendsto_def at ha,
  specialize ha ε ε_pos,
  cases ha with B h,
  use B,

  rw tendsto_def at hb,
  specialize hb ε ε_pos,
  cases hb with B h,

  intros n b_leq_n,
  -- triangle inequality not available
  --norm_add_le
  sorry
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n - b n) (t - u) :=
begin
  -- this one follows without too much trouble from earlier results.
  sorry
end

