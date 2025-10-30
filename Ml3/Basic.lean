import Mathlib.Data.NNReal.Basic

open scoped NNReal

#check ℝ≥0

def K (T : Type) : Type := (T → ℝ≥0) → ℝ≥0

instance : Monad K where
  pure := fun x f => f x
  bind := fun m f k => m (fun a => f a k)

noncomputable def bernoulli_integral : K ℕ := fun f =>
  (f 0 + f 1) / 2

noncomputable def prog :=
  do
  let x <- bernoulli_integral
  let y <- bernoulli_integral
  return (x + y)

lemma math_works : (prog (fun n => if n = 0 then 1 else 0) = 1/4) :=
  by
  unfold prog
  unfold bernoulli_integral
  unfold bind
  unfold instMonadK
  simp
  ring
