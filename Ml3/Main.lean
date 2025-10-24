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

--------

axiom closed : Sort u → Sort u

def close_universe : Type u := Sort u -> Sort u

def equiv (α β) := exists (f : α → β) (g : β → α), (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)
def equiv' (α β) := exists (f : α → β) (g : β → α), (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

axiom fracture : equiv (Sort u) (Σ' (A : Sort u) (B : Sort u), A → (closed B))

inductive MDP (A : Type) : Type where
| ret : A → MDP A
| flip : (Bool -> MDP A) → MDP A
| charge : ℝ≥0 -> MDP A → MDP A

open MDP

noncomputable def flipKont : Unit → K Bool := fun () k => 1/2 * (k True + k False)

noncomputable def denSem {α} : MDP α → K α := fun x =>
match x with
 | ret a => return a
 | MDP.flip k => let F1 := denSem (k True)
             let F2 := denSem (k False)
             (fun k' => 1/2 * (F1 k' + F2 k'))
 | charge r x => fun F => r + ((denSem x) F)

inductive InputOutput (A : Type) : Type where
| ret' : A → InputOutput A
| input : (Nat -> InputOutput A) → InputOutput A
| output : Nat -> InputOutput A → InputOutput A

open InputOutput

def KleisliExtension (f : A → InputOutput B) (x : InputOutput A) : InputOutput B :=
  match x with
  | ret' a =>  f a
  | input k => input (fun (n : Nat) => KleisliExtension f (k n))
  | output n k => output n (KleisliExtension f k)


lemma unitLaw {A} : (fun x : InputOutput A => KleisliExtension ret' x) = (fun x : InputOutput A => x) :=
  by
  apply funext
  intros x
  induction x with
  | ret' a => rfl
  | input k ih => unfold KleisliExtension; congr; apply funext; exact ih
  | output n x ih => unfold KleisliExtension; congr
-- axiom fracture : equiv Type (Sigma (fun A : Type => Sigma
-- (fun B => A -> (close B))))

def ioProg : InputOutput Unit := input (fun n => if n > 3 then output 3 (ret' ()) else ret' ())


----



def signature := List (Type × Type)
def fromSigToFunctor (σ : signature) : Type -> Type := sorry
