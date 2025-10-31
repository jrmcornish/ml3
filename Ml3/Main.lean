import Mathlib.Data.NNReal.Basic

import Ml3.Open
import Ml3.Closed

open Ml3.OpenModality
open Ml3.ClosedModality

structure Iso (α β : Sort u) : Type u where
  (f : α → β)
  (g : β → α)
  (left: ∀ x, g (f x) = x)
  (right: ∀ y, f (g y) = y)

-- This is not the elementary definition of monad morphism T1 => T2 defined on
-- the same category. Instead it uses a more general notion defined when T1 and
-- T2 are monads on different categories C1 and C2 (see Definition 3.1 of
-- https://ncatlab.org/nlab/show/monad#BicategoryOfMonads).
--
-- Specifically, given T1 : Monad C1 and T2 : Monad C2, the data of a monad
-- morphism T1 => T2 consists of:
--   * A functor F : C1 -> C2
--   * A natural transformation T2 ∘ F  => F ∘ T1
--   * A proof that the monad laws hold
--
-- In our case, we take C1 = OpenU, C2 = CloseU, and F = ClosedFactor ∘ fst
-- (where here fst is just the inclusion of OpenU into Sort u).
def MonadMorphism (T1 : CloseU → CloseU) [ClosedMonad T1] (T2 : OpenU → OpenU) [OpenMonad T2] :=
  (A : OpenU) → (T1 (ClosedFactor A.fst)).fst → (ClosedFactor (T2 A).fst).fst

-- Problem: How can we do (mFunctorAction M g)
def GluedMonad
  {M : CloseU → CloseU} [ClosedMonad M]
  {N : OpenU → OpenU} [OpenMonad N]
  (m : MonadMorphism M N)
  (A : Type u) : Type u :=
    let ⟨X, Y, g⟩ := fracture.f A
    sorry
    -- fracture.g (M X.fst, N Y.fst, fun x => m ((mFunctorAction M g) x))
-- ----

-- def MonadMorphism (T1 T2 : Type u → Type u) := (A : OpenU) → T1 (Closed A.fst) → Closed (T2 A.fst)

-- def mFunctorAction {A B} (M : Type u → Type u) [Monad M] (f : A → B) : M A → M B := fun m => do
--   let x <- m
--   return (f x)


-- def ClosedMonad (M : Type u → Type u) [Monad M] := ∀ A : CloseU, Iso (Closed (M A.fst)) (M A.fst)
-- def OpenMonad (M : Type u → Type u) [Monad M] := ∀ A : OpenU, Iso (Open (M A.fst)) (M A.fst)

-- -- def GluedMonad {M : Type u → Type u} {N : Type u → Type u} [Monad M] [Monad N] (p : OpenMonad N) (m: MonadMorphism M N) (A : Type u) : Type u :=
-- --   let ⟨X, Y, g⟩ := fracture.f A
-- --   let ⟨toIsoM, fromIsoM, _, _⟩ := p Y
-- --   fracture.g (M X.fst, N Y.fst, fun x => m ((mFunctorAction M g) x))

-- -- Problem: How can we do (mFunctorAction M g)
-- def GluedMonad {M : Type u → Type u} {N : Type u → Type u} [Monad M] [Monad N] (p : OpenMonad N) (m: MonadMorphism M N) (A : Type u) : Type u := sorry

-------

variable (X Y G : Type)

-- Signature

inductive SymSig (A : Type) : Type where
| ret : A → SymSig A
| α : G → X → (X → SymSig A) → SymSig A
| β : G → Y → (Y → SymSig A) → SymSig A
| inv : G → (G → SymSig A) → SymSig A
| f : X → (Y → SymSig A) → SymSig A
| γ : X → (G → SymSig A) → SymSig A

namespace SymSig

def SymBind {A B : Type} (x : SymSig X Y G A) (h : A → SymSig X  Y G B) : SymSig X Y G B :=
  match x with
  | ret a => h a
  | α g x k => α g x (fun x' => SymBind (k x') h)
  | β g y k => β g y (fun y' => SymBind (k y') h)
  | inv g k => inv g (fun g' => SymBind (k g') h)
  | f x k => f x (fun y => SymBind (k y) h)
  | γ x k => γ x (fun g' => SymBind (k g') h)

instance : Monad (SymSig X Y G) where
  pure := ret
  bind := SymBind X Y G

-- Generic effects
def α_op (g : G) (x : X) : SymSig X Y G X := α g x (fun x' => ret x')
def β_op (g : G) (y : Y) : SymSig X Y G Y := β g y (fun y' => ret y')
def inv_op (g : G) : SymSig X Y G G := inv g (fun g' => ret g')
def f_op (x : X) : SymSig X Y G Y := f x (fun y => ret y)
def γ_op (x : X) : SymSig X Y G G := γ x (fun g' => ret g')

--- Math monad

def IdentityMonad (A : Type) : Type := A

instance : Monad IdentityMonad where
  pure := fun x => x
  bind := fun m f => f m

--- monad morphisms

def monad_morph : MonadMorphism SymSig IdentityMonad := fun A m =>
  match m with
  | ret a => a
  | α g x k => k x
  | β g y k => k y
  | inv g k => k g
  | f x k => k (0 : Y)  -- placeholder
  | γ x k => k (0 : G)  -- placeholder


--- use fracture axiom to glue monads

def GluedSymSig (A : Type) : Type := GluedMonad monad_morph A
#check GluedSymSig

instance : Monad GluedSymSig where
  pure := sorry
  bind := sorry

def model (x : X) : SymSig X Y G Y :=
  do
    let g <- γ_op X Y G x
    let g' <- inv_op X Y G g
    let x' <- α_op X Y G g' x
    let y <- f_op X Y G x'

    let y' <- β_op X Y G g y
    return y'

end SymSig


--------

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

-----

inductive MDP (A : Type) : Type where
| ret : A → MDP A
| flip : (Bool -> MDP A) → MDP A
| charge : ℝ≥0 -> MDP A → MDP A

open MDP

noncomputable def flipKont : Unit → K Bool := fun () k => 1/2 * (k True + k False)

noncomputable def denSem α : MDP α → K α := fun x =>
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


----
