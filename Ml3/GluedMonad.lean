import Ml3.Closed
import Ml3.Open
import Ml3.Postulates

-- TODO Align naming across these two files
open Ml3.OpenModality
open Ml3.ClosedModality

-- TODO: Eventually use Type for both of these:
def OpenUniverse1.{u} := Open p1 (Type u)
def ClosedUniverse1.{u} := Closed p1 (Type u)

def OpenInclusion (τ : OpenUniverse1.{u}) : Type u :=
  (pi : p1) → τ pi


@[simp] def ClosedInclusionAux (x : PSum (Type u) p1) : Type u :=
  match x with
  | PSum.inl A => Closed p1 A
  | PSum.inr _ => PUnit.{u + 1} -- TODO: Should this be pi instead?

-- Can prove the two are isomorphic; not sure are about *equal*, so we assume
-- this for now
axiom ClosedInclusionAxiom : ∀ A : Type u, p → (Closed p1 A = PUnit)

def ClosedInclusion (τ : ClosedUniverse1.{u}) : Type u := by
  revert τ
  apply Quotient.lift ClosedInclusionAux
  intro a b p
  match a, b with
    | PSum.inl A, PSum.inl B => cases (aux p1 A B p)
                                case inl eq => rw [eq]
                                case inr π =>
                                apply Eq.trans
                                apply ClosedInclusionAxiom _ π
                                apply Eq.symm
                                apply ClosedInclusionAxiom _ π
    | PSum.inl A, PSum.inr π => apply ClosedInclusionAxiom _ π
    | PSum.inr π, PSum.inl B => apply Eq.symm
                                apply ClosedInclusionAxiom _ π
    | PSum.inr π, PSum.inr π' => rfl

def frac : (Type u) -> (Σ (A : ClosedUniverse1.{u}) (B : OpenUniverse1.{u}), ClosedInclusion A → Closed p1 (OpenInclusion B)) := sorry

def glue : (Σ (A : ClosedUniverse1.{u}) (B : OpenUniverse1.{u}), ClosedInclusion A → Closed p1 (OpenInclusion B)) → (Type u) := sorry

-- axiom fracture : Iso (Sort u) (Σ' (A : CloseU.{u}) (B : OpenU.{u}), A.fst → (Closed B.fst))
axiom fracture : (frac ∘ glue = id) ∧ (glue ∘ frac = id)

class ClosedMonad (T : Type u → Type u) [Monad T] where
  pi : ∀ A : Type u, T (Closed p1 A) = Closed p1 (T A)

class OpenMonad (T : Type u → Type u) [Monad T] where
  pi : ∀ A : Type u, T (Open p1 A) = Open p1 (T A)

def MonadMorphism (T1 : Type u → Type u) [Monad T1] (T2 : Type u → Type u) [Monad T2] :=
  (τ : Type u) → (T1 τ → T2 τ)

def GluedMonad
  {S : Type → Type} [i1 : Monad S]
  {T : Type → Type} [i2 : Monad T]
  (m : MonadMorphism S T)
  (A : Type) : Type :=
    let ⟨X, Y, g⟩ := frac A
    by
    apply glue
    constructor
    constructor
    case fst =>
      apply (unit p1)
      apply S
      apply (ClosedInclusion X)
    case snd.fst =>
      apply OpenUnit
      apply T
      apply (OpenInclusion Y)
    case snd.snd => intro x
                    sorry
