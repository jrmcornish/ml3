import Ml3.Closed
import Ml3.Open

open Ml3.OpenModality
open Ml3.ClosedModality

-- axiom fracture : Iso (Sort u) (Σ' (A : CloseU.{u}) (B : OpenU.{u}), A.fst → (Closed B.fst))
axiom fracture : False

def MonadMorphism (T1 : Type → Type) [Monad T1] (T2 : Type → Type) [Monad T2] :=
  (A : Type) → (T1 A) → T2 A

def GluedMonad
  {S : Type → Type} [Monad M]
  {T : Type → Type} [Monad N]
  (m : MonadMorphism M N)
  (A : Type) : Type := sorry
