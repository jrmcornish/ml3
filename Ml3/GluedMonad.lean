import Ml3.Closed
import Ml3.Open

#check Open

axiom fracture : False

def MonadMorphism (T1 : Type → Type) [Monad T1] (T2 : Type → Type) [Monad T2] :=
  (A : Type) → (T1 A) → T2 A

def GluedMonad
  {S : Type → Type} [Monad M]
  {T : Type → Type} [Monad N]
  (m : MonadMorphism M N)
  (A : Type) : Type := sorry

def GluedSymSig (A : Type) : Type := GluedMonad monad_morph A
#check GluedSymSig

instance : Monad GluedSymSig where
  pure := sorry
  bind := sorry
