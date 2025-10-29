axiom p : Prop

def Open (τ : Sort u) : Sort u := p → τ

def OpenUnit {τ : Sort u} (t : τ) : Open τ :=
  fun _ => t

def OpenBind {τ τ' : Sort u} (f : τ → Open τ') (t : Open τ) : Open τ' :=
  fun ph => f (t ph) ph

def OpenFunctor {τ τ' : Sort u} (f : τ → τ') (t : Open τ) : Open τ' :=
  OpenBind (fun t' => OpenUnit (f t')) t

def OpenMultiplication {τ : Sort u} (t : Open (Open τ)) : Open τ :=
  OpenBind (fun t : Open τ => t) t

theorem OpenRightUnitLaw {τ : Sort u} : ∀ t : Open τ, OpenMultiplication (OpenUnit t) = t := by
  intro t
  unfold OpenMultiplication OpenUnit OpenBind
  simp

def IsIso {α β : Sort u} (f : α → β) : Prop :=
  ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

theorem OpenIdempotent {τ : Sort u} : IsIso (OpenFunctor (OpenUnit (τ := τ))) := by
  refine ⟨OpenMultiplication (τ := τ), ?p⟩
  constructor
  . intro x
    apply OpenRightUnitLaw
  . intro y
    unfold OpenFunctor OpenUnit OpenMultiplication OpenBind
    simp




inductive ClosedUnquotiented (τ : Sort u) where
  | inl : p → ClosedUnquotiented τ
  | inr : τ → ClosedUnquotiented τ

namespace ClosedUnquotiented

def Relation {τ : Sort u} (x y : ClosedUnquotiented τ) : Prop :=
  match x, y with
  | inr t1, inr t2 => t1 = t2
  | _, _ => True

-- TODO: understand this better
inductive TransitiveClosure {α : Sort u} (r : α → α → Prop) : α → α → Prop where
| base x y  : r x y → TransitiveClosure r x y
| step x y z : TransitiveClosure r x y →  r y z → TransitiveClosure r x z


open TransitiveClosure

def ClosedSetoid (τ : Sort u) : Setoid (ClosedUnquotiented τ) where
  r := TransitiveClosure Relation
  iseqv := by sorry


def MyQuotient (τ : Sort u) : Sort u :=
  Quotient (ClosedSetoid τ)


end ClosedUnquotiented

def Closed (τ : Sort u) : Sort u := sorry --Quotient.{u}
