import Ml3.Postulates

section OpenModality
variable (p : Prop)

def Open (τ : Sort u) : Sort u := p → τ

def OpenUnit {τ : Sort u} (t : τ) : Open p τ :=
  fun _ => t

def OpenBind {τ τ' : Sort u} (f : τ → Open p τ') (t : Open p τ) : Open p τ' :=
  fun ph => f (t ph) ph

def OpenFunctor {τ τ' : Sort u} (f : τ → τ') (t : Open p τ) : Open p τ' :=
  OpenBind p (fun t' => OpenUnit p (f t')) t

def OpenMultiplication {τ : Sort u} (t : Open p (Open p τ)) : Open p τ :=
  OpenBind p (fun t : Open p τ => t) t

theorem OpenRightUnitLaw {τ : Sort u} : ∀ t : Open p τ, OpenMultiplication p (OpenUnit p t) = t := by
  intro t
  unfold OpenMultiplication OpenUnit OpenBind
  -- We should be careful about simp here: we want to make sure this doesn't use
  -- classical reasoning. If we do enable classical reasoning, then Lean becomes
  -- Boolean (i.e. there are only two propositions, True and False), and hence
  -- is uninteresting for our open and closed modalities. (In particular, p
  -- above will either be True or False, and hence there will be only two
  -- possible ways of defining Open, both of which will be uninteresting: one is
  -- the constant unit monad (corresponding to p = false), and the other is the
  -- identity monad (corresponding to p = true).)
  -- In other words, if we allow classical reasoning, then the models of our
  -- type theory are really boring. We can model either Set^1 (i.e. just Set) by
  -- taking p = True, and Set^0 (i.e. the terminal category) by taking p =
  -- False. We want more than this! So we must avoid classical reasoning in our
  -- proofs.
  simp

def IsIso {α β : Sort u} (f : α → β) : Prop :=
  ∃ g : β → α, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

theorem OpenIdempotent {τ : Sort u} : IsIso (OpenFunctor p (OpenUnit p (τ := τ))) := by
  refine ⟨OpenMultiplication p (τ := τ), ?p⟩
  constructor
  . intro x
    apply OpenRightUnitLaw
  . intro y
    unfold OpenFunctor OpenUnit OpenMultiplication OpenBind
    simp
end OpenModality
