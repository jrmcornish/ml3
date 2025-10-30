import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Tauto
import Mathlib.Data.Quot

-- Equivalence relation stuff

inductive transitiveClosure {α : Sort u} (r : α → α → Prop) : α → α → Prop :=
| base x y : r x y → transitiveClosure r x y
| step x y z : transitiveClosure r x y → transitiveClosure r y z → transitiveClosure r x z

lemma transitiveClosureSymmIsSymm {α : Sort u}: forall (r : α → α → Prop),
Std.Symm r → Std.Symm (transitiveClosure r) := by
  intros r p
  constructor
  intros a b h
  induction h with
  |base w z q => apply transitiveClosure.base; apply p.symm; assumption
  |step x y z h1 h2 IH1 IH2 => apply (transitiveClosure.step z y x); tauto; tauto

lemma transitiveClosureReflIsRefl {α : Sort u}: forall (r : α → α → Prop),
Std.Refl r → Std.Refl (transitiveClosure r) := by
  intros r h
  constructor
  intro a
  apply transitiveClosure.base
  apply h.refl

lemma transitiveClosureIsTrans {α : Sort u}: forall (r : α → α → Prop),
forall x y z, (transitiveClosure r) x y → (transitiveClosure r) y z →
(transitiveClosure r) x z:= by
  intros r x y z h1 h2
  apply transitiveClosure.step
  tauto
  tauto

axiom p : Prop

def relation {α : Sort u} : (PSum α p) → (PSum α p) → Prop :=  fun x y =>
  match x, y with
  | PSum.inl x1, PSum.inl x2 => x1 = x2
  | _, _ => True

lemma relationIsSymm {α : Sort u}: ∀ {x y : PSum α p}, relation x y → relation y x :=
  by
  intros x y h
  match x, y with
    | PSum.inl v, PSum.inl v' => unfold relation at h; simp at h; rw [h]; tauto
    | PSum.inl v, PSum.inr π => tauto
    | PSum.inr π, PSum.inl v => tauto
    | PSum.inr π, PSum.inr π' => tauto

@[simp] instance ClosedSetoid (α : Sort u) : Setoid (PSum α p) where
  r := transitiveClosure relation
  iseqv := by
    constructor
    · intro x
      apply transitiveClosure.base
      unfold relation
      cases x <;> (simp)
    · intro x y h
      induction h with
      | base w z q =>
        apply transitiveClosure.base
        apply relationIsSymm; assumption
      | step a b c h1 h2 IH1 IH2 =>
        apply transitiveClosure.step
        apply IH2
        apply IH1
    · intros x y z h
      apply transitiveClosureIsTrans; assumption

-- Monad structure

@[simp] def ClosedModality (α : Type u) := Quotient (ClosedSetoid α)

#check ClosedModality

lemma closedCrush (α : Type u) : ∀ x y : ClosedModality α, p → x = y := by
  intros x y π
  obtain ⟨a, eq1⟩ := Quot.exists_rep x
  obtain ⟨b, eq2⟩ := Quot.exists_rep y
  rw [← eq1]
  rw [← eq2]
  apply Quot.sound
  simp
  apply (transitiveClosure.step a (PSum.inr π) b) <;> apply transitiveClosure.base
  · cases a <;> unfold  relation <;> simp
  · unfold relation; simp

def unit {α : Type u} : α → ClosedModality α :=
  fun a => Quotient.mk (ClosedSetoid α) (PSum.inl a)

def KleisliLiftAux {α β : Type u} (f : α → ClosedModality β) : α ⊕' p → ClosedModality β :=
fun x => match x with
         | PSum.inl v => f v
         | PSum.inr π => Quotient.mk (ClosedSetoid β) (PSum.inr π)

lemma aux' {α : Type u} : forall x x' : α ⊕' p, transitiveClosure relation x x' →
(relation x x') ∨ p := by
  intros x x' h
  induction h with
  | base a b π => tauto
  | step x'' y z a1 a2 IH1 IH2 =>
    match IH1, IH2 with
    | Or.inr h1, _ => tauto
    | _, Or.inr h1 => tauto
    | Or.inl h1, Or.inl h2 =>
    cases y with
    | inr π => tauto
    | inl v =>
      match x'', z with
      | PSum.inl v1, PSum.inl v2 => unfold relation at h1 h2; simp_all
      | PSum.inr _, _ | _, PSum.inr _ => tauto

lemma aux {α : Type u} : forall v v' : α,
transitiveClosure relation (PSum.inl v) (PSum.inl v') → (v = v') ∨ p := by
intros v v' h
cases (aux' (PSum.inl v) (PSum.inl v') h) with
| inl h' => unfold relation at h'; tauto
| inr _ => tauto

lemma KleisliLiftAuxLemma {α β : Type u} (f : α → ClosedModality β) : ∀ (a b : α ⊕' p),
a ≈ b → KleisliLiftAux f a = KleisliLiftAux f b := by
  intros a b h
  match a, b with
    | PSum.inl v, PSum.inl v' =>
      have h1 : v = v' ∨ p := by apply aux; tauto
      cases h1 with
      | inl eq => rw [eq]
      | inr π => apply closedCrush; assumption
    | PSum.inl v, PSum.inr π | PSum.inr π, PSum.inl v' | PSum.inr π, PSum.inr π'
      => apply closedCrush; assumption

def KleisliLift {α β : Type u} (f : α → ClosedModality β) : ClosedModality α → ClosedModality β :=
  Quotient.lift (KleisliLiftAux f) (KleisliLiftAuxLemma f)

-- Monad laws + idempotency

lemma unitLaw1 {A B} : ∀ (f : A → ClosedModality B) (x : A), (KleisliLift f) (unit x) = f x := by
  intros f x; rfl

lemma unitLaw2 {A} : ∀ (x : ClosedModality A), (KleisliLift unit) x = x := by
  intro x
  obtain ⟨v, eq⟩ := Quotient.exists_rep x
  cases v
  case inl v =>
    subst eq
    tauto
  case inr π =>
    apply closedCrush; assumption

lemma bindLaw {A B C} : ∀ (f : A → ClosedModality B) (g : B → ClosedModality C),
(KleisliLift g) ∘ (KleisliLift f) = KleisliLift (KleisliLift g ∘ f) := by
  intros f g
  apply funext
  intros x
  obtain ⟨v, eq⟩ := Quot.exists_rep x
  cases v
  case inr π =>
    apply closedCrush; assumption
  case inl v =>
    subst eq; tauto

def closedBind {A : Type u} : ClosedModality (ClosedModality A) → ClosedModality A := KleisliLift (fun x => x)

lemma relativeClosedIdempotent {A B : Type u} : ∀ (f : ClosedModality A → ClosedModality B), (KleisliLift (f ∘ unit)) = f := by
intro f
apply funext; intro x
obtain ⟨v, eq⟩ := Quot.exists_rep x
cases v
case inr π => apply closedCrush; assumption
case inl v => subst eq; tauto

lemma closedIdempotent {A} : ∀ x : ClosedModality (ClosedModality A), ((unit) ∘ (closedBind)) x = x := by
  intro x
  simp
  obtain ⟨v, eq⟩ := Quotient.exists_rep x
  subst eq
  unfold closedBind
  unfold KleisliLift
  simp
  cases v
  case inr π => apply closedCrush; assumption
  case inl v =>
    obtain ⟨v', eq⟩ := Quotient.exists_rep v
    cases v'
    case inr π  => apply closedCrush; assumption
    case inl v1 => tauto

-- Propositional closed modality

def closedProp (q : Prop) : Prop := q ∨ p

def unitClosedProp (q : Prop) : q → closedProp q := fun π => Or.inl π

def liftClosedProp (q1 q2 : Prop) : (q1 → closedProp q2) → (closedProp q1 → closedProp q2) :=
fun f π => match π with
              |Or.inl x => f x
              |Or.inr x => Or.inr x

lemma idempotencyClosedProp : ∀ (q : Prop), closedProp (closedProp q) ↔ (closedProp q) := by
  intro q
  constructor <;> intro x <;> cases x <;> tauto
