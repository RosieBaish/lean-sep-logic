import FirstOrderLeaning

open Classical

inductive Asrt where
  | literal : Bool → Asrt
  | emp : Asrt
  | singleton : Nat → Nat → Asrt
  | sep : Asrt → Asrt → Asrt
  | sepimp : Asrt → Asrt → Asrt
open Asrt

def Partial (A B : Type): Type := A → Option B

def Store : Type := Partial Nat Nat
def Heap : Type := Partial Nat Nat

def Subset (A : Type) : Type := A → Prop

def empty_set {A : Type} : Subset A :=
λ x => false

def set_intersect {A : Type} (s1 s2 : Subset A) : Subset A :=
λ x => (s1 x) ∨ (s2 x)

@[simp] def equal {A : Type} (s1 s2 : Subset A) : Prop :=
  ∀ x , s1 x ↔ s2 x

@[simp] def dom {A B : Type}  (p : Partial A B) : Subset A := λ a => match (p a) with
| some _  => true
| none    => false

@[simp]
noncomputable def partial_singleton {A B : Type} (a : Option A) (b : Option B) : Partial A B :=
  λ x => (Option.bind a (λ a1 => if x = a1 then b else none))

def disjoint {A B : Type} (p1 p2 : Partial A B) : Prop :=
set_intersect (dom p1) (dom p2) = empty_set

def union {A B : Type} (p1 p2 : Partial A B) : Partial A B :=
λ x => (p1 x) <|> (p2 x)

@[simp]
def in_partial {A B : Type} (a : A) (p : Partial A B) : Prop :=
  match p a with
  | some _ => true
  | none   => false

@[simp]
def asrt (q : Asrt) (s : Store) (h : Heap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) ∧ partial_singleton (s v1) (s v2) = h
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

@[simp]
def domain_exact_impl (q : Asrt) : Prop := match q with
  | literal b     => False
  | emp           => True
  | singleton _ _ => True
  | sep q1 q2     => (domain_exact_impl q1) ∧ (domain_exact_impl q2)
  | sepimp q1 q2  => (domain_exact_impl q1) ∧ (domain_exact_impl q2)

@[simp]
def domain_exact_theory (q : Asrt) : Prop := ((∃ s1 h1 , (asrt q s1 h1)) ∧ (∀ s h h' , (asrt q s h) ∧ (asrt q s h') → equal (dom h) (dom h')))

theorem domain_exact_correct_literal: ∀ b , (domain_exact_impl (literal b)) ↔ (domain_exact_theory (literal b)) := by {
  simp;
  intro b;
  have s  : Store := (λ (n : Nat) => none);
  have h  : Heap := (λ (n : Nat) => none);
  have h' : Heap := (λ (n : Nat) => some n);
  match b with
  | true => {
    intro hyp;
    have domains := hyp.right s (λ (n : Nat) => none) (λ (n : Nat) => some n) rfl;
    have iffy := domains 0;
    have contra := iffy.mpr;
    apply contra;
    simp;
  }
  | false => {
    intro hyp;
    have ⟨ _, ⟨ _ , con ⟩⟩ := hyp.left;
    contradiction;
  }
}

theorem domain_exact_correct_emp : (domain_exact_impl emp) ↔ (domain_exact_theory emp) := by {
  simp;
  apply And.intro;
  case left => {
    exists (λ (n : Nat) => none);
    exists (λ (n : Nat) => none);
    simp;
  }
  case right => {
    intro s h h';
    intro ⟨ l , r ⟩;
    intro x;
    rw [(l x)];
    rw [(r x)];
    simp;
  }
}

theorem domain_exact_correct_singleton v1 v2 : (domain_exact_impl (singleton v1 v2)) ↔ (domain_exact_theory (singleton v1 v2)) := by {
  simp;
  apply And.intro;
  case left => {
    exists (λ (n : Nat) => some n);
    exists (λ (n : Nat) => if n = v1 then some v2 else none);
    simp;
    simp [Option.bind];
    sorry;
  }
  case right => {
    simp [Option.bind];
    intro s h h';
    intro ⟨ ⟨ l, ⟨ a , ⟨ c , d ⟩ ⟩ ⟩ , ⟨ r , _ ⟩ ⟩;
    intro x;
    apply Iff.intro;
    case mp  => {
      sorry;
    }
    case mpr => {
      sorry;
    }
  }
}


theorem domain_exact_correct : ∀ q , (domain_exact_impl q) ↔ (domain_exact_theory q) := by
  intro q;
  match q with
  | literal b     => exact (domain_exact_correct_literal b);
  | emp           => exact (domain_exact_correct_emp);
  | singleton _ _ => sorry;
  | sep q1 q2     => sorry;
  | sepimp q1 q2  => sorry;
}
