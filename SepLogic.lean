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
def SubHeap : Type := Partial Nat Nat
def Heap : Type := Nat → Nat

def Subset (A : Type) : Type := A → Prop

def empty_set {A : Type} : Subset A :=
λ x => false

def set_intersect {A : Type} (s1 s2 : Subset A) : Subset A :=
λ x => (s1 x) ∨ (s2 x)

def set_disjoint {A : Type} (s1 s2 : Subset A) : Prop :=
∀ x , ¬((s1 x) ∧ (s2 x))

def set_subset {A : Type} (s1 s2 : Subset A) : Prop :=
∀ x , (s1 x) → (s2 x)

-- s1 / s2
def set_difference {A : Type} (s1 s2 : Subset A) : Subset A :=
λ x => (s1 x) ∧ ¬(s2 x)

@[simp] def equal {A : Type} (s1 s2 : Subset A) : Prop :=
  ∀ x , s1 x ↔ s2 x

@[simp] def dom {A B : Type}  (p : Partial A B) : Subset A := λ a => (p a).isSome

def disjoint {A B : Type} (p1 p2 : Partial A B) : Prop :=
set_intersect (dom p1) (dom p2) = empty_set

def partial_of {A B : Type} (p : Partial A B) (t : A → B) : Prop :=
  ∀ x , match p x with
  | some y => (y = t x)
  | none   => True

noncomputable def union {A : Type} (p1 p2 : Partial A A) : Partial A A :=
λ x => if (p1 x) = none then (p2 x) else (p1 x)

@[simp]
def in_partial {A B : Type} (a : A) (p : Partial A B) : Prop := (p a).isSome

def asrt (q : Asrt) (s : Store) (h : SubHeap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) ∧ ∀ x , (dom h) x = (some x = (s v1))
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

@[simp]
def check (q : Asrt) (s : Store) (h : Heap) : (Prop × Subset Nat) := match q with
  | literal b => (b , empty_set)
  | emp       => (True, empty_set)
  | singleton v1 v2 => ((Option.map h (s v1)) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) , λ x => (some x = (s v1)))
  | sep q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q1 s h); (b1 ∧ b2 ∧ (set_disjoint m1 m2) , (set_intersect m1 m2))
  | sepimp q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q1 s h); (b1 → b2 ∧ set_subset m1 m2 , set_difference m2 m1)

--  | literal b => b
theorem equivalence_literal (s : Store) (h_tilde : Heap) (lit : Bool) : let ⟨ b , m ⟩ := (check (literal lit) s h_tilde); if b then (asrt (literal lit) s (λ x => some (h_tilde x))) ∨ (∀ h : SubHeap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt (literal lit) s h))) else ∀ h , ¬(asrt (literal lit) s h) := by {
  simp;
  cases Classical.em (lit = true) with
  | inl a => {
    rw[if_pos];
    simp[a, asrt];
    exact a;
  }
  | inr a => {
    rw[if_neg];
    simp[a, asrt];
    exact a;
  }
}

--  | emp       => ∀ x , (dom h) x = false
theorem equivalence_emp (s : Store) (h_tilde : Heap) (lit : Bool) : let ⟨ b , m ⟩ := (check emp s h_tilde); if b then (asrt emp s (λ x => some (h_tilde x))) ∨ (∀ h : SubHeap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt emp s h))) else ∀ h , ¬(asrt emp s h) := by {
  simp [asrt];
  apply Or.inr;
  intro h _;
  apply Iff.intro;
  case mp  => {
    simp[empty_set];
    intro h_def;
    intro a;
    rw[congrFun h_def a];
  }
  case mpr => {
    intro a;
    simp[empty_set];
    simp[a];
  }
}
--  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) ∧ ∀ x , (dom h) x = (some x = (s v1))
theorem equivalence_singleton (s : Store) (h_tilde : Heap) (lit : Bool) : let ⟨ b , m ⟩ := (check (singleton v1 v2) s h_tilde); if b then (asrt (singleton v1 v2) s (λ x => some (h_tilde x))) ∨ (∀ h : SubHeap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt (singleton v1 v2) s h))) else ∀ h , (partial_of h h_tilde) → ¬(asrt (singleton v1 v2) s h) := by {
  simp;
  split;
  case inl temp => {
    have ⟨ points , is_some_v1 , is_some_v2 ⟩ := temp;
    rw[is_some] at is_some_v1;
    have ⟨ s_v1 , some_v1 ⟩ := is_some_v1;
    rw[is_some] at is_some_v2;
    have ⟨ s_v2 , some_v2 ⟩ := is_some_v2;
    apply Or.inr;
    intro h partiality;
    apply Iff.intro;
    case mp  => {
      intro h_def;
      have h_def1 := congrFun h_def;
      apply And.intro;
      case left => {
        simp[partial_of] at partiality
        --rw[Eq.symm points];
        simp[Option.bind];
        rw[some_v1] at h_def1;
        simp at h_def1;
        have h_def2 := h_def1 s_v1;
        rw[is_some] at h_def2;
        simp at h_def2;
        have ⟨ hsv_1, a ⟩ := of_eq_true h_def2;

        revert points;
        simp[Option.map, Option.bind];
        rw[some_v1];
        rw[some_v2];
        simp;
        have part1 := partiality s_v1;
        simp[a] at part1;
        rw[(Eq.symm part1)];
        intro;
        simp[a];
        assumption;
      }
      case right => {
        simp[in_partial];
        apply And.intro;
        case left => rw[is_some]; exact is_some_v1;
        case right => {
          apply And.intro;
          case left => rw[is_some]; exact is_some_v2;
          case right => exact h_def1;
        }
      }
    }
    case mpr => {
      simp[asrt];
      intro ⟨ points, is_some_v1, is_some_v2, same_domain ⟩;
      apply funext;
      exact same_domain;
    }
  }
  case inr not_check => {
    intro h;
    simp[partial_of];
    intro partiality;
    revert not_check;
    rw [← pp_imp_nn];
    simp[asrt];
    rw[is_some];
    rw[is_some];
    intro ⟨ points, ⟨ sv1 , sv1_proof ⟩ , ⟨ sv2 , sv2_proof ⟩ , d ⟩;
    apply And.intro;
    case left  => {
      simp[Option.map, Option.bind, sv1_proof];
      have part1 := partiality sv1;
      simp [sv1_proof] at part1;
      simp [sv2_proof];
      simp [sv1_proof, sv2_proof, Option.bind] at points;
      rw[points] at part1;
      simp at part1;
      rw[part1];
    }
    case right => apply And.intro (Exists.intro sv1 sv1_proof )  (Exists.intro sv2 sv2_proof);
  }
}
--  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
--  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')




theorem equivalence (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check q s h_tilde); if b then (asrt q s (λ x => some (h_tilde x))) ∨ (∀ h : SubHeap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt q s h))) else ∀ h , ¬(asrt q s h) := by {
  match q with
  | literal lit => simp[equivalence_literal];
  | emp => sorry;
  | singleton v1 v2 => sorry;
  | sep q1 q2 => sorry;
  | sepimp q1 q2 => sorry;
}
