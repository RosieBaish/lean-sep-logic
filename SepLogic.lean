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

def Store : Type := Nat → Nat
def Heap : Type := Partial Nat Nat

def Subset (A : Type) : Type := A → Prop

def empty_set {A : Type} : Subset A :=
λ x => false

def set_union {A : Type} (s1 s2 : Subset A) : Subset A :=
λ x => (s1 x) ∨ (s2 x)

def set_intersection {A : Type} (s1 s2 : Subset A) : Subset A :=
λ x => (s1 x) ∧ (s2 x)

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

def empty_partial {A B : Type} : Partial A B := λ x => none

noncomputable def singleton_partial {A B : Type} (a : A) (b : B) : Partial A B := λ x => if (x = a) then some b else none

noncomputable def singleton_partial_some {A B : Type} (a : A) (b : Option B) : Partial A B := match b with
  | some x => singleton_partial a x
  | none => empty_partial

def disjoint {A B : Type} (p1 p2 : Partial A B) : Prop :=
set_intersection (dom p1) (dom p2) = empty_set

@[simp]
def in_partial {A B : Type} (a : A) (p : Partial A B) : Prop := (p a).isSome

def partial_of {A B : Type} (p1 p2 : Partial A B) : Prop :=
  ∀ x , match p1 x with
  | some y => (p2 x) = some y
  | none   => True


@[simp] theorem partial_of_emp {A B : Type} (p : Partial A B) : partial_of empty_partial p := by {
  simp[partial_of, empty_partial];
}

@[simp] theorem partial_of_singleton {A B : Type} (a : A) (b : B) (p : Partial A B) : partial_of (singleton_partial a b) p ↔ (p a = some b) := by {
  simp [partial_of];
  simp [singleton_partial];
  apply Iff.intro;
  case mp  => {
    intro precondition ;
    have p1 := precondition a;
    simp at p1;
    exact p1;
  }
  case mpr => {
    intro pred a1;
    apply Or.elim (Classical.em (a1 = a));
    case left => {
      intro temp;
      simp[temp];
      exact pred;
    }
    case right => {
      intro temp;
      simp[temp];
    }
  }
}

def partial_difference {A : Type} (p1 p2 : Partial A A) : Partial A A :=
λ x => match (p2 x) with
  | some _ => none
  | none => p1 x

noncomputable def union {A : Type} (p1 p2 : Partial A A) : Partial A A :=
λ x => if (p1 x) = none then (p2 x) else (p1 x)

def asrt (q : Asrt) (s : Store) (h : Heap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => h (s v1) = some (s v2) ∧ ∀ x , (dom h) x = (x = (s v1))
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

@[simp]
noncomputable def check (q : Asrt) (s : Store) (h : Heap) : (Prop × Heap) := match q with
  | literal b => (b , empty_partial)
  | emp       => (True, empty_partial)
  | singleton v1 v2 => (h (s v1) = some (s v2) , singleton_partial_some (s v1) (h (s v1)))
  | sep q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q2 s h); (b1 ∧ b2 ∧ (disjoint m1 m2) , (union m1 m2))
  | sepimp q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q1 s h); (b1 → b2 ∧ partial_of m1 m2 , partial_difference m2 m1)

theorem partiality (q : Asrt) (s : Store) (h_tilde : Heap) : partial_of (check q s h_tilde).2 h_tilde := by {
  match q with
  | literal lit => simp;
  | emp => simp;
  | singleton v1 v2 => {
    simp[check];
    simp[singleton_partial_some];
    apply Or.elim (Classical.em (h_tilde (s v1)).isSome);
    case left => {
      rw[is_some];
      intro ⟨ a, b ⟩;
      simp[b];
    }
    case right => {
      rw[is_not_some];
      intro temp;
      rw [temp];
      simp;
    }
  }
  | sep q1 q2 => {
    have partial1 := partiality q1 s h_tilde;
    have partial2 := partiality q2 s h_tilde;
    simp[check];
    simp[partial_of];
    intro x;
    simp[union];
    simp[partial_of] at partial1;
    have partial1_1 := partial1 x;
    simp[partial_of] at partial2;
    have partial2_1 := partial2 x;
    apply Or.elim (Classical.em ((check q1 s h_tilde).2 x = none));
    case left  => {
      apply Or.elim (Classical.em ((check q2 s h_tilde).2 x = none));
      case left => intro temp1 temp2; simp[temp1, temp2];
      case right => {
        intro temp1 temp2;
        rw[← is_not_some] at temp1;
        simp[dne] at temp1;
        rw[is_some] at temp1;
        have ⟨ witness, proof ⟩ := temp1;
        simp[proof, temp2];
        rw[proof] at partial2_1;
        simp at partial2_1;
        exact partial2_1;
      }
    }
    case right => {
      apply Or.elim (Classical.em ((check q2 s h_tilde).2 x = none));
      case left  => {
        intro temp1 temp2;
        simp[temp1, temp2];
        rw[← is_not_some] at temp2;
        simp[dne] at temp2;
        rw[is_some] at temp2;
        have ⟨ witness, proof ⟩ := temp2;
        simp[proof];
        rw[proof] at partial1_1;
        simp at partial1_1;
        exact partial1_1;
      }
      case right => {
        intro temp1 temp2;
        simp[temp1, temp2];
        rw[← is_not_some] at temp2;
        simp[dne] at temp2;
        rw[is_some] at temp2;
        have ⟨ witness, proof ⟩ := temp2;
        simp[proof];
        rw[proof] at partial1_1;
        simp at partial1_1;
        exact partial1_1;
      }
    }
  }
  | sepimp q1 q2 => {
    sorry;
  }
}

mutual
/-
--  | literal b => b
theorem equivalence_literal (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check (literal lit) s h_tilde); if b then (asrt (literal lit) s (λ x => some (h_tilde x))) ∨ (∀ h : Heap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt (literal lit) s h))) else ∀ h , (partial_of h h_tilde) → ¬(asrt (literal lit) s h) := by {
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
theorem equivalence_emp (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check emp s h_tilde); if b then (asrt emp s (λ x => some (h_tilde x))) ∨ (∀ h : Heap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt emp s h))) else ∀ h , (partial_of h h_tilde) → ¬(asrt emp s h) := by {
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
theorem equivalence_singleton (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check (singleton v1 v2) s h_tilde); if b then (asrt (singleton v1 v2) s (λ x => some (h_tilde x))) ∨ (∀ h : Heap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt (singleton v1 v2) s h))) else ∀ h , (partial_of h h_tilde) → ¬(asrt (singleton v1 v2) s h) := by {
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
theorem equivalence_sep (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check (sep q1 q2) s h_tilde); if b then (asrt (sep q1 q2) s (λ x => some (h_tilde x))) ∨ (∀ h : Heap , (partial_of h h_tilde) → ((dom h) = m ↔ (asrt (sep q1 q2) s h))) else ∀ h , (partial_of h h_tilde) → ¬(asrt (sep q1 q2) s h) := by {
  simp;
  
  split;
  case inl temp => {
    have ⟨ a, b, c ⟩ := temp;
    apply Or.inr;
    intro h partiality;
    simp[set_union];
    apply Iff.intro;
    case mp  => {
      intro z;
      have z1:= congrFun z;
      simp[asrt];
      
      sorry;
    }
    case mpr => {
      sorry;
    }
  }
  case inr => {
    sorry;
  }
}
--  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')



-/
theorem equivalence (s : Store) (h_tilde : Heap) : (let ⟨ b , m ⟩ := (check q s h_tilde);  (b ↔ (asrt q s h_tilde) ∨ (asrt q s m))) := by {
  match q with
  | literal lit => sorry;--simp[equivalence_literal];
  | emp => sorry;--simp[equivalence_emp];
  | singleton v1 v2 => sorry;--simp[equivalence_singleton];
  | sep q1 q2 => sorry;
  | sepimp q1 q2 => sorry;
}

end
