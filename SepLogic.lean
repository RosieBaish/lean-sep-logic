import FirstOrderLeaning

open Classical

inductive Asrt where
  | literal : Bool → Asrt
  | emp : Asrt
  | singleton : Nat → Nat → Asrt
  | sep : Asrt → Asrt → Asrt
--  | sepimp : Asrt → Asrt → Asrt
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

infix:60 " ⊥ " => disjoint

theorem disjoint_symm {A B : Type} {p1 p2 : Partial A B} : p1 ⊥ p2 ↔ p2 ⊥ p1 := by {
  simp[disjoint];
  simp[set_intersection];
  simp[empty_set];
  apply Iff.intro;
  case mp  => {
    intro lhs;
    rw[← lhs];
    apply funext;
    intro x;
    rw[and_symm];
  }
  case mpr => {
    intro lhs;
    rw[← lhs];
    apply funext;
    intro x;
    rw[and_symm];
  }
}

@[simp]
def in_partial {A B : Type} (a : A) (p : Partial A B) : Prop := (p a).isSome

def partial_of {A B : Type} (p1 p2 : Partial A B) : Prop :=
  ∀ x , match p1 x with
  | some y => (p2 x) = some y
  | none   => True

infix:60 " ⊆ " => partial_of

@[simp] theorem partial_of_emp {A B : Type} (p : Partial A B) : empty_partial ⊆ p := by {
  simp[partial_of, empty_partial];
}

@[simp] theorem partial_of_singleton {A B : Type} (a : A) (b : B) (p : Partial A B) : ((singleton_partial a b) ⊆ p) ↔ (p a = some b) := by {
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

theorem partial_of_self (p : Partial A B) : p ⊆ p := by {
  simp[partial_of];
  intro x;
  apply Or.elim (Classical.em (p x).isSome);
  case left  => {
    rw[is_some];
    intro ⟨ witness, proof ⟩;
    rw[proof];
  }
  case right => {
    rw[is_not_some];
    intro p_x_none;
    rw[p_x_none];
    simp;
  }
}

theorem partial_of_transitive {p1 p2 p3 : Partial A B} : p1 ⊆ p2 → p2 ⊆ p3 → p1 ⊆ p3 := by {
  simp[partial_of];
  intro p1_p2 p2_p3;
  intro x;
  have := p1_p2 x;
  apply Or.elim (Classical.em (p1 x).isSome);
  case left  => {
    simp[is_some];
    intro ⟨ witness, proof ⟩;
    rw[proof];
    simp;
    rw[proof] at this;
    simp at this;
    have p2_x := this;
    have := p2_p3 x;
    rw[p2_x] at this;
    simp at this;
    exact this;
  }
  case right => {
    rw[is_not_some];
    intro not_p1_x;
    rw[not_p1_x];
    simp;
  }
}

theorem disjoint_partial {p1 p2 p1' : Partial A B} : p1 ⊥ p2 → p1' ⊆ p1 → p1' ⊥ p2 := by {
  simp[disjoint, partial_of, set_intersection, empty_set];
  intro disjoint_proof;
  intro partial_proof;
  apply funext;
  intro x;
  have partial_proof1 := partial_proof x;
  have disjoint_proof1 := congrFun disjoint_proof x;
  apply Or.elim (Classical.em (p1' x).isSome);
  case left  => {
    intro temp;
    simp[temp];
    revert temp;
    rw[is_some];
    intro ⟨ witness, proof ⟩;
    revert disjoint_proof1;
    simp[proof] at partial_proof1;
    simp[partial_proof1];
    simp[Option.isSome];
    split <;> simp;
  }
  case right => {
    intro temp;
    simp[temp];
  }
}

noncomputable def union {A : Type} (p1 p2 : Partial A B) : Partial A B :=
λ x => if (p1 x) = none then (p2 x) else (p1 x)

infix:60 " ∪ " => union

theorem union_disjoint_symm : p1 ⊥ p2 → p1 ∪ p2 = p2 ∪ p1 := by {
  simp[disjoint, union, set_intersection, empty_set];
  intro disjoint_proof;
  apply funext;
  intro x;
  have disjoint_proof1 := congrFun disjoint_proof x;
  simp[de_morgan''] at disjoint_proof1;
  simp[is_not_some''] at disjoint_proof1;
  apply Or.elim (Classical.em (p1 x).isSome);
  case left  => {
    simp[is_some];
    intro ⟨ witness, proof ⟩;
    simp[proof];
    simp[proof] at disjoint_proof1;
    simp[disjoint_proof1];
  }
  case right => {
    simp[is_not_some''];
    intro temp;
    simp[temp];
    match p2 x with
    | some _ => simp;
    | none   => simp;
  }
}

theorem partial_of_p1_union : p1 ⊥ p2 → p = p1 ∪ p2 → p1 ⊆ p := by {
  simp[union];
  intro disjoint_proof p_defn;
  simp[partial_of];
  rw[p_defn];
  intro x;
  apply Or.elim (Classical.em (p1 x).isSome);
  case left  => {
    simp[is_some];
    intro ⟨ witness, proof ⟩;
    rw[proof];
    simp;
  }
  case right => {
    simp[is_not_some''];
    intro h1x_none;
    simp[h1x_none];
  }
}

theorem partial_of_union : p1 ⊥ p2 → p = p1 ∪ p2 → p1 ⊆ p ∧ p2 ⊆ p := by {
  intro disjoint_proof_p1_p2 p_p1_p2;
  have disjoint_proof_p2_p1 := (disjoint_symm.mp disjoint_proof_p1_p2);
  have p_p2_p1 : p = (union p2 p1) := by { rw[(union_disjoint_symm disjoint_proof_p1_p2)] at p_p1_p2; exact p_p1_p2;};
  apply And.intro (partial_of_p1_union disjoint_proof_p1_p2 p_p1_p2)
                  (partial_of_p1_union disjoint_proof_p2_p1 p_p2_p1);
}

noncomputable def partial_difference {A B : Type} (p1 p2 : Partial A B) : Partial A B :=
λ x => match (p2 x) with
  | some _ => none
  | none => p1 x

infix:60 "\\" => partial_difference

theorem eq_false'' {A : Prop} : (A = False) → ¬ A := by {
  intro a_false;
  intro a;
  rw[a_false] at a;
  exact a;
}

theorem exists_witness {A : Type} : (witness : A) → (∃ (a : A) , witness = a) := by {
  intro witness;
  apply Exists.intro witness;
  simp;
}

theorem partial_of_disjoint_subtraction {A B : Type} {p1 p2 p3 : Partial A B} : p1 ⊆ p3 ∧ disjoint p1 p2 → p1 ⊆ (partial_difference p3 p2) := by {
  simp [partial_of, partial_difference, disjoint, set_intersection, empty_set];
  intro ⟨ partial_p1_p3 , disjoint_p1_p2 ⟩ x;
  have partial_p1_p3_x := partial_p1_p3 x;
  apply Or.elim (Classical.em (p1 x).isSome);
  case left  => {
    rw[is_some];
    intro ⟨ witness, proof⟩;
    rw[proof];
    simp;
    rw[proof] at partial_p1_p3_x;
    simp at partial_p1_p3_x;
    have := (congrFun disjoint_p1_p2) x;
    rw[proof] at this;
    rw[is_some] at this;
    simp at this;
    have := eq_false'' this;
    simp[(exists_witness witness)] at this;
    rw[is_not_some''] at this;
    simp[this];
    assumption;
  }
  case right => {
    rw[is_not_some];
    intro p1_x_none;
    rw[p1_x_none];
    simp;
  }
}

theorem partial_of_difference_self {A B : Type} (p1 p2 : Partial A B) : partial_difference p1 p2 ⊆ p1 := by {
  simp[partial_of, partial_difference];
  intro x;
  apply Or.elim (Classical.em (p2 x).isSome);
  case left  => {
    rw[is_some];
    intro ⟨ proof , witness ⟩;
    simp[witness];
  }
  case right => {
    rw[is_not_some];
    intro not_p2_x;
    simp[not_p2_x];
    apply Or.elim (Classical.em (p1 x).isSome);
    case left  => {
      rw[is_some];
      intro ⟨ witness , proof ⟩;
      simp[proof];
    }
    case right => {
      rw[is_not_some];
      intro not_p1_x;
      simp[not_p1_x];
    }
  }
}

theorem difference_disjoint {A B : Type} (p1 p2 : Partial A B) : partial_difference p1 p2 ⊥ p2 := by {
  simp[partial_difference, disjoint, set_intersection, empty_set];
  apply funext;
  intro x;
  apply Or.elim (Classical.em (p2 x).isSome);
  case left  => {
    rw[is_some];
    intro ⟨ witness, proof ⟩;
    rw[proof];
    simp[Option.isSome];
  }
  case right => {
    rw[is_not_some];
    intro p2_x_none;
    simp[p2_x_none, Option.isSome];
  }
}

theorem difference_union_opposite {p1 p2 : Partial A B} : p2 ⊆ p1 → p1 = (partial_difference p1 p2) ∪ p2 := by {
  simp[partial_difference, union, partial_of];
  intro p2_p1;
  apply funext;
  intro x;
  apply Or.elim (Classical.em (p2 x).isSome);
  case left  => {
    rw[is_some];
    intro ⟨ witness, proof ⟩;
    simp[proof];
    have := p2_p1 x;
    rw[proof] at this;
    simp at this;
    exact this;
  }
  case right => {
    rw[is_not_some];
    intro p2_x_none;
    simp[p2_x_none];
    apply Or.elim (Classical.em (p1 x).isSome);
    · rw[is_some]; intro ⟨ witness , proof ⟩ ; simp[proof];
    · rw[is_not_some]; intro temp; simp[temp];
  }
}

theorem difference_union_opposite' {p1 p2 : Partial A B} : p2 ⊆ p1 → p1 = p2 ∪ (partial_difference p1 p2) := by {
  rw[union_disjoint_symm];
  exact difference_union_opposite;
  exact disjoint_symm.mp (difference_disjoint p1 p2);
}

def asrt (q : Asrt) (s : Store) (h : Heap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => h (s v1) = some (s v2) ∧ ∀ x , (dom h) x ↔ (x = (s v1))
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
--  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

@[simp]
noncomputable def check (q : Asrt) (s : Store) (h : Heap) : (Prop × Heap) := match q with
  | literal b => (b , empty_partial)
  | emp       => (True, empty_partial)
  | singleton v1 v2 => (h (s v1) = some (s v2) , singleton_partial_some (s v1) (h (s v1)))
  | sep q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q2 s h); (b1 ∧ b2 ∧ (disjoint m1 m2) , (union m1 m2))
--  | sepimp q1 q2 => let ⟨ b1 , m1 , t1 ⟩ := (check q1 s h); let ⟨ b2 , m2 , t2 ⟩ := (check q2 s h); (b1 → b2 ∧ m1 ⊆ m2 , partial_difference m2 m1 , sorry)

def tight (q : Asrt) : Prop := match q with
  | literal lit => False
  | emp => True
  | singleton v1 v2 => True
  | sep q1 q2 => tight q1 ∧ tight q2
--  | sepimp q1 q2 => False;

theorem partiality (q : Asrt) (s : Store) (h_tilde : Heap) : (check q s h_tilde).2 ⊆ h_tilde := by {
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
/-  | sepimp q1 q2 => {
    have partial1 := partiality q1 s h_tilde;
    have partial2 := partiality q2 s h_tilde;
    simp[check];
    simp[partial_of];
    intro x;
    simp[partial_difference];
    simp[partial_of] at partial1;
    have partial1_1 := partial1 x;
    simp[partial_of] at partial2;
    have partial2_1 := partial2 x;
    apply Or.elim (Classical.em ((check q1 s h_tilde).2.1 x = none));
    case left  => {
      apply Or.elim (Classical.em ((check q2 s h_tilde).2.1 x = none));
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
      apply Or.elim (Classical.em ((check q2 s h_tilde).2.1 x = none));
      case left  => {
        intro temp1 temp2;
        simp[temp1, temp2];
        rw[← is_not_some] at temp2;
        simp[dne] at temp2;
        rw[is_some] at temp2;
        have ⟨ witness, proof ⟩ := temp2;
        simp[proof];
      }
      case right => {
        intro temp1 temp2;
        simp[temp1, temp2];
        rw[← is_not_some] at temp2;
        simp[dne] at temp2;
        rw[is_some] at temp2;
        have ⟨ witness, proof ⟩ := temp2;
        simp[proof];
      }
    }
  }-/
}

theorem uniqueness :
  (check q s h_tilde).1 ∧ tight q → ∀ h h' , (asrt q s h ∧ asrt q s h' → h = h') := by {
    match q with
  | literal lit => simp[asrt, tight];
  | emp => {
    intro ⟨ a, b ⟩ h h';
    simp[asrt];
    simp[is_not_some'];
    intro ⟨ hx , h'x ⟩;
    apply funext;
    intro x;
    rw[(hx x)];
    rw[(h'x x)];
  }
  | singleton v1 v2 => {
    simp[asrt];
    intro points;
    intro h h';
    intro ⟨ ⟨ a , b ⟩ , c , d ⟩;
    apply funext;
    intro x;
    have bx := b x;
    have dx := d x;
    have p := partiality q s h_tilde;
    apply Or.elim (Classical.em (x = s v1));
    case left  => {
      intro xsv1;
      simp[xsv1];
      simp[a, c];
    }
    case right => {
      intro xnsv1;
      simp[xnsv1] at bx;
      simp[xnsv1] at dx;
      simp[is_not_some''] at bx;
      simp[is_not_some''] at dx;
      simp[bx, dx];
    }
  }
  | sep q1 q2 => {
    simp[asrt];
    intro ⟨ ⟨ a1 , a2, a3  ⟩, b, c ⟩ h h' ⟨ ⟨ h1 , h2 , q1h1 , q2h2 , h1_disj_h2 , h_h1_h2 ⟩ , ⟨ h1' , h2' , q1h1' , q2h2' , h1_disj_h2' , h_h1_h2' ⟩ ⟩;
    have q1_uniqueness := uniqueness (And.intro a1 b);
    have q2_uniqueness := uniqueness (And.intro a2 c);
    have h1_same := q1_uniqueness h1 h1' (And.intro q1h1 q1h1');
    have h2_same := q2_uniqueness h2 h2' (And.intro q2h2 q2h2');
    simp[h_h1_h2, h_h1_h2', h1_same, h2_same];
  }
  /-
  | sepimp q1 q2 => {
    simp;
    sorry;
  }-/
}

theorem check_of_superset : (check q s h).1 ∧ h ⊆ h_tilde → (check q s h) = (check q s h_tilde) := by {
  match q with
  | literal lit => simp[check];
  | emp => simp[check];
  | singleton v1 v2 => {
    simp[check, partial_of];
    intro ⟨ points, subset ⟩;
    have proof := subset (s v1);
    simp[points] at proof;
    simp[points, proof];
  }
  | sep q1 q2 => {
    simp[check];--, partial_of];
    intro ⟨ ⟨ a1 , a2 , a3 ⟩ , b ⟩;
    have c1 := check_of_superset (And.intro a1 b);
    have c2 := check_of_superset (And.intro a2 b);
    simp[c1, c2];
  }
--  | sepimp q1 q2 => sorry;
}

theorem no_false_neg : (asrt q s h) → (check q s h).1 := by {
    match q with
  | literal lit => simp[asrt, check]; intro; assumption;
  | emp => simp[asrt, check];
  | singleton v1 v2 => simp[asrt, check]; intro ⟨ a, b ⟩; exact a;
  | sep q1 q2 => {
    simp[asrt, check];
    intro ⟨ h1, h2 , q1h1 , q2h2 , disjoint_h1_h2 , h_h1_h2 ⟩;

    apply And.intro;
    case left  => {
      have q1h1_b := (no_false_neg q1h1)
      have q1h := check_of_superset (And.intro q1h1_b (partial_of_union disjoint_h1_h2 h_h1_h2).1);
      rw[← q1h];
      exact q1h1_b;
    }
    case right => {
      apply And.intro;
      case left  => {
        have q2h2_b := (no_false_neg q2h2)
        have q2h := check_of_superset (And.intro q2h2_b (partial_of_union disjoint_h1_h2 h_h1_h2).2);
        rw[← q2h];
        exact q2h2_b;
      }
      case right => {
        have c_q1h1_b := no_false_neg q1h1;
        have q1_equiv := check_of_superset (And.intro c_q1h1_b (partial_of_union disjoint_h1_h2 h_h1_h2).1);
        have subset_1 := partiality q1 s h1;
        rw[q1_equiv] at subset_1;

        have c_q2h2_b := no_false_neg q2h2;
        have q2_equiv := check_of_superset (And.intro c_q2h2_b (partial_of_union disjoint_h1_h2 h_h1_h2).2);
        have subset_2 := partiality q2 s h2;
        rw[q2_equiv] at subset_2;

        have temp := disjoint_partial disjoint_h1_h2 subset_1;
        rw[disjoint_symm] at temp;
        have temp2 := disjoint_partial temp subset_2;
        rw[disjoint_symm] at temp2;
        exact temp2;
      }
    }
  }
--  | sepimp q1 q2 => sorry;
}

theorem no_false_pos : let ⟨ b, m ⟩ := (check q s h_tilde); b → asrt q s m := by {
  match q with
  | literal lit =>   simp[check, asrt]; intro; assumption;
  | emp => simp[check, asrt, empty_partial];
  | singleton v1 v2 => {
    simp[check, asrt, singleton_partial_some, singleton_partial];
    intro points;
    rw[points];
    simp;
    intro x;
    apply Or.elim (Classical.em (x = s v1));
    case left  => {
      intro x_s_v1;
      simp[x_s_v1, Option.isSome];
    }
    case right => {
      intro not_x_s_v1;
      simp[not_x_s_v1];
    }
  }
  | sep q1 q2 => {
    simp[check, asrt];
    intro ⟨ b1 , b2 , disjoint_m1_m2 ⟩ ;
    apply Exists.intro (check q1 s h_tilde).2;
    apply Exists.intro (check q2 s h_tilde).2;
    apply And.intro (no_false_pos b1);
    apply And.intro (no_false_pos b2);
    apply And.intro (disjoint_m1_m2);
    simp;
  }
}

variable (q : Asrt)
variable (s : Store)
variable (h_tilde : Heap)
variable (b : (check q s h_tilde).1)

theorem tightness {q s h_tilde} : let ⟨ b , m ⟩ := (check q s h_tilde); (b ∧ ¬ tight q) → ∀ h : Heap , m ⊆ h ∧ h ⊆ h_tilde → asrt q s h := by {
  match q with
  | literal lit => simp[asrt, check]; intro ⟨ _ , _ ⟩ _ _; assumption;
  | emp => simp[asrt, check, tight];
  | singleton v1 v2 => simp[tight];
  | sep q1 q2 => {
    simp[check, tight];
    intro ⟨ ⟨ b1 , b2 , disjoint_m1_m2 ⟩ , not_both_tight ⟩ h;
    rw [de_morgan] at not_both_tight;
    intro ⟨ partial_m_h , partial_h_h_tilde ⟩;
    have check_q_s_h_tilde : (check (sep q1 q2) s h_tilde).1 := And.intro b1 (And.intro b2 disjoint_m1_m2);
    have check_q_s_m : (check (sep q1 q2) s (check (sep q1 q2) s h_tilde).2).1 := no_false_neg (no_false_pos check_q_s_h_tilde);
    have partial_m1_h := partial_of_transitive (partial_of_union disjoint_m1_m2 rfl).left  partial_m_h;
    have partial_m2_h := partial_of_transitive (partial_of_union disjoint_m1_m2 rfl).right partial_m_h;
    apply Or.elim not_both_tight;
    case left  => {
      intro not_tight_q1;
      apply Exists.intro (partial_difference h (check q2 s h_tilde).2);
      apply Exists.intro (check q2 s h_tilde).2;
      have partial_m1_diff := partial_of_disjoint_subtraction (And.intro partial_m1_h disjoint_m1_m2);
      have b1_m1_eq_check_q1_s_diff := check_of_superset (And.intro (no_false_neg (no_false_pos b1)) partial_m1_diff);
      apply And.intro (tightness (And.intro b1 not_tight_q1) (partial_difference h (check q2 s h_tilde).2) (And.intro partial_m1_diff (partial_of_transitive (partial_of_difference_self h (check q2 s h_tilde).2) partial_h_h_tilde)));
      apply And.intro (no_false_pos b2);
      apply And.intro (difference_disjoint h (check q2 s h_tilde).2);
      exact (difference_union_opposite partial_m2_h);
    }
    case right => {
      intro not_tight_q2;
      apply Exists.intro (check q1 s h_tilde).2;
      apply Exists.intro (partial_difference h (check q1 s h_tilde).2);
      have partial_m2_diff := partial_of_disjoint_subtraction (And.intro partial_m2_h (disjoint_symm.mp disjoint_m1_m2));
      have b2_m2_eq_check_q2_s_diff := check_of_superset (And.intro (no_false_neg (no_false_pos b2)) partial_m2_diff);
      apply And.intro (no_false_pos b1);
      apply And.intro (tightness (And.intro b2 not_tight_q2) (partial_difference h (check q1 s h_tilde).2) (And.intro partial_m2_diff (partial_of_transitive (partial_of_difference_self h (check q1 s h_tilde).2) partial_h_h_tilde)));
      apply And.intro (disjoint_symm.mp (difference_disjoint h (check q1 s h_tilde).2));
      exact (difference_union_opposite' partial_m1_h);
    }
  }
--  | sepimp q1 q2 => False;
}

theorem equivalence (s : Store) (h_tilde : Heap) : let ⟨ b , m ⟩ := (check q s h_tilde); asrt q s h_tilde ↔ b ∧ (tight q → h_tilde = m) := by {
  simp;
  apply Iff.intro;
  case mp  => {
    intro asrt_q_s_h_tilde;
    have b := no_false_neg asrt_q_s_h_tilde;
    apply And.intro b;
    intro tight_q;
    have uniqueness_of_heaps := uniqueness (And.intro b tight_q);
    have asrt_q_s_m := no_false_pos b;
    have h_tilde_equal_m := uniqueness_of_heaps h_tilde (check q s h_tilde).2 (And.intro asrt_q_s_h_tilde asrt_q_s_m);
    exact h_tilde_equal_m;
  }
  case mpr => {
    intro ⟨ b, tight_implies_h_tilde_equal_m ⟩;
    have asrt_q_s_m := no_false_pos b;
    apply Or.elim (Classical.em (tight q));
    case left  => {
      intro tight_q;
      have h_tilde_equal_m := tight_implies_h_tilde_equal_m tight_q;
      revert asrt_q_s_m;
      rw[← h_tilde_equal_m];
      intro; assumption;
    }
    case right => {
      intro not_tight_q;
      have partial_implies_asrt_q_s_h_tilde := (tightness (And.intro b not_tight_q)) h_tilde;
      have partial_m_h_tilde := And.intro (partiality q s h_tilde) (partial_of_self h_tilde);
      exact (partial_implies_asrt_q_s_h_tilde partial_m_h_tilde);
    }
  }
}

