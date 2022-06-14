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

theorem disjoint_symm {A B : Type} {p1 p2 : Partial A B} : (disjoint p1 p2) ↔ (disjoint p2 p1) := by {
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

theorem partial_of_self (p : Partial A B) : partial_of p p := by {
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

theorem disjoint_partial {p1 p2 p1' : Partial A B} : (disjoint p1 p2) → (partial_of p1' p1) → (disjoint p1' p2) := by {
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

theorem union_disjoint_symm {A B : Type} (p1 p2 : Partial A B) : (disjoint p1 p2) → (union p1 p2) = (union p2 p1) := by {
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

theorem partial_of_p1_union {A B : Type} (p p1 p2 : Partial A B) : (disjoint p1 p2) → p = (union p1 p2) → (partial_of p1 p) := by {
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

theorem partial_of_union {A B : Type} (p p1 p2 : Partial A B) : (disjoint p1 p2) → p = (union p1 p2) → (partial_of p1 p) ∧ (partial_of p2 p) := by {
  intro disjoint_proof_p1_p2 p_p1_p2;
  have disjoint_proof_p2_p1 := (disjoint_symm.mp disjoint_proof_p1_p2);
  have p_p2_p1 : p = (union p2 p1) := by { rw[(union_disjoint_symm p1 p2 disjoint_proof_p1_p2)] at p_p1_p2; exact p_p1_p2;};
  apply And.intro (partial_of_p1_union p p1 p2 disjoint_proof_p1_p2 p_p1_p2)
                  (partial_of_p1_union p p2 p1 disjoint_proof_p2_p1 p_p2_p1);
}

def partial_difference {A : Type} (p1 p2 : Partial A A) : Partial A A :=
λ x => match (p2 x) with
  | some _ => none
  | none => p1 x

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
--  | sepimp q1 q2 => let ⟨ b1 , m1 , t1 ⟩ := (check q1 s h); let ⟨ b2 , m2 , t2 ⟩ := (check q2 s h); (b1 → b2 ∧ partial_of m1 m2 , partial_difference m2 m1 , sorry)

def tight (q : Asrt) : Prop := match q with
  | literal lit => False
  | emp => True
  | singleton v1 v2 => True
  | sep q1 q2 => tight q1 ∧ tight q2
--  | sepimp q1 q2 => False;


theorem tightness : let ⟨ b , m ⟩ := (check q s h_tilde); (b ∧ ¬ tight q) → ∀ h : Heap , (partial_of m h ∧ partial_of h h_tilde → asrt q s h) := by {
  sorry;
}

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
  | literal lit => simp[asrt]; sorry;
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

theorem check_of_superset (q : Asrt) (s : Store) (h h_tilde : Heap) : (check q s h).1 ∧ partial_of h h_tilde → (check q s h) = (check q s h_tilde) := by {
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
    have c1 := check_of_superset q1 s h h_tilde (And.intro a1 b);
    have c2 := check_of_superset q2 s h h_tilde (And.intro a2 b);
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
      have q1h := check_of_superset q1 s h1 h (And.intro q1h1_b (partial_of_union h h1 h2 disjoint_h1_h2 h_h1_h2).1);
      rw[← q1h];
      exact q1h1_b;
    }
    case right => {
      apply And.intro;
      case left  => {
        have q2h2_b := (no_false_neg q2h2)
        have q2h := check_of_superset q2 s h2 h (And.intro q2h2_b (partial_of_union h h1 h2 disjoint_h1_h2 h_h1_h2).2);
        rw[← q2h];
        exact q2h2_b;
      }
      case right => {
        have c_q1h1_b := no_false_neg q1h1;
        have q1_equiv := check_of_superset q1 s h1 h (And.intro c_q1h1_b (partial_of_union h h1 h2 disjoint_h1_h2 h_h1_h2).1);
        have subset_1 := partiality q1 s h1;
        rw[q1_equiv] at subset_1;

        have c_q2h2_b := no_false_neg q2h2;
        have q2_equiv := check_of_superset q2 s h2 h (And.intro c_q2h2_b (partial_of_union h h1 h2 disjoint_h1_h2 h_h1_h2).2);
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
  sorry
}

/-
--  | emp       => ∀ x , (dom h) x = false
theorem equivalence_emp (s : Store) (h_tilde : Heap) : (let ⟨ b , m ⟩ := (check emp s h_tilde);  (b ↔ if t then (asrt emp s m) else (asrt emp s h_tilde))) := by {
  simp[asrt];
  simp[empty_partial];
}

--  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) ∧ ∀ x , (dom h) x = (some x = (s v1))
theorem equivalence_singleton (s : Store) (h_tilde : Heap) : (let ⟨ b , m , t ⟩ := (check (singleton v1 v2) s h_tilde);  (b ↔ if t then (asrt (singleton v1 v2) s m) else (asrt (singleton v1 v2) s h_tilde))) := by {
  apply Iff.intro;
  case mp  => {
    intro points;
    simp[asrt];
    rw [if_pos]
    
    apply And.intro;
    case left  => {
      simp[points];
      simp[singleton_partial_some];
      simp[singleton_partial];
    }
    case right => {
      intro x;
      simp[points, singleton_partial_some, singleton_partial];
      rw[is_some];
      apply Or.elim (Classical.em (x = s v1));
      case left  => intro temp; simp[temp]; apply Exists.intro (s v2); simp;
      case right => intro temp; simp[temp]; intro n; have ⟨ a, f⟩ := n; contradiction;
    }
    case hc => simp;
  }
  case mpr => {
    rw[if_pos];
    simp[asrt];
    intro ⟨ l, r ⟩;
    revert l;
    simp[singleton_partial_some];
    apply Or.elim (Classical.em (h_tilde (s v1)).isSome);
    case left  => {
      rw[is_some];
      intro ⟨ witness, proof ⟩;
      simp[proof];
      simp[singleton_partial];
      intro;
      assumption;
    }
    case right => {
      rw[is_not_some];
      intro contr;
      simp[contr];
      simp[empty_partial];
    }
    case hc => simp;
  }
}
--  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
theorem equivalence_sep (s : Store) (h_tilde : Heap) : (let ⟨ b , m , t ⟩ := (check (sep q1 q2) s h_tilde);  (b ↔ if t then (asrt (sep q1 q2) s m) else (asrt (sep q1 q2) s h_tilde))) := by {
  simp;
  apply Iff.intro;
  case mp  => {
    intro ⟨ a, b, c ⟩;
    apply Or.elim (Classical.em ((check q1 s h_tilde).2.2 ∧ (check q2 s h_tilde).2.2));
    case left  => {
      intro ⟨ t1, t2 ⟩;
      simp[t1, t2];
      simp[union];
      simp[asrt];
      simp at equivalence;
      rw[equivalence] at a;
      simp[t1] at a;
      rw[equivalence] at b;
      simp[t2] at b;
      apply Exists.intro (check q1 s h_tilde).2.1;
      apply Exists.intro (check q2 s h_tilde).2.1;
      apply And.intro;
      case left  => exact a;
      case right => {
        apply And.intro;
        case left  => exact b;
        case right => {
          apply And.intro;
          case left  => exact c;
          case right => simp[union];
        }
      }
    }
    case right => {
      intro not_ts;
      simp[not_ts];
      simp[asrt];
      rw[de_morgan] at not_ts;
      apply Exists.intro (check q1 s h_tilde).2.1;
      apply Exists.intro (check q2 s h_tilde).2.1;
      simp[c];
      simp at equivalence;
      rw[equivalence] at a;
      rw[equivalence] at b;
      apply Or.elim (Classical.em (check q1 s h_tilde).2.2);
      case left  => {
        intro t1;
        simp[t1] at not_ts;
        have nt2 := by { exact not_ts }
        simp[t1] at a;
        simp[nt2] at b;
        sorry;
      }
      case right => {
        intro nt1;
        sorry;
      }
    }
  }
  case mpr => {
    split;
    case inl temp => {
      have ⟨ t1 , t2 ⟩ := temp;
      simp[asrt];
      intro ⟨ h1 , h2 , q1_h1 , q2_h2 , h1h2_disjoint , matching_unions ⟩;
      apply And.intro;
      case left => {
        simp at equivalence;
        rw[equivalence];
        rw[(if_pos t1)];
--        have temp := uniqueness q1 s h_tilde;
        sorry;
      }
      sorry;
    }
    case inr => {
      sorry;
    }
  }
}
--  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')
-/

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

