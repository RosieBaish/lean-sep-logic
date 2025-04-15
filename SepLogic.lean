--import FirstOrderLeaning
import Mathlib

--open Data.Set.Basic
--open Data.PFun
--open Logic

open Classical

/- Random Definitions and Theorems from FirstOrderLeaning -/
theorem forall_to_exists (p : Store → Heap → Heap → Prop) (f : ¬ ∀ s h h', ¬ (p s h h') ) : ∃ s h h', (p s h h') :=
  Classical.byContradiction
    (fun hyp1 : ¬ ∃ s h h', p s h h' =>
      have hyp2 : ∀ s h h', ¬ p s h h' :=
        fun s h h' =>
        fun hyp3 : p s h h' =>
        have hyp4 : ∃ s h h', p s h h' := ⟨ s , ⟨ h , ⟨h', hyp3⟩ ⟩ ⟩
        show False from hyp1 hyp4
      show False from f hyp2)

def dne {p} (hyp : ¬¬p) : p := by {
  apply Classical.byContradiction;
  intro Not_p;
  contradiction;
}
def dni {P : Prop} : P → ¬¬P := by {
  intros p np;
  exact np p;
}

theorem dne_equivalence {p}: ¬¬p ↔ p := by
  apply Iff.intro
  case mp =>  intro nnp; exact (dne nnp)
  case mpr => intro p; exact (dni p)

theorem dna_equivalence {p}: p ↔ ¬¬p:= by
  apply Iff.intro
  case mp => intro p; exact (dni p)
  case mpr =>  intro nnp; exact (dne nnp)


theorem exists_n_implies_n_forall {p : α → Prop} : (∃ x , ¬ p x) → (¬ ∀ x , p x) := by
  intro ⟨ x, not_p_x ⟩
  intro for_all
  have p_x := for_all x
  exact not_p_x p_x

theorem exists_implies_n_forall_n {p : α → Prop} : (∃ x , p x) → (¬ ∀ x , ¬ p x) := by
  intro ⟨ x, p_x ⟩
  intro for_all
  have not_p_x := for_all x
  exact not_p_x p_x

theorem forall_implies_n_exists_n {p : α → Prop} : (∀ x , p x) → ¬(∃ x , ¬ p x) := by
  intro for_all
  intro ⟨ x, not_p_x ⟩
  have p_x := for_all x
  exact not_p_x p_x

theorem n_exists_implies_forall_n {p : α → Prop} : (¬ ∃ x , p x) → (∀ x , ¬ p x) :=
by {
  intro ne;
  have ne2 := eq_false ne;
  simp [exists_implies_n_forall_n] at ne2;
  exact ne2;
}

theorem forall_n_implies_n_exists {p : α → Prop} : (∀ x , ¬ p x) → ¬(∃ x , p x) := by
  intro for_all
  intro ⟨ x, p_x ⟩
  have not_p_x := for_all x
  exact not_p_x p_x

theorem contrapos {A B : Prop} : (A → B) → ((¬B) → (¬A)) := by {
intro A_implies_B;
intro Not_B;
intro A;
have B := (A_implies_B A);
contradiction;
/-  intro a_to_b not_b a;
  exact not_b (a_to_b a);
-/
}

theorem inverse {A B : Prop} : ((¬B) → (¬A)) → (A → B) := by {
intro Not_B_implies_Not_A;
intro A;
apply Classical.byContradiction;
intro Not_B;
have Not_A := (Not_B_implies_Not_A Not_B);
contradiction;

/-
  intro nb_to_na;
  intro a;
  apply Classical.byContradiction;
  apply @contrapos (¬B) (¬A) nb_to_na;
  apply dni;
  exact a;
-/
}

theorem pp_imp_nn {A B : Prop} : (A → B) ↔ ((¬B) → (¬A)) := by
  apply Iff.intro
  case mp  => apply contrapos
  case mpr => apply inverse

theorem np_imp_pn {A B : Prop} : ((¬A) → B) ↔ ((¬B) → A) := by
  apply Iff.intro
  case mp  =>
    conv =>
      lhs
      rw [pp_imp_nn]
    intro nb_to_nna
    intro not_b
    have nna := nb_to_nna not_b
    exact (dne nna)
  case mpr =>
    intro nb_to_a
    intro not_a
    apply Classical.byContradiction (
      λ not_b => by
      have a := nb_to_a not_b
      exact not_a a
    )

theorem pn_imp_np {A B : Prop} : (A → (¬B)) ↔ (B → (¬A)) := by
  apply Iff.intro
  case mp  =>
    conv =>
      lhs
      rw [pp_imp_nn]
    intro nnb_to_na
    intro b
    have nnb := (dni b)
    exact nnb_to_na nnb
  case mpr =>
    intro b_to_na
    intro a
    apply Classical.byContradiction (
      λ nnb => by
      have not_a := b_to_na (dne nnb)
      exact not_a a
    )


theorem n_imp {P Q : Prop} : ((¬ P) → Q) ↔ (P ∨ Q) := by
  apply Iff.intro
  case mp  =>
    intro not_p_imp_q
    have p_or_not_p := Classical.em P
    apply Or.elim p_or_not_p
      (
        λ p => Or.inl p
      )
      (
        λ np => Or.inr (not_p_imp_q np)
      )
  case mpr =>
    intro p_or_q
    cases p_or_q with
    | inl p =>
      intro np
      apply absurd p np
    | inr q => intro; exact q

theorem n_forall_implies_exists_n {p : α → Prop} : ¬(∀ x , p x) → (∃ x , ¬ p x) := by {
  rw [np_imp_pn];
  intro not_exists x;
  cases h : Classical.em (p x) with
  | inl p_x => exact p_x;
  | inr np_x => {
    apply False.elim;
    apply not_exists;
    apply Exists.intro x;
    exact np_x
  }
}

theorem de_morgan (A B : Prop) : ¬(A ∧ B) ↔ ¬A ∨ ¬B := by
  cases Classical.em A with
  | inl a  => cases Classical.em B with
              | inl b  => simp [ a,  b]
              | inr nb => simp [ a, nb]
  | inr na => cases Classical.em B with
              | inl b  => simp [na,  b]
              | inr nb => simp [na, nb]

section triple_products
variable
  {α β γ: Type}
  (x : α)
  (y : β)
  (z : γ)
  (p : α → β → γ → Prop)
  (t : α × β × γ)

def p3 : α × β × γ :=
  (x, y, z)

def p3_app : Prop := p (t.fst) (t.snd.fst) (t.snd.snd)

theorem p3_app_id : p3_app p (p3 x y z) ↔ p x y z := Iff.intro id id

theorem fa3 : (∀ x y z , p x y z) ↔ (∀ t , (p3_app p) t) := by
  apply Iff.intro
  case mp  =>
    intro sep
    intro t
    simp [p3_app]
    apply sep
  case mpr =>
    intro comb
    intro x y z
    rw [← (p3_app_id x y z p)]
    exact comb (p3 x y z)


theorem e3 : (∃ x y z , ¬ p x y z) ↔ (∃ t , ¬ (p3_app p) t) := by
  apply Iff.intro
  case mp  =>
    intro ⟨ x , ⟨ y , ⟨ z , not_p ⟩⟩⟩
    apply Exists.intro (p3 x y z)
    apply not_p
  case mpr =>
    intro ⟨ t, not_t ⟩
    apply Exists.intro t.fst
    apply Exists.intro t.snd.fst
    apply Exists.intro t.snd.snd
    apply not_t

end triple_products

theorem is_some {A : Type} {O : Option A} : O.isSome ↔ ∃ a : A , O = some a := by
  apply Iff.intro
  case mp  =>
    simp[Option.isSome]
    split
    case h_1 x => intro; exists x
    case h_2   => intro a; apply absurd a; simp[Bool.not_true]
  case mpr =>
    intro ⟨ a, b ⟩
    simp[Option.isSome]
    simp[b]

theorem is_not_some {A : Type} {O : Option A} : ¬ O.isSome ↔ O = none := by
  apply Iff.intro
  case mp  =>
    simp[Option.isSome]
    split
    intro contradiction
    apply absurd contradiction
    rw[Bool.not_eq_false]
    simp
  case mpr =>
    intro o_none
    rw[is_some]
    intro ⟨ witness, proof ⟩
    rw[o_none] at proof
    contradiction

theorem is_not_some' {A : Type} {O : Option A} : (O.isSome = true) = False ↔ O = none := by
  apply Iff.intro
  case mp  =>
    simp[Option.isSome]
    split
    case h_1 =>
      intro contradiction
      apply absurd contradiction
      simp
    case h_2 =>
      intro
      simp
  case mpr =>
    intro o_none
    rw[is_some]
    rw[← eq_false]
    intro ⟨ witness, proof ⟩
    rw[o_none] at proof
    contradiction

theorem is_not_some'' {A : Type} {O : Option A} : (O.isSome = false) ↔ O = none := by
  apply Iff.intro
  case mp  =>
    simp[Option.isSome]
    split
    case h_1 =>
      intro contradiction
      apply absurd contradiction
      simp
    case h_2 =>
      intro
      simp
  case mpr =>
    intro o_none
    simp[o_none]

theorem and_symm { p q : Prop } : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  case mp =>
    intro p_and_q
    have ⟨ p' , q' ⟩ := p_and_q
    apply And.intro
    case left =>
      exact q'
    case right =>
      exact p'
  case mpr =>
    intro q_and_p
    have ⟨ q' , p' ⟩ := q_and_p
    apply And.intro
    case left =>
      exact p'
    case right =>
      exact q'
/- End of FOL stuff -/

--variable (value : Type _)

inductive Asrt (v : Type _) where
  | literal : Bool → Asrt v
  | emp : Asrt v
  | singleton : Set v → Set v → Asrt v
  | sep : Asrt v → Asrt v → Asrt v
--  | sepimp : Asrt → Asrt → Asrt
open Asrt

def Store (v : Type _) : Type := Set v → Set v
def Heap (v : Type _) : Type := Set v →. Set v

def empty_partial {A B : Type} : A →. B := λ _ => Part.none

noncomputable def singleton_partial {A B : Type} (a : A) (b : B) : A →. B := λ x => if (x = a) then Part.some b else Part.none

noncomputable def singleton_partial_some {A B : Type} (a : A) (b : Part B) : A →. B := match b.toOption with
  | some x => singleton_partial a x
  | none => empty_partial


def disjoint {A B : Type} (p1 p2 : A →. B) : Prop := Disjoint p1.Dom p2.Dom
--  (p1.Dom) ∩ (p2.Dom) = ∅

infix:60 " ⊥ " => disjoint

theorem disjoint_symm {A B : Type} {p1 p2 : A →. B} : p1 ⊥ p2 ↔ p2 ⊥ p1 := by
  simp[disjoint]
  apply Iff.intro
  case mp  =>
    rw[Set.disjoint_iff_inter_eq_empty]
    intro temp
    rw[Set.disjoint_iff_inter_eq_empty]
    rw [← temp]
    rw[Set.inter_comm]
  case mpr =>
    rw[Set.disjoint_iff_inter_eq_empty]
    intro temp
    rw[Set.disjoint_iff_inter_eq_empty]
    rw [← temp]
    rw[Set.inter_comm]

@[simp]
def in_partial {A B : Type} (a : A) (p : A →. B) : Prop := a ∈ p.Dom

def partial_of {A B : Type} (p1 p2 : A →. B) : Prop :=
  p1.Dom ⊆ p2.Dom ∧ (∀ x ∈ p1.Dom , ((p1 x) = (p2 x)))
--  p1.graph ⊆ p2.graph

infix:60 " ⊆ " => partial_of

--theorem partial_of_alternate_defn {A B : Type} {p1 p2 : A →. B} : ((PFun.graph p1) ⊆ (PFun.graph p2): Prop) ↔ (p1.Dom ⊆ p2.Dom ∧ (∀ x ∈ p1.Dom , ((p1 x) = (p2 x)))) :=
--by {
--
--}

@[simp] theorem partial_of_emp {A B : Type} (p : A →. B) : empty_partial ⊆ p := by
  simp[partial_of]
  simp[empty_partial]
  unfold empty_partial
  simp [PFun.Dom]



@[simp] theorem partial_of_singleton {A B : Type} (a : A) (b : B) (p : A →. B) : ((singleton_partial a b) ⊆ p) ↔ (p a = some b) := by
  simp [partial_of]
  simp [singleton_partial]
  apply Iff.intro
  case mp  =>
    intro ⟨ _ , precondition_2 ⟩
    have p1 := precondition_2 a
    simp at p1
    rw[p1]
  case mpr =>
    intro p_a
    apply And.intro
    case left =>
      unfold singleton_partial
      simp;
      rw[← PFun.Dom]
      intro x
      apply Or.elim (Classical.em (x = a)) <;> intro temp <;> simp [temp]
      · rw [p_a]
        apply Exists.intro b
        simp
    case right =>
      intro x x_1
      apply Or.elim (Classical.em (x = a)) <;> intro temp <;> simp[temp]
      · intro
        rw [p_a]

theorem partial_of_self (p : A →. B) : p ⊆ p := by
  simp[partial_of]

theorem partial_of_transitive {p1 p2 p3 : A →. B} : p1 ⊆ p2 → p2 ⊆ p3 → p1 ⊆ p3 := by {
  simp[partial_of];
  intro p1_p2_dom p1_p2_same p2_p3_dom p2_p3_same;
  apply And.intro (Set.Subset.trans p1_p2_dom p2_p3_dom)
  intro x y;
  have p1_p2 := p1_p2_same x y;
  have p2_p3 := p2_p3_same x y;
  intro y_in_p1x;
  simp [y_in_p1x] at p1_p2;
  rw[p1_p2];
  rw[p2_p3];
  rw[← p1_p2];
  exact y_in_p1x
}

theorem disjoint_partial {p1 p2 p1' : A →. B} : p1 ⊥ p2 → p1' ⊆ p1 → p1' ⊥ p2 := by {
  simp[disjoint, partial_of];
  intro disjoint_proof;
  intro partial_proof _;
  apply Set.disjoint_of_subset_left partial_proof disjoint_proof;
}

noncomputable def union {A : Type} (p1 p2 : A →. B) : A →. B :=
  λ x => if (p1 x) = Part.none then (p2 x) else (p1 x)

infix:60 " ∪ " => union

theorem test_lemma {x : Prop} : ¬ x ↔ x = False := by
  apply Iff.intro
  case mp =>
    intro temp
    apply eq_false
    exact temp
  case mpr =>
    intro temp
    rw[temp]
    simp

theorem union_disjoint_symm {p1 p2 : A →. B} : p1 ⊥ p2 → p1 ∪ p2 = p2 ∪ p1 := by
  unfold disjoint
  unfold union
  intro disjoint_proof
  apply funext
  intro x
  -- Split into 4 cases for each of p1 x and p2 x being some or none
  -- 3 of these are trivially true so simp gets them
  split_ifs with h1 h2 h2 <;> try simp [h1, h2]
  -- This is the case where p1 and p2 intersect, which can't happen
  -- So we prove the contradiction instead.
  rw [← ne_eq] at h2
  rw [Part.ne_none_iff] at h2
  have ⟨ temp3, temp4 ⟩ := h2
  rw [← ne_eq] at h1
  rw [Part.ne_none_iff] at h1
  have ⟨ temp5 , temp6 ⟩ := h1
  rw [Set.disjoint_left] at disjoint_proof
  have dp := @disjoint_proof x
  rw [PFun.mem_dom] at dp
  rw [Part.eq_some_iff] at temp4
  rw [Part.eq_some_iff] at temp6
  have dp2 := dp ⟨temp5 , temp6⟩
  rw [PFun.mem_dom] at dp2
  have dp3 := dp2 ⟨ temp3 , temp4 ⟩
  contradiction

theorem partial_of_p1_union {p1 p2 : A →. B} :  p1 ⊥ p2 → p = p1 ∪ p2 → p1 ⊆ p := by
  unfold union
  intro _ p_defn
  unfold partial_of
  rw[p_defn]
  apply And.intro
  case left =>
    rw [PFun.dom_eq]
    rw [PFun.dom_eq]
    rw [Set.setOf_subset_setOf]
    intro a
    intro ⟨ y , pa ⟩
    apply Exists.intro y
    have pa1 := pa
    rw [← Part.eq_some_iff] at pa1
    rw [pa1]
    simp
  case right =>
    intro x
    intro x1_in_p1
    simp
    have h : p1 x ≠ Part.none := by
      contrapose! x1_in_p1
      simp [Part.Dom, x1_in_p1]
    simp [h]

theorem partial_of_union {p1 p2 : A →. B} : p1 ⊥ p2 → p = p1 ∪ p2 → p1 ⊆ p ∧ p2 ⊆ p := by
  intro disjoint_proof_p1_p2 p_p1_p2
  have disjoint_proof_p2_p1 := (disjoint_symm.mp disjoint_proof_p1_p2)
  have p_p2_p1 : p = (union p2 p1) := by { rw[(union_disjoint_symm disjoint_proof_p1_p2)] at p_p1_p2; exact p_p1_p2;}
  apply And.intro (partial_of_p1_union disjoint_proof_p1_p2 p_p1_p2)
                  (partial_of_p1_union disjoint_proof_p2_p1 p_p2_p1)


noncomputable def partial_difference {A B : Type} (p1 p2 : A →. B) : A →. B :=
λ x => match (p2 x).toOption with
  | some _ => Part.none
  | none => p1 x

infix:60 "\\" => partial_difference

theorem eq_false'' {A : Prop} : (A = False) → ¬ A := by
  intro a_false
  intro a
  rw[a_false] at a
  exact a

theorem exists_witness {A : Type} : (witness : A) → (∃ (a : A) , witness = a) := by
  intro witness
  apply Exists.intro witness
  simp

theorem partial_of_disjoint_subtraction {A B : Type} {p1 p2 p3 : A →. B} : p1 ⊆ p3 ∧ disjoint p1 p2 → p1 ⊆ (partial_difference p3 p2) := by
  simp [partial_of, partial_difference, disjoint]
  intro _
  intro p1_overlap_p3
  intro p1_disjoint_p2
  apply And.intro
  case left =>
    intro x
    simp
    intro y y_p1_x
    rw [Set.disjoint_left] at p1_disjoint_p2
    have dp := @p1_disjoint_p2 x
    rw [PFun.mem_dom] at dp
    rw [PFun.mem_dom] at dp
    have dp2 := dp ⟨ y , y_p1_x ⟩
    apply Or.elim (Part.eq_none_or_eq_some (p2 x))
    case left =>
      unfold partial_difference
      intro p2x_none
      simp [p2x_none]
      have := p1_overlap_p3 x y y_p1_x
      apply Exists.intro y
      rw [← this]
      exact y_p1_x
    case right =>
      intro ⟨witness, proof ⟩
      rw [Part.eq_some_iff] at proof
      simp [eq_false] at dp2
      have := dp2 witness
      contradiction
  case right =>
    intro x y
    intro y_p1_x
    rw [Set.disjoint_left] at p1_disjoint_p2
    have dp := @p1_disjoint_p2 x
    rw [PFun.mem_dom] at dp
    rw [PFun.mem_dom] at dp
    have dp2 := dp ⟨ y , y_p1_x ⟩
    have temp := Part.eq_none_or_eq_some (p2 x)

    apply Or.elim temp
    case left =>
      intro p2x_none
      simp [p2x_none]
      exact p1_overlap_p3 x y y_p1_x
    case right =>
      intro ⟨witness, proof ⟩
      rw [Part.eq_some_iff] at proof
      simp [eq_false] at dp2
      have := dp2 witness
      contradiction

theorem partial_of_difference_self {A B : Type} (p1 p2 : A →. B) : partial_difference p1 p2 ⊆ p1 := by
  simp[partial_of, partial_difference]
  apply And.intro
  case left =>
    rw[PFun.dom_eq]
    rw[PFun.dom_eq]
    rw [Set.setOf_subset_setOf]
    intro x
    unfold partial_difference
    apply Or.elim (Part.eq_none_or_eq_some (p2 x))
    case left =>
      intro p2x_none
      simp [p2x_none]
    case right =>
      intro ⟨y, p2x_y⟩
      simp [p2x_y]
  case right =>
    intro x
    apply Or.elim (Part.eq_none_or_eq_some (p2 x))
    case left =>
      intro px_none
      simp [px_none]
    case right =>
      intro ⟨ y, p2_x ⟩
      simp [p2_x]

theorem difference_disjoint {A B : Type} (p1 p2 : A →. B) :  (p1 \ p2) ⊥ p2 := by
  simp[partial_difference, disjoint]
  rw[PFun.dom_eq]
  rw[PFun.dom_eq]
  rw[Set.disjoint_iff_inter_eq_empty]
  rw[Set.inter_def]
  simp
  rw[← Set.setOf_false]
  rw[Set.ext_iff]
  intro x
  rw[Set.mem_setOf_eq]
  rw[Set.mem_setOf_eq]
  apply Iff.intro
  case mp =>
    unfold partial_difference
    intro ⟨ l, ⟨ y , p2_x ⟩ ⟩
    rw [← Part.eq_some_iff] at p2_x
    simp [p2_x] at l
  case mpr =>
    simp;

theorem difference_union_opposite {p1 p2 : A →. B} : p2 ⊆ p1 → p1 = (partial_difference p1 p2) ∪ p2 := by
  simp[partial_difference, union, partial_of]
  unfold partial_difference
  unfold union
  intro _
  intro overlap
  apply PFun.ext
  intro x y
  apply Or.elim (Part.eq_none_or_eq_some (p2 x))
  case left =>
    intro p2x_none
    simp [p2x_none]
    apply Or.elim (Part.eq_none_or_eq_some (p1 x))
    case left =>
      intro temp
      simp [temp]
    case right =>
      intro ⟨_ , temp ⟩
      simp [temp]
  case right =>
    intro ⟨ witness, proof ⟩
    simp [proof]
    rw [Part.eq_some_iff] at proof
    have temp := overlap x witness proof
    rw [← temp]
    apply Iff.intro
    case mp =>
      intro proof2
      have := Part.mem_unique proof2 proof
      exact this
    case mpr =>
      intro eq
      simp [eq]
      exact proof

theorem difference_union_opposite' {p1 p2 : A →. B} : p2 ⊆ p1 → p1 = p2 ∪ (partial_difference p1 p2) := by
  rw[union_disjoint_symm]
  exact difference_union_opposite
  exact disjoint_symm.mp (difference_disjoint p1 p2)


def asrt {v : Type _} (q : Asrt v) (s : Store v) (h : Heap v) : Prop := match q with
  | literal b => b
  | emp       => h.Dom = ∅ --∀ x , (dom h) x = false
  | Asrt.singleton v1 v2 => h (s v1) = some (s v2) ∧ ∀ x , x ∈ h.Dom ↔ (x = (s v1))
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
--  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

@[simp]
noncomputable def check {v : Type _} (q : Asrt v) (s : Store v) (h : Heap v) : (Prop × Heap v) := match q with
  | literal b => (b , empty_partial)
  | emp       => (True, empty_partial)
  | Asrt.singleton v1 v2 => (h (s v1) = some (s v2) , singleton_partial_some (s v1) (h (s v1)))
  | sep q1 q2 => let ⟨ b1 , m1 ⟩ := (check q1 s h); let ⟨ b2 , m2 ⟩ := (check q2 s h); (b1 ∧ b2 ∧ (disjoint m1 m2) , (union m1 m2))
--  | sepimp q1 q2 => let ⟨ b1 , m1 , t1 ⟩ := (check q1 s h); let ⟨ b2 , m2 , t2 ⟩ := (check q2 s h); (b1 → b2 ∧ m1 ⊆ m2 , partial_difference m2 m1 , sorry)

def tight {v : Type _} (q : Asrt v) : Prop := match q with
  | literal _ => False
  | emp => True
  | Asrt.singleton _ _ => True
  | sep q1 q2 => tight q1 ∧ tight q2
--  | sepimp q1 q2 => False;

theorem union_dom {A B : Type} {a b : PFun A B} {x : A} : x ∈ (a ∪ b).Dom ↔ x ∈ a.Dom ∨ x ∈ b.Dom := by
  unfold union
  constructor
  · intro premise
    apply Or.elim (Classical.em (a x = Part.none))
    case mp.left =>
      intro temp
      simp [temp] at premise
      apply Or.inr
      unfold PFun.Dom
      simp [premise]
    case mp.right =>
      intro temp
      simp [temp] at premise
      apply Or.inl
      unfold PFun.Dom
      simp [premise]
  · intro x_in_a_or_b
    rcases x_in_a_or_b with x_in_a | x_in_b
    · simp at x_in_a
      have ⟨ y, y_in_ax ⟩ := x_in_a
      rw [← Part.eq_some_iff] at y_in_ax
      simp [y_in_ax]
    · simp at x_in_b
      have ⟨ y, y_in_bx ⟩ := x_in_b
      rw [← Part.eq_some_iff] at y_in_bx
      simp [y_in_bx]
      apply Or.elim (Classical.em (a x = Part.none)) <;> intro temp <;> simp [temp]
      rw [Part.eq_none_iff'] at temp
      exact dne temp

theorem subset_union {A B : Type} {a b c : PFun A B} : a ⊆ c ∧ b ⊆ c → (a ∪ b) ⊆ c := by
  unfold partial_of
  intro ⟨⟨ a_c_dom, a_c_match⟩ , ⟨ b_c_dom, b_c_match ⟩⟩
  apply And.intro
  · intro x
    rw [union_dom]
    intro x_in_a_or_b
    rcases x_in_a_or_b with x_in_a | x_in_b
    · exact a_c_dom x_in_a
    · exact b_c_dom x_in_b
  · intro x
    rw [union_dom]
    unfold union
    intro x_in_a_or_b
    rcases x_in_a_or_b with x_in_a | x_in_b
    · have ax_eq_cx : a x = c x := a_c_match x x_in_a
      simp [Part.Dom] at x_in_a
      have ⟨ y, y_in_ax ⟩ := x_in_a
      rw [← Part.eq_some_iff] at y_in_ax
      rw [y_in_ax]
      simp
      rw [ax_eq_cx] at y_in_ax
      simp [y_in_ax]
    · have bx_eq_cx : b x = c x := b_c_match x x_in_b
      simp [Part.Dom] at x_in_b
      have ⟨ y, y_in_bx ⟩ := x_in_b
      rw [← Part.eq_some_iff] at y_in_bx
      rw [y_in_bx]
      apply Or.elim (Classical.em (a x = Part.none)) <;> intro temp <;> simp [temp]
      · rw [Part.eq_none_iff'] at temp
        rw [bx_eq_cx] at y_in_bx
        simp [y_in_bx]
      · apply a_c_match
        have := (Part.eq_none_or_eq_some (a x))
        simp [temp] at this
        have ⟨ y', ax_is_y' ⟩ := this
        simp
        rw [Part.eq_some_iff] at ax_is_y'
        apply Exists.intro y'
        exact ax_is_y'

theorem partiality {v: Type _} (q : Asrt v) (s : Store v) (h_tilde : Heap v) : (check q s h_tilde).2 ⊆ h_tilde := by
  match q with
  | literal _ => simp
  | emp => simp
  | Asrt.singleton v1 v2 =>
    simp [check]
    simp [singleton_partial_some]
    cases h: (h_tilde (s v1)).toOption with
    | none =>
      simp
    | some x =>
      simp
      apply congr_arg Part.ofOption at h
      simp at h
      exact h
  | sep q1 q2 =>
    have partial1 := partiality q1 s h_tilde
    have partial2 := partiality q2 s h_tilde
    simp [check]
    apply subset_union
    exact ⟨ partial1, partial2 ⟩
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

theorem uniqueness {v : Type _} {q : Asrt v} {s : Store v} {h_tilde : Heap v}:
  (check q s h_tilde).1 ∧ tight q → ∀ h h' , (asrt q s h ∧ asrt q s h' → h = h') := by
  match q with
  | literal lit => simp[asrt, tight]
  | emp =>
    simp[asrt]
    intro _ h h' hx h'x

    funext x
    have : x ∉ PFun.Dom h := by simp [hx]
    simp [PFun.Dom] at this
    rw [← Part.eq_none_iff'] at this
    rw [this]

    have : x ∉ PFun.Dom h' := by simp [h'x]
    simp [PFun.Dom] at this
    rw [← Part.eq_none_iff'] at this
    rw [this]
  | Asrt.singleton v1 v2 =>
    simp[asrt]
    intro _ _
    intros h h' a b c d
    apply funext
    intro x
    have bx := b x
    have dx := d x
    apply Or.elim (Classical.em (x = s v1))
    case left  =>
      intro xsv1
      simp[xsv1]
      simp[a, c]
    case right =>
      intro xnsv1
      simp[xnsv1] at bx
      simp[xnsv1] at dx
      rw [← Part.eq_none_iff] at bx dx
      rw [bx, dx]
  | sep q1 q2 =>
    unfold asrt tight
    simp only [check, exists_and_left, and_imp, forall_exists_index]
    intro check_q1 check_q2 _ tight_q1 tight_q2
    intro h h'
    intro h1 asrt_q1h1 h2 asrt_q2h2 _ h_h1_h2
    intro h1' asrt_q1h1' h2' asrt_q2h2' _ h_h1_h2'
    have q1_uniqueness := uniqueness (And.intro check_q1 tight_q1)
    have q2_uniqueness := uniqueness (And.intro check_q2 tight_q2)
    have h1_same := q1_uniqueness h1 h1' (And.intro asrt_q1h1 asrt_q1h1')
    have h2_same := q2_uniqueness h2 h2' (And.intro asrt_q2h2 asrt_q2h2')
    simp only [h_h1_h2, h_h1_h2', h1_same, h2_same]
  /-
  | sepimp q1 q2 => {
    simp;
    sorry;
  }-/

theorem check_of_superset {v : Type _} {q : Asrt v} {s : Store v} {h h_tilde : Heap v} : (check q s h).1 ∧ h ⊆ h_tilde → (check q s h) = (check q s h_tilde) := by
  cases q with
  | literal lit => simp[check]
  | emp => simp[check]
  | singleton v1 v2 =>
    unfold check partial_of
    intro ⟨ points, _, subset⟩
    simp at points
    have proof := subset (s v1)
    simp[points] at proof
    simp[points, proof]
  | sep q1 q2 =>
    simp only [check, Prod.mk.injEq, eq_iff_iff, and_imp]
    intro a1 a2 _ b
    have c1 := check_of_superset (And.intro a1 b)
    have c2 := check_of_superset (And.intro a2 b)
    simp[c1, c2]
--  | sepimp q1 q2 => sorry;

theorem no_false_neg : (asrt q s h) → (check q s h).1 := by
  cases q with
  | literal lit => unfold asrt check; intro; assumption
  | emp => simp[asrt, check]
  | singleton v1 v2 => unfold asrt check; intro ⟨ a, _ ⟩; exact a
  | sep q1 q2 =>
    unfold asrt check
    intro ⟨ h1, h2 , q1h1 , q2h2 , disjoint_h1_h2 , h_h1_h2 ⟩

    apply And.intro
    case left  =>
      have q1h1_b := (no_false_neg q1h1)
      have q1h := check_of_superset (And.intro q1h1_b (partial_of_union disjoint_h1_h2 h_h1_h2).1)
      rw[← q1h]
      exact q1h1_b
    case right =>
      apply And.intro
      case left  =>
        have q2h2_b := (no_false_neg q2h2)
        have q2h := check_of_superset (And.intro q2h2_b (partial_of_union disjoint_h1_h2 h_h1_h2).2)
        rw[← q2h]
        exact q2h2_b
      case right =>
        have c_q1h1_b := no_false_neg q1h1
        have q1_equiv := check_of_superset (And.intro c_q1h1_b (partial_of_union disjoint_h1_h2 h_h1_h2).1)
        have subset_1 := partiality q1 s h1
        rw[q1_equiv] at subset_1

        have c_q2h2_b := no_false_neg q2h2
        have q2_equiv := check_of_superset (And.intro c_q2h2_b (partial_of_union disjoint_h1_h2 h_h1_h2).2)
        have subset_2 := partiality q2 s h2
        rw[q2_equiv] at subset_2

        have temp := disjoint_partial disjoint_h1_h2 subset_1
        rw[disjoint_symm] at temp
        have temp2 := disjoint_partial temp subset_2
        rw[disjoint_symm] at temp2
        exact temp2
--  | sepimp q1 q2 => sorry;

theorem no_false_pos {v q s} {h_tilde : Heap v} : let ⟨ b, m ⟩ := (check q s h_tilde); b → asrt q s m := by
  cases q with
  | literal lit => unfold check asrt; intro; assumption
  | emp => unfold check asrt empty_partial; simp
  | singleton v1 v2 =>
    unfold check asrt
    simp
    intro points
    rw[points]
    unfold singleton_partial_some singleton_partial
    simp
    intro x
    apply Or.elim (Classical.em (x = s v1))
    case left  =>
      intro x_s_v1
      simp[x_s_v1, Option.isSome]
    case right =>
      intro not_x_s_v1
      simp[not_x_s_v1]
  | sep q1 q2 =>
    unfold check asrt
    intro ⟨ b1 , b2 , disjoint_m1_m2 ⟩
    apply Exists.intro (check q1 s h_tilde).2
    apply Exists.intro (check q2 s h_tilde).2
    apply And.intro (no_false_pos b1)
    apply And.intro (no_false_pos b2)
    apply And.intro (disjoint_m1_m2)
    simp

variable (q : Asrt v)
variable (s : Store v)
variable (h_tilde : Heap v)
variable (b : (check q s h_tilde).1)

theorem tightness {q s h_tilde} : let ⟨ b , m ⟩ := (check q s h_tilde); (b ∧ ¬ tight q) → ∀ h : Heap v, m ⊆ h ∧ h ⊆ h_tilde → asrt q s h := by
  cases q with
  | literal lit => unfold asrt check; intro ⟨ _ , _ ⟩ _ _; assumption
  | emp => simp[asrt, check, tight]
  | singleton v1 v2 => simp[tight]
  | sep q1 q2 =>
    unfold check tight
    intro ⟨ ⟨ b1 , b2 , disjoint_m1_m2 ⟩ , not_both_tight ⟩ h
    rw [de_morgan] at not_both_tight
    intro ⟨ partial_m_h , partial_h_h_tilde ⟩
    have partial_m1_h := partial_of_transitive (partial_of_union disjoint_m1_m2 rfl).left  partial_m_h
    have partial_m2_h := partial_of_transitive (partial_of_union disjoint_m1_m2 rfl).right partial_m_h
    apply Or.elim not_both_tight
    case left  =>
      intro not_tight_q1
      apply Exists.intro (partial_difference h (check q2 s h_tilde).2)
      apply Exists.intro (check q2 s h_tilde).2
      have partial_m1_diff := partial_of_disjoint_subtraction (And.intro partial_m1_h disjoint_m1_m2)
      apply And.intro (tightness (And.intro b1 not_tight_q1) (partial_difference h (check q2 s h_tilde).2) (And.intro partial_m1_diff (partial_of_transitive (partial_of_difference_self h (check q2 s h_tilde).2) partial_h_h_tilde)))
      apply And.intro (no_false_pos b2)
      apply And.intro (difference_disjoint h (check q2 s h_tilde).2)
      exact (difference_union_opposite partial_m2_h)
    case right =>
      intro not_tight_q2
      apply Exists.intro (check q1 s h_tilde).2
      apply Exists.intro (partial_difference h (check q1 s h_tilde).2)
      have partial_m2_diff := partial_of_disjoint_subtraction (And.intro partial_m2_h (disjoint_symm.mp disjoint_m1_m2))
      apply And.intro (no_false_pos b1)
      apply And.intro (tightness (And.intro b2 not_tight_q2) (partial_difference h (check q1 s h_tilde).2) (And.intro partial_m2_diff (partial_of_transitive (partial_of_difference_self h (check q1 s h_tilde).2) partial_h_h_tilde)))
      apply And.intro (disjoint_symm.mp (difference_disjoint h (check q1 s h_tilde).2))
      exact (difference_union_opposite' partial_m1_h)
--  | sepimp q1 q2 => False;

theorem equivalence (s : Store v) (h_tilde : Heap v) : let ⟨ b , m ⟩ := (check q s h_tilde); asrt q s h_tilde ↔ b ∧ (tight q → h_tilde = m) := by
  simp
  apply Iff.intro
  case mp  =>
    intro asrt_q_s_h_tilde
    have b := no_false_neg asrt_q_s_h_tilde
    apply And.intro b
    intro tight_q
    have uniqueness_of_heaps := uniqueness (And.intro b tight_q)
    have asrt_q_s_m := no_false_pos b
    have h_tilde_equal_m := uniqueness_of_heaps h_tilde (check q s h_tilde).2 (And.intro asrt_q_s_h_tilde asrt_q_s_m)
    exact h_tilde_equal_m
  case mpr =>
    intro ⟨ b, tight_implies_h_tilde_equal_m ⟩
    have asrt_q_s_m := no_false_pos b
    apply Or.elim (Classical.em (tight q))
    case left  =>
      intro tight_q
      have h_tilde_equal_m := tight_implies_h_tilde_equal_m tight_q
      revert asrt_q_s_m
      rw[← h_tilde_equal_m]
      intro; assumption
    case right =>
      intro not_tight_q
      have partial_implies_asrt_q_s_h_tilde := (tightness (And.intro b not_tight_q)) h_tilde
      have partial_m_h_tilde := And.intro (partiality q s h_tilde) (partial_of_self h_tilde)
      exact (partial_implies_asrt_q_s_h_tilde partial_m_h_tilde)
