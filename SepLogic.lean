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

def dom {A B : Type}  (p : Partial A B) : Subset A := λ a => match (p a) with
| some _  => true
| none    => false

def disjoint {A B : Type} (p1 p2 : Partial A B) : Prop :=
set_intersect (dom p1) (dom p2) = empty_set

def union {A B : Type} (p1 p2 : Partial A B) : Partial A B :=
λ x => (p1 x) <|> (p2 x)

def asrt (q : Asrt) (s : Store) (h : Heap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2)
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')
 
theorem e_true : ∃ (s : Store) (h : Heap) , True := by
let s : Store := λ x => none
let h : Heap := λ x => none
exists s
exists h
simp

def same_domains : Heap → Heap → Prop :=
λ h h' => ((dom h) = (dom h'))

theorem forall_to_exists (p : Store → Heap → Heap → Prop) (f : ¬ ∀ s h h', ¬ (p s h h') ) : ∃ s h h', (p s h h') :=
  byContradiction
    (fun hyp1 : ¬ ∃ s h h', p s h h' =>
      have hyp2 : ∀ s h h', ¬ p s h h' :=
        fun s h h' =>
        fun hyp3 : p s h h' =>
        have hyp4 : ∃ s h h', p s h h' := ⟨ s , ⟨ h , ⟨h', hyp3⟩ ⟩ ⟩
        show False from hyp1 hyp4
      show False from f hyp2)

def dne {p : Prop} (hyp : ¬¬p) : p :=
  byContradiction
    (fun hyp1 : ¬p =>
     show False from hyp hyp1)

def dna {p : Prop} (hp : p) : ¬¬p :=
  λ hnp => False.elim (hnp hp)

theorem dne_equivalence {p : Prop}: ¬¬p ↔ p := by
  apply Iff.intro
  case mp =>  intro nnp; exact (dne nnp)
  case mpr => intro p; exact (dna p)


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

theorem forall_n_implies_n_exists {p : α → Prop} : (∀ x , ¬ p x) → ¬(∃ x , p x) := by 
  intro for_all
  intro ⟨ x, p_x ⟩
  have not_p_x := for_all x
  exact not_p_x p_x

theorem pp_imp_nn {A B : Prop} : (A → B) ↔ ((¬B) → (¬A)) := by
  apply Iff.intro
  case mp  => 
    intro a_to_b
    intro not_b 
    intro a
    have b := a_to_b a
    exact not_b b
  case mpr =>
    intro nb_to_na
    intro a 
    apply byContradiction (
      λ not_b => by
      have not_a := nb_to_na not_b
      exact not_a a
    )

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
    apply byContradiction (
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
    have nnb := (dna b)
    exact nnb_to_na nnb
  case mpr =>
    intro b_to_na
    intro a 
    apply byContradiction (
      λ nnb => by
      have not_a := b_to_na (dne nnb)
      exact not_a a
    )


theorem n_imp {P Q : Prop} : ((¬ P) → Q) ↔ (P ∨ Q) := by
  apply Iff.intro
  case mp  =>
    intro not_p_imp_q
    have p_or_not_p := em P
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
    
theorem n_forall_implies_exists_n {p : α → Prop} : ¬(∀ x , p x) → (∃ x , ¬ p x) := by 
  conv =>
    lhs
    rhs

    --apply forall_implies_n_exists_n


  sorry

a → b 
a → ¬b


  


theorem exists_same_as_forall {p : α → Prop} : (∃ x , ¬ p x) ↔ (¬ ∀ x , p x) := by 
  apply Iff.intro
  case mp => apply exists_n_implies_n_forall
  case mpr => sorry
  
    
  
    


theorem sd {h h' : Heap} : ((dom h) = (dom h')) = same_domains h h' := by apply rfl
--theorem dd1 {p : Store → Heap → Heap → Prop}: ¬ (∀ (s : Store) (h h' : Heap) , ¬ (p s h h')) := by
   --forall_to_exists

/-
theorem diff_domains : ¬ (∀ (s : Store) (h h' : Heap) , ¬ ((dom h) = (dom h'))) := by
  -- p := λ (s : Store) (h h' : Heap) => ¬ (dom h) = (dom h')
  conv =>
    rhs
    intro s
    conv => 
      intro h
      conv => 
        intro h'
        rhs
        apply sd
  admit    
  --revert      

  --apply forall_to_exists
        

      

    


theorem domain_exact_literal { b : Bool} : ¬ (∀ s h h' , (∃ s1 h1 , (asrt (literal b) s1 h1)) ∧ (asrt (literal b) s h) ∧ (asrt (literal b) s h') → (dom h) = (dom h')):= by
    simp [asrt]
    cases b with 
    | true => {
      simp [e_true]
      apply byContradiction (
        λ x : ¬¬ (∀ s h h' , (dom h) = (dom h')) => show false by

      )
    }

    | false => sorry

theorem domain_exact {q : Asrt} : (∀ s h h' , (∃ s1 h1 , (asrt q s1 h1)) ∧ (asrt q s h) ∧ (asrt q s h') → (dom h) = (dom h')) := by {
  sorry
}
-/