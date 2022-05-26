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

-/
/-
def pred (b : Bool) (s : Store) (h h' : Heap) : Prop := (∃ s1 h1 , (asrt (literal b) s1 h1)) ∧ (asrt (literal b) s h) ∧ (asrt (literal b) s h') → (dom h) = (dom h')


theorem domain_exact_literal1 (p : Store → Heap → Heap → Prop) : ¬(∀ s h h' , (p s h h')) := by {

}
-/

theorem domain_exact_literal { b : Bool} : ¬((∃ s1 h1 , (asrt (literal b) s1 h1)) ∧ (∀ s h h' , (asrt (literal b) s h) ∧ (asrt (literal b) s h') → equal (dom h) (dom h'))) := by {
  have s  : Store := (λ (n : Nat) => none);
  have h  : Heap := (λ (n : Nat) => none);
  have h' : Heap := (λ (n : Nat) => some n);
  simp [asrt];
  simp [equal];
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
/-
  rw [exists_same_as_forall_3]
  have s  : Store := (λ (n : Nat) => none);
  have h  : Heap := (λ (n : Nat) => none);
  have h' : Heap := (λ (n : Nat) => some n);
  apply Exists.intro s;
  apply Exists.intro h;
  apply Exists.intro h';
  rw[not_imp];
-/
}

/-
    simp [asrt]
    cases b with
    | true => {
      simp [e_true]
      apply byContradiction (
        λ x : ¬¬ (∀ s h h' , (dom h) = (dom h')) => show false by

      )
    }

    | false => sorry
-/
/-
theorem domain_exact {q : Asrt} : (∀ s h h' , (∃ s1 h1 , (asrt q s1 h1)) ∧ (asrt q s h) ∧ (asrt q s h') → (dom h) = (dom h')) := by {
  sorry
}
-/
