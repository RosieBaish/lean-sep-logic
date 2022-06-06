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

@[simp] def dom {A B : Type}  (p : Partial A B) : Subset A := λ a => (p a) ≠ none

def disjoint {A B : Type} (p1 p2 : Partial A B) : Prop :=
set_intersect (dom p1) (dom p2) = empty_set

noncomputable def union {A : Type} (p1 p2 : Partial A A) : Partial A A :=
λ x => if (p1 x) = none then (p2 x) else (p1 x)

@[simp]
def in_partial {A B : Type} (a : A) (p : Partial A B) : Prop := (p a).isSome

@[simp]
def asrt (q : Asrt) (s : Store) (h : Heap) : Prop := match q with
  | literal b => b
  | emp       => ∀ x , (dom h) x = false
  | singleton v1 v2 => (Option.bind (s v1) h) = (s v2) ∧ (in_partial v1 s) ∧ (in_partial v2 s) ∧ ∀ x , (dom h) x = (some x = (s v1))
  | sep q1 q2 => ∃ h1 h2 , (asrt q1 s h1) ∧ (asrt q2 s h2) ∧ (disjoint h1 h2) ∧ h = (union h1 h2)
  | sepimp q1 q2 => ∀ h' , (asrt q1 s h') ∧ disjoint h h' -> asrt q2 s (union h h')

def aw (q : Asrt) (s : Store) (h : Heap) (m : Subset Nat) : Prop :=
  (if ((dom h) = m) then (asrt q s h) else False)

@[simp]
def domain_exact_impl (q : Asrt) : Prop := match q with
  | literal b     => False
  | emp           => True
  | singleton _ _ => True
  | sep q1 q2     => (domain_exact_impl q1) ∧ (domain_exact_impl q2) ∧ ∃ s h m , aw (sep q1 q2) s h m
  | sepimp q1 q2  => (domain_exact_impl q1) ∧ (domain_exact_impl q2)

@[simp]
def domain_exact_theory (q : Asrt) : Prop := (
  (∃ s1 h1 m1 , (aw q s1 h1 m1)) ∧
  (∀ s ,
    (∃ h m, (aw q s h m)) →
    (∃ m , ∀ h h' : Heap ,
      (dom h = m) ∧ (dom h' = m) →
      ((aw q s h m) ∧
       (aw q s h' m)
      )
    )
  )
)

mutual
theorem domain_exact_correct_literal: ∀ b , (domain_exact_impl (literal b)) ↔ (domain_exact_theory (literal b)) := by {
  simp;-- [aw];
  intro b;
  have s  : Store := (λ (n : Nat) => none);
  have h  : Heap := (λ (n : Nat) => none);
  have h' : Heap := (λ (n : Nat) => some n);
  match b with
  | true => {
    rw [de_morgan];
    apply Or.inr;
    intro negation;
    have e : (∃ h m, aw (literal true) s h m) := (Exists.intro h (Exists.intro (dom h) (by simp [aw])));
    have ⟨ m , n ⟩ := negation s e;
    have n1 := n (λ (n : Nat) => none) (λ (n : Nat) => some n);
-- (by simp [aw]) (by simp [aw]) 0;
    simp [aw] at n1;
    revert n1;
    
    --exact (n 0);
    sorry;
  }
  | false => {
    have e : (∃ s h m, aw (literal true) s h m) := (Exists.intro s (Exists.intro h (Exists.intro (dom h) (by simp [aw]))));
    simp [aw];
    intro ⟨ s , h , h1 , hyp⟩;
    contradiction;
  }
}

theorem domain_exact_correct_emp : (domain_exact_impl emp) ↔ (domain_exact_theory emp) := by {
  simp;
  apply And.intro;
  case left => {
    exists (λ (n : Nat) => none);
    exists (λ (n : Nat) => none);
    simp [aw];
    exists (λ n => False);
    simp;
  }
  case right => {
    simp [aw];
    intro s _ h h';
    intro ⟨ l , r ⟩;
    intro x;
    rw [(l x)];
    rw [(r x)];
    simp;
  }
}

theorem domain_exact_correct_singleton v1 v2 : (domain_exact_impl (singleton v1 v2)) ↔ (domain_exact_theory (singleton v1 v2)) := by {
  simp [aw];
  apply And.intro;
  case left => {
    exists (λ (n : Nat) => some n);
    exists (λ (n : Nat) => if n = v1 then some v2 else none);
    simp;
    simp [Option.bind];
    simp [Option.isSome];
    simp [Option.isNone];
    exists (fun a => ¬(if a = v1 then some v2 else none) = none);
    simp;
    intro x;
    apply Or.elim (Classical.em (x = v1));
    case left  => intro eq; simp [eq];
    case right => intro neq; simp [neq];
  }
  case right => {
    intro s _ h h';
    intro ⟨ ⟨ _, ⟨ _, ⟨ _ , l ⟩ ⟩ ⟩ , ⟨ _ ,  ⟨ _ , ⟨ _ , r ⟩ ⟩ ⟩ ⟩;
    intro x;
    rw [l, r];
    simp;
  }
}

theorem iff_not (A B : Prop) : (¬A ↔ ¬B) ↔ (A ↔ B) := by {
  cases Classical.em A with
  | inl a  => cases Classical.em B with
              | inl b  => simp [ a,  b];
              | inr nb => simp [ a, nb];
  | inr na => cases Classical.em B with
              | inl b  => simp [na,  b];
              | inr nb => simp [na, nb];
}

theorem domain_exact_correct_sep q1 q2 : domain_exact_impl (sep q1 q2) ↔ domain_exact_theory (sep q1 q2) := by {
  apply Iff.intro;
  case mp  => {
    simp [domain_exact_correct, aw];
    
    intro ⟨ ⟨ ⟨ q1s , ⟨ q1h , q1m, q1a ⟩ ⟩ , q1_de ⟩ , ⟨ ⟨ q2s , ⟨ q2h , q2a ⟩ ⟩ , q2_de ⟩ , ⟨ s , h, m, z⟩⟩ ;--⟨ s , h, h1, h2, conj ⟩⟩;
    apply And.intro;
    case left => {
      exists s;
      exists h;
      exists m;
      exact z;
    }
    case right => {
      intro s;
      intro ⟨ h1, m1, z1⟩;
      intro h h';
      intro ⟨ ⟨ c3h1 , c3h2 , c31 , c32 , c33 , c34 ⟩ , ⟨ c4h1 , c4h2 , c41 , c42 , c43 , c44 ⟩ ⟩;
      intro x;
      have q1 := q1_de s (Exists.intro c3h1 (Exists.intro (fun a => ¬c3h1 a = none) (by simp; apply c31))) c3h1 c4h1 (And.intro c31 c41) x;
      have q2 := q2_de s (Exists.intro c3h2 (Exists.intro (fun a => ¬c3h2 a = none) (by simp; apply c32))) c3h2 c4h2 (And.intro c32 c42) x;
      rw [c34, c44, union, union];
      simp [iff_not];
      simp [iff_not] at q2;
      simp [iff_not] at q1;
      revert q1 q2;
      match (c3h1 x) with
      | some x1 => {
        match (c4h1 x) with
        | some x2 => simp;
        | none    => simp;
      }
      | none   => {
      match (c4h1 x) with
        | some x2 => simp;
        | none    => simp; intro; assumption;
      }
    }
  }
  case mpr => {
    simp;
    intro ⟨ ⟨ s, h , m, app ⟩ , b⟩;
    have as := app;
    simp [aw] at as;
    have temp : (fun a => ¬h a = none) = m := by {
      revert as;
      split;
      case inl => intro _; assumption;
      case inr => simp;
    };

--    intro ⟨ a, ⟨ c1_s, c1_a, c1_h, c1_h1, c1_h2 , c11 , c12, c13, c14 ⟩ , c2 ⟩;
    have b1 := b s ⟨ h , m , app⟩;
    rw [aw] at app;
    simp [temp] at app;
    have ⟨ h1 , h2 , c1, c2, c3, c4⟩ := app;
    apply And.intro;
    case left => {
      simp [domain_exact_correct];
      apply And.intro;
      case left => {
        exists s;
        exists h1;
        exists (dom h1);
        simp [aw];
        exact c1;
      }
      case right => {
        intro s ⟨ a , m , b ⟩ h h' ⟨ l , r ⟩ x;
        simp [aw] at l;
        simp [aw] at r;
        
        /-
        have c3 := (c2 c1_s) (Exists.intro c1_h (Exists.intro c1_h1 (Exists.intro c1_h2 (⟨c11, c12, c13, c14⟩)))) h h';
        have lhs : (∃ h1 h2, asrt q1 c1_s c1_h1 ∧ asrt q2 c1_s c1_h2 ∧ disjoint c1_h1 c1_h2 ∧ c1_h = union c1_h1 c1_h2)
  := (Exists.intro c1_h1 (Exists.intro c1_h2 ⟨c11, c12, c13, c14 ⟩));
        --
      --(∃ h1 h2, asrt q1 c1_s h1 ∧ asrt q2 c1_s h2 ∧ disjoint h1 h2 ∧ h' = union h1 h2)

        have lemm1 := (λ x : Heap => asrt q1 c1_s c1_h1 ∧ asrt q2 c1_s c1_h2 ∧ disjoint c1_h1 c1_h2 ∧ c1_h = (union c1_h1 c1_h2))
        have lemm0 : lemm1 := λ x => And.intro c11 (And.intro c12 (And.intro c13 c14));
        have lemm2 := (@Exists.intro Heap  lemm1 c1_h2 (lemm0 c1_h2))
        have lemm3 := (@Exists.intro Heap (@Exists.intro Heap λ _ =>  c1_h1) c1_h);
        --have lemm := (Exists.intro c1_h (Exists.intro c1_h1 lemm1));
        have c3 := (c2 c1_s) lemm2;
        -/
        sorry;
      }
    }
    sorry;
  }
}

theorem domain_exact_correct : ∀ q , (domain_exact_impl q) ↔ (domain_exact_theory q) := by
  intro q;
  match q with
  | literal b       => exact (domain_exact_correct_literal b);
  | emp             => exact (domain_exact_correct_emp);
  | singleton v1 v2 => exact (domain_exact_correct_singleton v1 v2);
  | sep q1 q2       => sorry;
  | sepimp q1 q2    => sorry;
end
