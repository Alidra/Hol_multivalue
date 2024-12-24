Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400767_term_abbrevs.
Require Import IN_INSERT_spec.
Lemma lem5400761 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5400762 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5400763 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5400762 A x) (@lem5400761 A x)). Qed.
Lemma lem5400764 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem5400763 A x y). Qed.
Lemma lem5400765 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem5400766 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem5400765 A y x) (@lem5400764 A x y)). Qed.
Lemma lem5400767 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem5400766 A y x s). Qed.
