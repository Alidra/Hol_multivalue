Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1071695_term_abbrevs.
Require Import thm1071345_spec.
Require Import thm1071681_spec.
Lemma lem1071682 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (term1 A) = (term2 A CONS').
Proof. exact (SYM (@lem1071345 A CONS' h1)). Qed.
Lemma lem1071683 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (@cons A) = (term2 A CONS').
Proof. exact (TRANS (@lem1071681 A) (@lem1071682 A CONS' h1)). Qed.
Lemma lem1071684 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1071685 {A : Type'} (a0 : A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (@cons A a0) = (term3 A CONS' a0).
Proof. exact (MK_COMB (@lem1071683 A CONS' h1) (@lem1071684 A a0)). Qed.
Lemma lem1071686 {A : Type'} (CONS' : type1399 A) (a0 : A) : (term3 A CONS' a0) = (term4 A CONS' a0).
Proof. exact (eq_refl (term3 A CONS' a0)). Qed.
Lemma lem1071687 {A : Type'} (a0 : A) : (term5 A a0) = (term5 A a0).
Proof. exact (eq_refl (term5 A a0)). Qed.
Lemma lem1071688 {A : Type'} (CONS' : type1399 A) (a0 : A) : ((@cons A a0) = (term3 A CONS' a0)) = ((@cons A a0) = (term4 A CONS' a0)).
Proof. exact (MK_COMB (@lem1071687 A a0) (@lem1071686 A CONS' a0)). Qed.
Lemma lem1071689 {A : Type'} (a0 : A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (@cons A a0) = (term4 A CONS' a0).
Proof. exact (EQ_MP (@lem1071688 A CONS' a0) (@lem1071685 A a0 CONS' h1)). Qed.
Lemma lem1071690 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1071691 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (@cons A a0 a1) = (term6 A CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071689 A a0 CONS' h1) (@lem1071690 A a1)). Qed.
Lemma lem1071692 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : list A) : (term6 A CONS' a0 a1) = (term7 A CONS' a0 a1).
Proof. exact (eq_refl (term6 A CONS' a0 a1)). Qed.
Lemma lem1071693 {A : Type'} (a0 : A) (a1 : list A) : (term8 A a0 a1) = (term8 A a0 a1).
Proof. exact (eq_refl (term8 A a0 a1)). Qed.
Lemma lem1071694 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : list A) : ((@cons A a0 a1) = (term6 A CONS' a0 a1)) = ((@cons A a0 a1) = (term7 A CONS' a0 a1)).
Proof. exact (MK_COMB (@lem1071693 A a0 a1) (@lem1071692 A CONS' a0 a1)). Qed.
Lemma lem1071695 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : (@cons A a0 a1) = (term7 A CONS' a0 a1).
Proof. exact (EQ_MP (@lem1071694 A CONS' a0 a1) (@lem1071691 A a0 a1 CONS' h1)). Qed.
