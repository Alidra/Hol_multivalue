Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17991_term_abbrevs.
Require Import thm17976_spec.
Require Import thm17977_spec.
Lemma lem17980 {A B : Type'} (t : A -> B) : t = (term0 A B t).
Proof. exact (EQ_MP (@lem17977 A B t) (@lem17976 A B t)). Qed.
Lemma lem17981 {A : Type'} (t : A -> Prop) : t = (term1 A t).
Proof. exact (@lem17980 A Prop t). Qed.
Lemma lem17982 {A : Type'} (P : A -> Prop) : P = (term1 A P).
Proof. exact (@lem17981 A P). Qed.
Lemma lem17983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem17984 {A : Type'} (P : A -> Prop) : (all P) = (term2 A P).
Proof. exact (MK_COMB (@lem17983 A) (@lem17982 A P)). Qed.
Lemma lem17985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17986 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (MK_COMB (@lem17985) (@lem17984 A P)). Qed.
Lemma lem17987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17988 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (MK_COMB (@lem17987) (@lem17986 A P)). Qed.
Lemma lem17989 {A : Type'} (P : A -> Prop) : (term7 A P) = (term7 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem17990 {A : Type'} (P : A -> Prop) : ((term3 A P) = (term7 A P)) = ((term4 A P) = (term7 A P)).
Proof. exact (MK_COMB (@lem17988 A P) (@lem17989 A P)). Qed.
Lemma lem17991 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term7 A P)) = ((term3 A P) = (term7 A P)).
Proof. exact (SYM (@lem17990 A P)). Qed.
