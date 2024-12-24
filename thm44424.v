Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm44424_term_abbrevs.
Require Import PAIR_EXISTS_THM_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem44418 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem44419 {A B : Type'} : (@ex (A -> B -> Prop)) = (term1 A B).
Proof. exact (@lem44418 (type1413 A B)). Qed.
Lemma lem44420 {A B : Type'} : (term2 A B) = (term2 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem44421 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem44419 A B) (@lem44420 A B)). Qed.
Lemma lem44422 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (eq_refl (term4 A B)). Qed.
Lemma lem44423 {A B : Type'} : (term3 A B) = (term5 A B).
Proof. exact (TRANS (@lem44421 A B) (@lem44422 A B)). Qed.
Lemma lem44424 {A B : Type'} : term5 A B.
Proof. exact (EQ_MP (@lem44423 A B) (@lem44416 A B)). Qed.
