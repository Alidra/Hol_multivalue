Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_REFL_term_abbrevs.
Lemma lem299 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem304 {A : Type'} : term0 A.
Proof. exact (fun x : A => @lem299 A x). Qed.
