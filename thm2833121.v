Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2833121_term_abbrevs.
Lemma lem2833121 (a : int) (d : int) (b : int) : (term0 a d b) = ((term1 d a b) = (term2 a d b)).
Proof. exact (eq_refl (term0 a d b)). Qed.
