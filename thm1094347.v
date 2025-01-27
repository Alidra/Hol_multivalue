Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094347_term_abbrevs.
Lemma lem1094347 {A : Type'} (P : type1143 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
