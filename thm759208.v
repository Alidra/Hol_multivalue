Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm759208_term_abbrevs.
Lemma lem759208 (n : nat) : (term0 n) = ((term1 n) = (term2 n)).
Proof. exact (eq_refl (term0 n)). Qed.
