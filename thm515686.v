Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515686_term_abbrevs.
Lemma lem515686 (m : nat) : (term0 m) = ((Nat.pow m 0) = (BIT1 0)).
Proof. exact (eq_refl (term0 m)). Qed.
