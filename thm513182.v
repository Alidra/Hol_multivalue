Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513182_term_abbrevs.
Lemma lem513182 (n : nat) : (term0 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
