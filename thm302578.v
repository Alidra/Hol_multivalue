Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302578_term_abbrevs.
Lemma lem302578 (p : nat) (m : nat) (n : nat) : (term0 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term0 m n p)). Qed.
