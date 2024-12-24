Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246847_term_abbrevs.
Require Import NOT_SUC_spec.
Lemma lem1246845 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1246846 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1246847 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1246846 n) (@lem1246845 n)). Qed.
