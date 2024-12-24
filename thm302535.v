Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302535_term_abbrevs.
Require Import NOT_SUC_spec.
Lemma lem302533 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem302534 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem302535 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem302534 n) (@lem302533 n)). Qed.
