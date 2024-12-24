Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302555_term_abbrevs.
Require Import EQ_MULT_LCANCEL_spec.
Lemma lem302549 (m : nat) : term0 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem302550 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem302551 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem302550 m) (@lem302549 m)). Qed.
Lemma lem302552 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem302551 m n). Qed.
Lemma lem302553 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem302554 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem302553 m n) (@lem302552 m n)). Qed.
Lemma lem302555 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem302554 m n p). Qed.
