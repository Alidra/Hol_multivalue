Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302577_term_abbrevs.
Require Import EQ_ADD_RCANCEL_spec.
Lemma lem302571 (m : nat) : term0 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem302572 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem302573 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem302572 m) (@lem302571 m)). Qed.
Lemma lem302574 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem302573 m n). Qed.
Lemma lem302575 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem302576 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem302575 m n) (@lem302574 m n)). Qed.
Lemma lem302577 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem302576 m n p). Qed.
