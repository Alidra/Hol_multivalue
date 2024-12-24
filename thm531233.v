Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531233_term_abbrevs.
Require Import thm531176_spec.
Lemma lem531200 : term0.
Proof. exact (proj1 (@lem531176)). Qed.
Lemma lem531201 (m : nat) : term1 m.
Proof. exact (@lem531200 m). Qed.
Lemma lem531202 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem531203 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem531202 m) (@lem531201 m)). Qed.
Lemma lem531204 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem531203 m n). Qed.
Lemma lem531205 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem531232 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem531205 m n) (@lem531204 m n)). Qed.
Lemma lem531233 : term6 = term7.
Proof. exact (@lem531232 (BIT1 0) (BIT1 0)). Qed.
