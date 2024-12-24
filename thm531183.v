Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531183_term_abbrevs.
Require Import thm531178_spec.
Lemma lem531179 : term0.
Proof. exact (proj2 (@lem531178)). Qed.
Lemma lem531180 (m : nat) : term1 m.
Proof. exact (@lem531179 m). Qed.
Lemma lem531181 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem531182 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem531181 m) (@lem531180 m)). Qed.
Lemma lem531183 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem531182 m n). Qed.
