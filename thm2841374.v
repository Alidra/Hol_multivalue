Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841374_term_abbrevs.
Require Import thm2841350_spec.
Lemma lem2841371 (m : nat) : term0 m.
Proof. exact (@lem2841350 m). Qed.
Lemma lem2841372 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2841373 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2841372 m) (@lem2841371 m)). Qed.
Lemma lem2841374 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2841373 m n). Qed.
