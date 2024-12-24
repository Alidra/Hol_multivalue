Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841401_term_abbrevs.
Require Import thm2841284_spec.
Lemma lem2841398 (m : nat) : term0 m.
Proof. exact (@lem2841284 m). Qed.
Lemma lem2841399 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2841400 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2841399 m) (@lem2841398 m)). Qed.
Lemma lem2841401 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2841400 m n). Qed.
