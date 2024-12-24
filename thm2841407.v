Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841407_term_abbrevs.
Require Import thm2841270_spec.
Lemma lem2841404 (m : nat) : term0 m.
Proof. exact (@lem2841270 m). Qed.
Lemma lem2841405 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2841406 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2841405 m) (@lem2841404 m)). Qed.
Lemma lem2841407 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2841406 m n). Qed.
