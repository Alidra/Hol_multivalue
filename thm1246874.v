Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246874_term_abbrevs.
Require Import thm1246862_spec.
Lemma lem1246870 : term0.
Proof. exact (proj1 (@lem1246862)). Qed.
Lemma lem1246871 (m : nat) : term1 m.
Proof. exact (@lem1246870 m). Qed.
Lemma lem1246872 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1246873 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1246872 m) (@lem1246871 m)). Qed.
Lemma lem1246874 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1246873 m n). Qed.
