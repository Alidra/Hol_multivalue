Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246867_term_abbrevs.
Require Import thm1246862_spec.
Lemma lem1246863 : term0.
Proof. exact (proj2 (@lem1246862)). Qed.
Lemma lem1246864 (m : nat) : term1 m.
Proof. exact (@lem1246863 m). Qed.
Lemma lem1246865 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1246866 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1246865 m) (@lem1246864 m)). Qed.
Lemma lem1246867 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1246866 m n). Qed.
