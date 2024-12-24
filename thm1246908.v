Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246908_term_abbrevs.
Require Import thm1246898_spec.
Lemma lem1246905 (m : nat) : term0 m.
Proof. exact (@lem1246898 m). Qed.
Lemma lem1246906 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1246907 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1246906 m) (@lem1246905 m)). Qed.
Lemma lem1246908 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1246907 m n). Qed.
