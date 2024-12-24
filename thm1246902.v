Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246902_term_abbrevs.
Require Import LT_EXISTS_spec.
Lemma lem1246899 (m : nat) : term0 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1246900 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1246901 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1246900 m) (@lem1246899 m)). Qed.
Lemma lem1246902 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1246901 m n). Qed.
