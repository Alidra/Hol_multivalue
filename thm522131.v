Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522131_term_abbrevs.
Require Import NOT_LE_spec.
Lemma lem522128 (m : nat) : term0 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem522129 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522130 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522129 m) (@lem522128 m)). Qed.
Lemma lem522131 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522130 m n). Qed.
