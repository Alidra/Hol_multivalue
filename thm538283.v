Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538283_term_abbrevs.
Require Import thm538262_spec.
Lemma lem538263 : term0.
Proof. exact (proj2 (@lem538262)). Qed.
Lemma lem538279 : term1.
Proof. exact (proj1 (@lem538263)). Qed.
Lemma lem538280 (m : nat) : term2 m.
Proof. exact (@lem538279 m). Qed.
Lemma lem538281 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem538282 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem538281 m) (@lem538280 m)). Qed.
Lemma lem538283 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem538282 m n). Qed.
