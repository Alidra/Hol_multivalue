Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538868_term_abbrevs.
Require Import thm538855_spec.
Lemma lem538856 : term0.
Proof. exact (proj2 (@lem538855)). Qed.
Lemma lem538864 : term1.
Proof. exact (proj1 (@lem538856)). Qed.
Lemma lem538865 (m : nat) : term2 m.
Proof. exact (@lem538864 m). Qed.
Lemma lem538866 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem538867 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem538866 m) (@lem538865 m)). Qed.
Lemma lem538868 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem538867 m n). Qed.
