Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538882_term_abbrevs.
Require Import thm538854_spec.
Lemma lem538878 : term0.
Proof. exact (proj1 (@lem538854)). Qed.
Lemma lem538879 (m : nat) : term1 m.
Proof. exact (@lem538878 m). Qed.
Lemma lem538880 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem538881 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem538880 m) (@lem538879 m)). Qed.
Lemma lem538882 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem538881 m n). Qed.
