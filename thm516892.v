Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516892_term_abbrevs.
Require Import thm516884_spec.
Lemma lem516888 : term0.
Proof. exact (proj2 (@lem516884)). Qed.
Lemma lem516889 (m : nat) : term1 m.
Proof. exact (@lem516888 m). Qed.
Lemma lem516890 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem516891 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem516890 m) (@lem516889 m)). Qed.
Lemma lem516892 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem516891 m n). Qed.
