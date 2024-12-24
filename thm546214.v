Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546214_term_abbrevs.
Require Import thm546186_spec.
Lemma lem546210 : term0.
Proof. exact (proj1 (@lem546186)). Qed.
Lemma lem546211 (m : nat) : term1 m.
Proof. exact (@lem546210 m). Qed.
Lemma lem546212 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem546213 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem546212 m) (@lem546211 m)). Qed.
Lemma lem546214 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem546213 m n). Qed.
