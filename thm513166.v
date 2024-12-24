Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513166_term_abbrevs.
Require Import thm513161_spec.
Lemma lem513162 : term0.
Proof. exact (proj2 (@lem513161)). Qed.
Lemma lem513163 (m : nat) : term1 m.
Proof. exact (@lem513162 m). Qed.
Lemma lem513164 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem513165 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem513164 m) (@lem513163 m)). Qed.
Lemma lem513166 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem513165 m n). Qed.
