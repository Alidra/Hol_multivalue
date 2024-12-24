Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513173_term_abbrevs.
Require Import thm513161_spec.
Lemma lem513169 : term0.
Proof. exact (proj1 (@lem513161)). Qed.
Lemma lem513170 (m : nat) : term1 m.
Proof. exact (@lem513169 m). Qed.
Lemma lem513171 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem513172 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem513171 m) (@lem513170 m)). Qed.
Lemma lem513173 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem513172 m n). Qed.
