Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338271_term_abbrevs.
Require Import INT_OF_NUM_LE_spec.
Lemma lem2338268 (m : nat) : term0 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2338269 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2338270 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2338269 m) (@lem2338268 m)). Qed.
Lemma lem2338271 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2338270 m n). Qed.
