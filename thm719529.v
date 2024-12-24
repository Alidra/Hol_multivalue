Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm719529_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem719465 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem719466 : term1.
Proof. exact (proj2 (@lem719465)). Qed.
Lemma lem719467 : term2.
Proof. exact (proj2 (@lem719466)). Qed.
Lemma lem719468 : term3.
Proof. exact (proj2 (@lem719467)). Qed.
Lemma lem719469 : term4.
Proof. exact (proj2 (@lem719468)). Qed.
Lemma lem719501 : term5.
Proof. exact (proj1 (@lem719469)). Qed.
Lemma lem719502 (n : nat) : term6 n.
Proof. exact (@lem719501 n). Qed.
Lemma lem719503 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem719526 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem719503 n) (@lem719502 n)). Qed.
Lemma lem719527 : term8 = term9.
Proof. exact (@lem719526 (BIT1 0)). Qed.
Lemma lem719528 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem719529 : term10 = term11.
Proof. exact (MK_COMB (@lem719528) (@lem719527)). Qed.
