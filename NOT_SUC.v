Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_SUC_term_abbrevs.
Require Import thm0_spec.
Require Import thm72734_spec.
Require Import thm75559_spec.
Lemma lem75562 : 0 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem75559) (@lem0)). Qed.
Lemma lem75563 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem75564 (n : nat) : ((S n) = 0) = ((S n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem75563 n) (@lem75562)). Qed.
Lemma lem75565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem75566 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem75565) (@lem75564 n)). Qed.
Lemma lem75567 : term3 = term4.
Proof. exact (fun_ext (fun n : nat => @lem75566 n)). Qed.
Lemma lem75568 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75569 : term5 = term6.
Proof. exact (MK_COMB (@lem75568) (@lem75567)). Qed.
Lemma lem75570 : term6.
Proof. exact (EQ_MP (@lem75569) (@lem72734)). Qed.
