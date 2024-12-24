Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513091_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem513082 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513083 : (NUMERAL 0) = 0.
Proof. exact (@lem513082 0). Qed.
Lemma lem513084 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem513085 (n : nat) : ((S n) = (NUMERAL 0)) = ((S n) = 0).
Proof. exact (MK_COMB (@lem513084 n) (@lem513083)). Qed.
Lemma lem513086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem513087 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem513086) (@lem513085 n)). Qed.
Lemma lem513088 : term3 = term4.
Proof. exact (fun_ext (fun n : nat => @lem513087 n)). Qed.
Lemma lem513089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513090 : term5 = term6.
Proof. exact (MK_COMB (@lem513089) (@lem513088)). Qed.
Lemma lem513091 : term6.
Proof. exact (EQ_MP (@lem513090) (@lem75570)). Qed.
