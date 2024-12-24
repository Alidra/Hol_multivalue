Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513141_term_abbrevs.
Require Import PRE_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem513127 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513128 : (NUMERAL 0) = 0.
Proof. exact (@lem513127 0). Qed.
Lemma lem513129 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513130 : term0 = (Nat.pred 0).
Proof. exact (MK_COMB (@lem513129) (@lem513128)). Qed.
Lemma lem513131 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513132 : term1 = term2.
Proof. exact (MK_COMB (@lem513131) (@lem513130)). Qed.
Lemma lem513134 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513135 : (NUMERAL 0) = 0.
Proof. exact (@lem513134 0). Qed.
Lemma lem513136 : (term0 = (NUMERAL 0)) = ((Nat.pred 0) = 0).
Proof. exact (MK_COMB (@lem513132) (@lem513135)). Qed.
Lemma lem513137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513138 : term3 = term4.
Proof. exact (MK_COMB (@lem513137) (@lem513136)). Qed.
Lemma lem513139 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem513140 : term6 = term7.
Proof. exact (MK_COMB (@lem513138) (@lem513139)). Qed.
Lemma lem513141 : term7.
Proof. exact (EQ_MP (@lem513140) (@lem76888)). Qed.
