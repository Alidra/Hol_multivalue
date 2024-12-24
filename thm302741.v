Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302741_term_abbrevs.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm302535_spec.
Require Import thm302536_spec.
Require Import thm80550_spec.
Lemma lem302712 : term0 = term1.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem302713 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302714 : term2 = term3.
Proof. exact (MK_COMB (@lem302713) (@lem302712)). Qed.
Lemma lem302715 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem302716 : (term0 = (NUMERAL 0)) = (term1 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem302714) (@lem302715)). Qed.
Lemma lem302718 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem302536 n (@lem302535 n)). Qed.
Lemma lem302719 : (term1 = (NUMERAL 0)) = False.
Proof. exact (@lem302718 term4). Qed.
Lemma lem302720 : (term0 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem302716) (@lem302719)). Qed.
Lemma lem302721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem302722 : term5 = (or False).
Proof. exact (MK_COMB (@lem302721) (@lem302720)). Qed.
Lemma lem302725 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem302726 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem302722) (@lem302725 m n)). Qed.
Lemma lem302728 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem302729 (m : nat) (n : nat) : (term7 m n) = (m = n).
Proof. exact (@lem302728 (m = n)). Qed.
Lemma lem302732 (m : nat) (n : nat) : (term6 m n) = (m = n).
Proof. exact (TRANS (@lem302726 m n) (@lem302729 m n)). Qed.
Lemma lem302733 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem302734 (m : nat) (n : nat) : ((m = n) = (term6 m n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem302733 m n) (@lem302732 m n)). Qed.
Lemma lem302736 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem302737 (x : Prop) : (x = x) = True.
Proof. exact (@lem302736 Prop x). Qed.
Lemma lem302738 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem302737 (m = n)). Qed.
Lemma lem302739 (m : nat) (n : nat) : ((m = n) = (term6 m n)) = True.
Proof. exact (TRANS (@lem302734 m n) (@lem302738 m n)). Qed.
Lemma lem302740 (m : nat) (n : nat) : True = ((m = n) = (term6 m n)).
Proof. exact (SYM (@lem302739 m n)). Qed.
Lemma lem302741 (m : nat) (n : nat) : (m = n) = (term6 m n).
Proof. exact (EQ_MP (@lem302740 m n) (@lem0)). Qed.
