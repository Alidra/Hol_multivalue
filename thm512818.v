Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm512818_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem512708 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem512709 : (NUMERAL 0) = 0.
Proof. exact (@lem512708 0). Qed.
Lemma lem512710 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem512711 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem512710) (@lem512709)). Qed.
Lemma lem512712 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem512713 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem512711) (@lem512712 n)). Qed.
Lemma lem512714 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512715 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem512714) (@lem512713 n)). Qed.
Lemma lem512716 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem512717 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem512715 n) (@lem512716 n)). Qed.
Lemma lem512718 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem512717 n)). Qed.
Lemma lem512719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem512720 : term6 = term7.
Proof. exact (MK_COMB (@lem512719) (@lem512718)). Qed.
Lemma lem512721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512722 : term8 = term9.
Proof. exact (MK_COMB (@lem512721) (@lem512720)). Qed.
Lemma lem512724 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem512725 : (NUMERAL 0) = 0.
Proof. exact (@lem512724 0). Qed.
Lemma lem512726 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem512727 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem512726 m) (@lem512725)). Qed.
Lemma lem512728 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512729 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem512728) (@lem512727 m)). Qed.
Lemma lem512730 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem512731 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem512729 m) (@lem512730 m)). Qed.
Lemma lem512732 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem512731 m)). Qed.
Lemma lem512733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem512734 : term15 = term16.
Proof. exact (MK_COMB (@lem512733) (@lem512732)). Qed.
Lemma lem512735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512736 : term17 = term18.
Proof. exact (MK_COMB (@lem512735) (@lem512734)). Qed.
Lemma lem512737 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem512738 : term20 = term21.
Proof. exact (MK_COMB (@lem512736) (@lem512737)). Qed.
Lemma lem512739 : term22 = term23.
Proof. exact (MK_COMB (@lem512722) (@lem512738)). Qed.
Lemma lem512740 : term23.
Proof. exact (EQ_MP (@lem512739) (@lem77629)). Qed.
Lemma lem512761 : term7.
Proof. exact (proj1 (@lem512740)). Qed.
Lemma lem512762 (n : nat) : term24 n.
Proof. exact (@lem512761 n). Qed.
Lemma lem512763 (n : nat) : (term24 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem512765 (n : nat) : term25 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem512766 (n : nat) : (term25 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem512768 (n : nat) : term26 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem512769 (n : nat) : (term26 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem512776 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512769 n) (@lem512768 n)). Qed.
Lemma lem512777 : term27 = (NUMERAL 0).
Proof. exact (@lem512776 (NUMERAL 0)). Qed.
Lemma lem512779 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512769 n) (@lem512768 n)). Qed.
Lemma lem512780 : (NUMERAL 0) = 0.
Proof. exact (@lem512779 0). Qed.
Lemma lem512781 : term27 = 0.
Proof. exact (TRANS (@lem512777) (@lem512780)). Qed.
Lemma lem512782 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512783 : term28 = (@eq nat 0).
Proof. exact (MK_COMB (@lem512782) (@lem512781)). Qed.
Lemma lem512785 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512769 n) (@lem512768 n)). Qed.
Lemma lem512786 : (NUMERAL 0) = 0.
Proof. exact (@lem512785 0). Qed.
Lemma lem512787 : (term27 = (NUMERAL 0)) = (0 = 0).
Proof. exact (MK_COMB (@lem512783) (@lem512786)). Qed.
Lemma lem512789 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512790 (x : nat) : (x = x) = True.
Proof. exact (@lem512789 nat x). Qed.
Lemma lem512791 : (0 = 0) = True.
Proof. exact (@lem512790 0). Qed.
Lemma lem512792 : (term27 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem512787) (@lem512791)). Qed.
Lemma lem512793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512794 : term29 = (and True).
Proof. exact (MK_COMB (@lem512793) (@lem512792)). Qed.
Lemma lem512798 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem512766 n) (@lem512765 n)). Qed.
Lemma lem512799 : (BIT0 0) = (Nat.add 0 0).
Proof. exact (@lem512798 0). Qed.
Lemma lem512801 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem512763 n) (@lem512762 n)). Qed.
Lemma lem512802 : (Nat.add 0 0) = 0.
Proof. exact (@lem512801 0). Qed.
Lemma lem512803 : (BIT0 0) = 0.
Proof. exact (TRANS (@lem512799) (@lem512802)). Qed.
Lemma lem512804 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512805 : term30 = (@eq nat 0).
Proof. exact (MK_COMB (@lem512804) (@lem512803)). Qed.
Lemma lem512806 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem512807 : ((BIT0 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem512805) (@lem512806)). Qed.
Lemma lem512809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512810 (x : nat) : (x = x) = True.
Proof. exact (@lem512809 nat x). Qed.
Lemma lem512811 : (0 = 0) = True.
Proof. exact (@lem512810 0). Qed.
Lemma lem512812 : ((BIT0 0) = 0) = True.
Proof. exact (TRANS (@lem512807) (@lem512811)). Qed.
Lemma lem512813 : term31 = (True /\ True).
Proof. exact (MK_COMB (@lem512794) (@lem512812)). Qed.
Lemma lem512815 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem512816 : (True /\ True) = True.
Proof. exact (@lem512815 True). Qed.
Lemma lem512817 : term31 = True.
Proof. exact (TRANS (@lem512813) (@lem512816)). Qed.
Lemma lem512818 : True = term31.
Proof. exact (SYM (@lem512817)). Qed.
