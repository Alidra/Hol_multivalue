Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_EQ_0_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import INT_NEG_EQ_0_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import REAL_INV_EQ_0_spec.
Require Import REAL_POW_EQ_0_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3179558 (m : nat) : term0 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem3179559 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3179560 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3179559 m) (@lem3179558 m)). Qed.
Lemma lem3179561 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3179560 m n). Qed.
Lemma lem3179562 (m : nat) (n : nat) : (term2 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3179564 (x : real) : term3 x.
Proof. exact (@lem1630283 x). Qed.
Lemma lem3179565 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem3179566 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem3179565 x) (@lem3179564 x)). Qed.
Lemma lem3179567 (x : real) (n : nat) : term5 x n.
Proof. exact (@lem3179566 x n). Qed.
Lemma lem3179568 (x : real) (n : nat) : (term5 x n) = (((real_pow x n) = term6) = (term7 x n)).
Proof. exact (eq_refl (term5 x n)). Qed.
Lemma lem3179570 (x : int) : term8 x.
Proof. exact (@lem2306427 x). Qed.
Lemma lem3179571 (x : int) : (term8 x) = (((int_neg x) = term9) = (x = term9)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem3179573 (x : real) : term10 x.
Proof. exact (@lem1588944 x). Qed.
Lemma lem3179574 (x : real) : (term10 x) = (((real_inv x) = term6) = (x = term6)).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem3179576 : term11.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3179577 (x : real) : term12 x.
Proof. exact (@lem3179576 x). Qed.
Lemma lem3179578 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem3179579 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem3179578 x) (@lem3179577 x)). Qed.
Lemma lem3179580 (x : real) (n : nat) : term14 x n.
Proof. exact (@lem3179579 x n). Qed.
Lemma lem3179581 (x : real) (n : nat) : (term14 x n) = ((term15 x n) = (term16 x n)).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem3179583 : term17.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3179584 (x : real) : term18 x.
Proof. exact (@lem3179583 x). Qed.
Lemma lem3179585 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem3179586 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem3179585 x) (@lem3179584 x)). Qed.
Lemma lem3179587 (x : real) (n : nat) : term20 x n.
Proof. exact (@lem3179586 x n). Qed.
Lemma lem3179588 (x : real) (n : nat) : (term20 x n) = ((term21 x n) = (real_pow x n)).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem3179590 (P : int -> Prop) : term22 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3179591 (P : int -> Prop) : (term22 P) = ((term23 P) = (term24 P)).
Proof. exact (eq_refl (term22 P)). Qed.
Lemma lem3179604 (P : int -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem3179591 P) (@lem3179590 P)). Qed.
Lemma lem3179605 (x : real) : (term25 x) = (term26 x).
Proof. exact (@lem3179604 (term27 x)). Qed.
Lemma lem3179606 (x : real) (n : int) : (term28 x n) = (((real_zpow x n) = term6) = (term29 x n)).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem3179607 (x : real) : (term30 x) = (term27 x).
Proof. exact (fun_ext (fun n : int => @lem3179606 x n)). Qed.
Lemma lem3179608 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179609 (x : real) : (term25 x) = (term31 x).
Proof. exact (MK_COMB (@lem3179608) (@lem3179607 x)). Qed.
Lemma lem3179610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179611 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem3179610) (@lem3179609 x)). Qed.
Lemma lem3179612 (x : real) (n : nat) : (term34 x n) = (((term21 x n) = term6) = (term35 x n)).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem3179613 (x : real) : (term36 x) = (term37 x).
Proof. exact (fun_ext (fun n : nat => @lem3179612 x n)). Qed.
Lemma lem3179614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179615 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem3179614) (@lem3179613 x)). Qed.
Lemma lem3179616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179617 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem3179616) (@lem3179615 x)). Qed.
Lemma lem3179618 (x : real) (n : nat) : (term42 x n) = (((term15 x n) = term6) = (term43 x n)).
Proof. exact (eq_refl (term42 x n)). Qed.
Lemma lem3179619 (x : real) : (term44 x) = (term45 x).
Proof. exact (fun_ext (fun n : nat => @lem3179618 x n)). Qed.
Lemma lem3179620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179621 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem3179620) (@lem3179619 x)). Qed.
Lemma lem3179622 (x : real) : (term26 x) = (term48 x).
Proof. exact (MK_COMB (@lem3179617 x) (@lem3179621 x)). Qed.
Lemma lem3179623 (x : real) : ((term25 x) = (term26 x)) = ((term31 x) = (term48 x)).
Proof. exact (MK_COMB (@lem3179611 x) (@lem3179622 x)). Qed.
Lemma lem3179624 (x : real) : (term31 x) = (term48 x).
Proof. exact (EQ_MP (@lem3179623 x) (@lem3179605 x)). Qed.
Lemma lem3179638 (x : real) (n : nat) : (term21 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3179588 x n) (@lem3179587 x n)). Qed.
Lemma lem3179639 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3179640 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem3179639) (@lem3179638 x n)). Qed.
Lemma lem3179641 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem3179642 (x : real) (n : nat) : ((term21 x n) = term6) = ((real_pow x n) = term6).
Proof. exact (MK_COMB (@lem3179640 x n) (@lem3179641)). Qed.
Lemma lem3179645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179646 (x : real) (n : nat) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem3179645) (@lem3179642 x n)). Qed.
Lemma lem3179653 (x : real) (n : nat) : (term35 x n) = (term35 x n).
Proof. exact (eq_refl (term35 x n)). Qed.
Lemma lem3179654 (x : real) (n : nat) : (((term21 x n) = term6) = (term35 x n)) = (((real_pow x n) = term6) = (term35 x n)).
Proof. exact (MK_COMB (@lem3179646 x n) (@lem3179653 x n)). Qed.
Lemma lem3179657 (x : real) : (term37 x) = (term53 x).
Proof. exact (fun_ext (fun n : nat => @lem3179654 x n)). Qed.
Lemma lem3179658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179659 (x : real) : (term39 x) = (term54 x).
Proof. exact (MK_COMB (@lem3179658) (@lem3179657 x)). Qed.
Lemma lem3179666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179667 (x : real) : (term41 x) = (term55 x).
Proof. exact (MK_COMB (@lem3179666) (@lem3179659 x)). Qed.
Lemma lem3179679 (x : real) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (EQ_MP (@lem3179581 x n) (@lem3179580 x n)). Qed.
Lemma lem3179680 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3179681 (x : real) (n : nat) : (term56 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem3179680) (@lem3179679 x n)). Qed.
Lemma lem3179682 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem3179683 (x : real) (n : nat) : ((term15 x n) = term6) = ((term16 x n) = term6).
Proof. exact (MK_COMB (@lem3179681 x n) (@lem3179682)). Qed.
Lemma lem3179685 (x : real) : ((real_inv x) = term6) = (x = term6).
Proof. exact (EQ_MP (@lem3179574 x) (@lem3179573 x)). Qed.
Lemma lem3179686 (x : real) (n : nat) : ((term16 x n) = term6) = ((real_pow x n) = term6).
Proof. exact (@lem3179685 (real_pow x n)). Qed.
Lemma lem3179689 (x : real) (n : nat) : ((term15 x n) = term6) = ((real_pow x n) = term6).
Proof. exact (TRANS (@lem3179683 x n) (@lem3179686 x n)). Qed.
Lemma lem3179690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179691 (x : real) (n : nat) : (term58 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem3179690) (@lem3179689 x n)). Qed.
Lemma lem3179698 (x : real) (n : nat) : (term43 x n) = (term43 x n).
Proof. exact (eq_refl (term43 x n)). Qed.
Lemma lem3179699 (x : real) (n : nat) : (((term15 x n) = term6) = (term43 x n)) = (((real_pow x n) = term6) = (term43 x n)).
Proof. exact (MK_COMB (@lem3179691 x n) (@lem3179698 x n)). Qed.
Lemma lem3179702 (x : real) : (term45 x) = (term59 x).
Proof. exact (fun_ext (fun n : nat => @lem3179699 x n)). Qed.
Lemma lem3179703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179704 (x : real) : (term47 x) = (term60 x).
Proof. exact (MK_COMB (@lem3179703) (@lem3179702 x)). Qed.
Lemma lem3179711 (x : real) : (term48 x) = (term61 x).
Proof. exact (MK_COMB (@lem3179667 x) (@lem3179704 x)). Qed.
Lemma lem3179714 (x : real) : (term31 x) = (term61 x).
Proof. exact (TRANS (@lem3179624 x) (@lem3179711 x)). Qed.
Lemma lem3179715 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem3179714 x)). Qed.
Lemma lem3179716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179717 : term64 = term65.
Proof. exact (MK_COMB (@lem3179716) (@lem3179715)). Qed.
Lemma lem3179724 : term65 = term64.
Proof. exact (SYM (@lem3179717)). Qed.
Lemma lem3179738 (x : real) (n : nat) : ((real_pow x n) = term6) = (term7 x n).
Proof. exact (EQ_MP (@lem3179568 x n) (@lem3179567 x n)). Qed.
Lemma lem3179745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179746 (x : real) (n : nat) : (term52 x n) = (term66 x n).
Proof. exact (MK_COMB (@lem3179745) (@lem3179738 x n)). Qed.
Lemma lem3179752 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem3179562 m n) (@lem3179561 m n)). Qed.
Lemma lem3179753 (n : nat) : ((int_of_num n) = term9) = (n = (NUMERAL 0)).
Proof. exact (@lem3179752 n (NUMERAL 0)). Qed.
Lemma lem3179756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3179757 (n : nat) : (term67 n) = (term68 n).
Proof. exact (MK_COMB (@lem3179756) (@lem3179753 n)). Qed.
Lemma lem3179758 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem3179759 (x : real) (n : nat) : (term35 x n) = (term7 x n).
Proof. exact (MK_COMB (@lem3179758 x) (@lem3179757 n)). Qed.
Lemma lem3179762 (x : real) (n : nat) : (((real_pow x n) = term6) = (term35 x n)) = ((term7 x n) = (term7 x n)).
Proof. exact (MK_COMB (@lem3179746 x n) (@lem3179759 x n)). Qed.
Lemma lem3179764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3179765 (x : Prop) : (x = x) = True.
Proof. exact (@lem3179764 Prop x). Qed.
Lemma lem3179766 (x : real) (n : nat) : ((term7 x n) = (term7 x n)) = True.
Proof. exact (@lem3179765 (term7 x n)). Qed.
Lemma lem3179767 (x : real) (n : nat) : (((real_pow x n) = term6) = (term35 x n)) = True.
Proof. exact (TRANS (@lem3179762 x n) (@lem3179766 x n)). Qed.
Lemma lem3179768 (x : real) : (term53 x) = term70.
Proof. exact (fun_ext (fun n : nat => @lem3179767 x n)). Qed.
Lemma lem3179769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179770 (x : real) : (term54 x) = term71.
Proof. exact (MK_COMB (@lem3179769) (@lem3179768 x)). Qed.
Lemma lem3179772 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179773 (t : Prop) : (term73 t) = t.
Proof. exact (@lem3179772 nat t). Qed.
Lemma lem3179774 : term71 = True.
Proof. exact (@lem3179773 True). Qed.
Lemma lem3179775 (x : real) : (term54 x) = True.
Proof. exact (TRANS (@lem3179770 x) (@lem3179774)). Qed.
Lemma lem3179776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179777 (x : real) : (term55 x) = (and True).
Proof. exact (MK_COMB (@lem3179776) (@lem3179775 x)). Qed.
Lemma lem3179785 (x : real) (n : nat) : ((real_pow x n) = term6) = (term7 x n).
Proof. exact (EQ_MP (@lem3179568 x n) (@lem3179567 x n)). Qed.
Lemma lem3179792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179793 (x : real) (n : nat) : (term52 x n) = (term66 x n).
Proof. exact (MK_COMB (@lem3179792) (@lem3179785 x n)). Qed.
Lemma lem3179799 (x : int) : ((int_neg x) = term9) = (x = term9).
Proof. exact (EQ_MP (@lem3179571 x) (@lem3179570 x)). Qed.
Lemma lem3179800 (n : nat) : ((term74 n) = term9) = ((int_of_num n) = term9).
Proof. exact (@lem3179799 (int_of_num n)). Qed.
Lemma lem3179802 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem3179562 m n) (@lem3179561 m n)). Qed.
Lemma lem3179803 (n : nat) : ((int_of_num n) = term9) = (n = (NUMERAL 0)).
Proof. exact (@lem3179802 n (NUMERAL 0)). Qed.
Lemma lem3179806 (n : nat) : ((term74 n) = term9) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem3179800 n) (@lem3179803 n)). Qed.
Lemma lem3179807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3179808 (n : nat) : (term75 n) = (term68 n).
Proof. exact (MK_COMB (@lem3179807) (@lem3179806 n)). Qed.
Lemma lem3179809 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem3179810 (x : real) (n : nat) : (term43 x n) = (term7 x n).
Proof. exact (MK_COMB (@lem3179809 x) (@lem3179808 n)). Qed.
Lemma lem3179813 (x : real) (n : nat) : (((real_pow x n) = term6) = (term43 x n)) = ((term7 x n) = (term7 x n)).
Proof. exact (MK_COMB (@lem3179793 x n) (@lem3179810 x n)). Qed.
Lemma lem3179815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3179816 (x : Prop) : (x = x) = True.
Proof. exact (@lem3179815 Prop x). Qed.
Lemma lem3179817 (x : real) (n : nat) : ((term7 x n) = (term7 x n)) = True.
Proof. exact (@lem3179816 (term7 x n)). Qed.
Lemma lem3179818 (x : real) (n : nat) : (((real_pow x n) = term6) = (term43 x n)) = True.
Proof. exact (TRANS (@lem3179813 x n) (@lem3179817 x n)). Qed.
Lemma lem3179819 (x : real) : (term59 x) = term70.
Proof. exact (fun_ext (fun n : nat => @lem3179818 x n)). Qed.
Lemma lem3179820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179821 (x : real) : (term60 x) = term71.
Proof. exact (MK_COMB (@lem3179820) (@lem3179819 x)). Qed.
Lemma lem3179823 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179824 (t : Prop) : (term73 t) = t.
Proof. exact (@lem3179823 nat t). Qed.
Lemma lem3179825 : term71 = True.
Proof. exact (@lem3179824 True). Qed.
Lemma lem3179826 (x : real) : (term60 x) = True.
Proof. exact (TRANS (@lem3179821 x) (@lem3179825)). Qed.
Lemma lem3179827 (x : real) : (term61 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3179777 x) (@lem3179826 x)). Qed.
Lemma lem3179829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3179830 : (True /\ True) = True.
Proof. exact (@lem3179829 True). Qed.
Lemma lem3179831 (x : real) : (term61 x) = True.
Proof. exact (TRANS (@lem3179827 x) (@lem3179830)). Qed.
Lemma lem3179832 : term63 = term76.
Proof. exact (fun_ext (fun x : real => @lem3179831 x)). Qed.
Lemma lem3179833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179834 : term65 = term77.
Proof. exact (MK_COMB (@lem3179833) (@lem3179832)). Qed.
Lemma lem3179836 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179837 (t : Prop) : (term78 t) = t.
Proof. exact (@lem3179836 real t). Qed.
Lemma lem3179838 : term77 = True.
Proof. exact (@lem3179837 True). Qed.
Lemma lem3179839 : term65 = True.
Proof. exact (TRANS (@lem3179834) (@lem3179838)). Qed.
Lemma lem3179840 : True = term65.
Proof. exact (SYM (@lem3179839)). Qed.
Lemma lem3179841 : term65.
Proof. exact (EQ_MP (@lem3179840) (@lem0)). Qed.
Lemma lem3179842 : term64.
Proof. exact (EQ_MP (@lem3179724) (@lem3179841)). Qed.
