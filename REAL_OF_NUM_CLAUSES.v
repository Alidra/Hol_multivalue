Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_CLAUSES_term_abbrevs.
Require Import REAL_OF_NUM_GE_spec.
Require Import REAL_OF_NUM_GT_spec.
Require Import REAL_OF_NUM_LT_spec.
Require Import REAL_OF_NUM_MAX_spec.
Require Import REAL_OF_NUM_MIN_spec.
Require Import REAL_OF_NUM_POW_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1340282_spec.
Require Import thm1340339_spec.
Require Import thm1340396_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1485710 (x : nat) : term0 x.
Proof. exact (@lem1362595 x). Qed.
Lemma lem1485711 (x : nat) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1485712 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem1485711 x) (@lem1485710 x)). Qed.
Lemma lem1485713 (x : nat) (n : nat) : term2 x n.
Proof. exact (@lem1485712 x n). Qed.
Lemma lem1485714 (x : nat) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem1485716 (m : nat) : term5 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem1485717 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1485718 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem1485717 m) (@lem1485716 m)). Qed.
Lemma lem1485719 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem1485718 m n). Qed.
Lemma lem1485720 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = (term9 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem1485722 (m : nat) : term10 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem1485723 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1485724 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1485723 m) (@lem1485722 m)). Qed.
Lemma lem1485725 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1485724 m n). Qed.
Lemma lem1485726 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1485728 (m : nat) : term15 m.
Proof. exact (@lem1484027 m). Qed.
Lemma lem1485729 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1485730 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1485729 m) (@lem1485728 m)). Qed.
Lemma lem1485731 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1485730 m n). Qed.
Lemma lem1485732 (m : nat) (n : nat) : (term17 m n) = ((term18 m n) = (term19 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1485734 (m : nat) : term20 m.
Proof. exact (@lem1483910 m). Qed.
Lemma lem1485735 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1485736 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1485735 m) (@lem1485734 m)). Qed.
Lemma lem1485737 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1485736 m n). Qed.
Lemma lem1485738 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1485740 (m : nat) : term25 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1485741 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1485742 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1485741 m) (@lem1485740 m)). Qed.
Lemma lem1485743 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem1485742 m n). Qed.
Lemma lem1485744 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1485746 (m : nat) : term29 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1485747 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1485748 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1485747 m) (@lem1485746 m)). Qed.
Lemma lem1485749 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem1485748 m n). Qed.
Lemma lem1485750 (m : nat) (n : nat) : (term31 m n) = ((term32 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1485752 (m : nat) : term33 m.
Proof. exact (@lem1483793 m). Qed.
Lemma lem1485753 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1485754 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1485753 m) (@lem1485752 m)). Qed.
Lemma lem1485755 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1485754 m n). Qed.
Lemma lem1485756 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (Peano.gt m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1485758 (m : nat) : term37 m.
Proof. exact (@lem1483730 m). Qed.
Lemma lem1485759 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1485760 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1485759 m) (@lem1485758 m)). Qed.
Lemma lem1485761 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1485760 m n). Qed.
Lemma lem1485762 (m : nat) (n : nat) : (term39 m n) = ((term40 m n) = (Peano.ge m n)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1485764 (m : nat) : term41 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1485765 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1485766 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1485765 m) (@lem1485764 m)). Qed.
Lemma lem1485767 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem1485766 m n). Qed.
Lemma lem1485768 (m : nat) (n : nat) : (term43 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem1485783 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1485786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485787 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem1485786) (@lem1485783 m n)). Qed.
Lemma lem1485790 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1485791 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem1485787 m n) (@lem1485790 m n)). Qed.
Lemma lem1485793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485794 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485793 Prop x). Qed.
Lemma lem1485795 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem1485794 (m = n)). Qed.
Lemma lem1485796 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = True.
Proof. exact (TRANS (@lem1485791 m n) (@lem1485795 m n)). Qed.
Lemma lem1485797 (m : nat) : (term46 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1485796 m n)). Qed.
Lemma lem1485798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485799 (m : nat) : (term42 m) = term48.
Proof. exact (MK_COMB (@lem1485798) (@lem1485797 m)). Qed.
Lemma lem1485801 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485802 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485801 nat t). Qed.
Lemma lem1485803 : term48 = True.
Proof. exact (@lem1485802 True). Qed.
Lemma lem1485804 (m : nat) : (term42 m) = True.
Proof. exact (TRANS (@lem1485799 m) (@lem1485803)). Qed.
Lemma lem1485805 : term51 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1485804 m)). Qed.
Lemma lem1485806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485807 : term52 = term48.
Proof. exact (MK_COMB (@lem1485806) (@lem1485805)). Qed.
Lemma lem1485809 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485810 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485809 nat t). Qed.
Lemma lem1485811 : term48 = True.
Proof. exact (@lem1485810 True). Qed.
Lemma lem1485812 : term52 = True.
Proof. exact (TRANS (@lem1485807) (@lem1485811)). Qed.
Lemma lem1485813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485814 : term53 = (and True).
Proof. exact (MK_COMB (@lem1485813) (@lem1485812)). Qed.
Lemma lem1485828 (m : nat) (n : nat) : (term40 m n) = (Peano.ge m n).
Proof. exact (EQ_MP (@lem1485762 m n) (@lem1485761 m n)). Qed.
Lemma lem1485829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485830 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem1485829) (@lem1485828 m n)). Qed.
Lemma lem1485831 (m : nat) (n : nat) : (Peano.ge m n) = (Peano.ge m n).
Proof. exact (eq_refl (Peano.ge m n)). Qed.
Lemma lem1485832 (m : nat) (n : nat) : ((term40 m n) = (Peano.ge m n)) = ((Peano.ge m n) = (Peano.ge m n)).
Proof. exact (MK_COMB (@lem1485830 m n) (@lem1485831 m n)). Qed.
Lemma lem1485834 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485835 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485834 Prop x). Qed.
Lemma lem1485836 (m : nat) (n : nat) : ((Peano.ge m n) = (Peano.ge m n)) = True.
Proof. exact (@lem1485835 (Peano.ge m n)). Qed.
Lemma lem1485837 (m : nat) (n : nat) : ((term40 m n) = (Peano.ge m n)) = True.
Proof. exact (TRANS (@lem1485832 m n) (@lem1485836 m n)). Qed.
Lemma lem1485838 (m : nat) : (term56 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1485837 m n)). Qed.
Lemma lem1485839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485840 (m : nat) : (term38 m) = term48.
Proof. exact (MK_COMB (@lem1485839) (@lem1485838 m)). Qed.
Lemma lem1485842 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485843 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485842 nat t). Qed.
Lemma lem1485844 : term48 = True.
Proof. exact (@lem1485843 True). Qed.
Lemma lem1485845 (m : nat) : (term38 m) = True.
Proof. exact (TRANS (@lem1485840 m) (@lem1485844)). Qed.
Lemma lem1485846 : term57 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1485845 m)). Qed.
Lemma lem1485847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485848 : term58 = term48.
Proof. exact (MK_COMB (@lem1485847) (@lem1485846)). Qed.
Lemma lem1485850 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485851 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485850 nat t). Qed.
Lemma lem1485852 : term48 = True.
Proof. exact (@lem1485851 True). Qed.
Lemma lem1485853 : term58 = True.
Proof. exact (TRANS (@lem1485848) (@lem1485852)). Qed.
Lemma lem1485854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485855 : term59 = (and True).
Proof. exact (MK_COMB (@lem1485854) (@lem1485853)). Qed.
Lemma lem1485869 (m : nat) (n : nat) : (term36 m n) = (Peano.gt m n).
Proof. exact (EQ_MP (@lem1485756 m n) (@lem1485755 m n)). Qed.
Lemma lem1485870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485871 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem1485870) (@lem1485869 m n)). Qed.
Lemma lem1485872 (m : nat) (n : nat) : (Peano.gt m n) = (Peano.gt m n).
Proof. exact (eq_refl (Peano.gt m n)). Qed.
Lemma lem1485873 (m : nat) (n : nat) : ((term36 m n) = (Peano.gt m n)) = ((Peano.gt m n) = (Peano.gt m n)).
Proof. exact (MK_COMB (@lem1485871 m n) (@lem1485872 m n)). Qed.
Lemma lem1485875 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485876 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485875 Prop x). Qed.
Lemma lem1485877 (m : nat) (n : nat) : ((Peano.gt m n) = (Peano.gt m n)) = True.
Proof. exact (@lem1485876 (Peano.gt m n)). Qed.
Lemma lem1485878 (m : nat) (n : nat) : ((term36 m n) = (Peano.gt m n)) = True.
Proof. exact (TRANS (@lem1485873 m n) (@lem1485877 m n)). Qed.
Lemma lem1485879 (m : nat) : (term62 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1485878 m n)). Qed.
Lemma lem1485880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485881 (m : nat) : (term34 m) = term48.
Proof. exact (MK_COMB (@lem1485880) (@lem1485879 m)). Qed.
Lemma lem1485883 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485884 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485883 nat t). Qed.
Lemma lem1485885 : term48 = True.
Proof. exact (@lem1485884 True). Qed.
Lemma lem1485886 (m : nat) : (term34 m) = True.
Proof. exact (TRANS (@lem1485881 m) (@lem1485885)). Qed.
Lemma lem1485887 : term63 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1485886 m)). Qed.
Lemma lem1485888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485889 : term64 = term48.
Proof. exact (MK_COMB (@lem1485888) (@lem1485887)). Qed.
Lemma lem1485891 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485892 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485891 nat t). Qed.
Lemma lem1485893 : term48 = True.
Proof. exact (@lem1485892 True). Qed.
Lemma lem1485894 : term64 = True.
Proof. exact (TRANS (@lem1485889) (@lem1485893)). Qed.
Lemma lem1485895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485896 : term65 = (and True).
Proof. exact (MK_COMB (@lem1485895) (@lem1485894)). Qed.
Lemma lem1485910 (m : nat) (n : nat) : (term32 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1485750 m n) (@lem1485749 m n)). Qed.
Lemma lem1485911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485912 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem1485911) (@lem1485910 m n)). Qed.
Lemma lem1485913 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1485914 (m : nat) (n : nat) : ((term32 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1485912 m n) (@lem1485913 m n)). Qed.
Lemma lem1485916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485917 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485916 Prop x). Qed.
Lemma lem1485918 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1485917 (Peano.le m n)). Qed.
Lemma lem1485919 (m : nat) (n : nat) : ((term32 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem1485914 m n) (@lem1485918 m n)). Qed.
Lemma lem1485920 (m : nat) : (term68 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1485919 m n)). Qed.
Lemma lem1485921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485922 (m : nat) : (term30 m) = term48.
Proof. exact (MK_COMB (@lem1485921) (@lem1485920 m)). Qed.
Lemma lem1485924 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485925 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485924 nat t). Qed.
Lemma lem1485926 : term48 = True.
Proof. exact (@lem1485925 True). Qed.
Lemma lem1485927 (m : nat) : (term30 m) = True.
Proof. exact (TRANS (@lem1485922 m) (@lem1485926)). Qed.
Lemma lem1485928 : term69 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1485927 m)). Qed.
Lemma lem1485929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485930 : term70 = term48.
Proof. exact (MK_COMB (@lem1485929) (@lem1485928)). Qed.
Lemma lem1485932 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485933 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485932 nat t). Qed.
Lemma lem1485934 : term48 = True.
Proof. exact (@lem1485933 True). Qed.
Lemma lem1485935 : term70 = True.
Proof. exact (TRANS (@lem1485930) (@lem1485934)). Qed.
Lemma lem1485936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485937 : term71 = (and True).
Proof. exact (MK_COMB (@lem1485936) (@lem1485935)). Qed.
Lemma lem1485951 (m : nat) (n : nat) : (term28 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1485744 m n) (@lem1485743 m n)). Qed.
Lemma lem1485952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1485953 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem1485952) (@lem1485951 m n)). Qed.
Lemma lem1485954 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem1485955 (m : nat) (n : nat) : ((term28 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem1485953 m n) (@lem1485954 m n)). Qed.
Lemma lem1485957 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1485958 (x : Prop) : (x = x) = True.
Proof. exact (@lem1485957 Prop x). Qed.
Lemma lem1485959 (m : nat) (n : nat) : ((Peano.lt m n) = (Peano.lt m n)) = True.
Proof. exact (@lem1485958 (Peano.lt m n)). Qed.
Lemma lem1485960 (m : nat) (n : nat) : ((term28 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem1485955 m n) (@lem1485959 m n)). Qed.
Lemma lem1485961 (m : nat) : (term74 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1485960 m n)). Qed.
Lemma lem1485962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485963 (m : nat) : (term26 m) = term48.
Proof. exact (MK_COMB (@lem1485962) (@lem1485961 m)). Qed.
Lemma lem1485965 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485966 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485965 nat t). Qed.
Lemma lem1485967 : term48 = True.
Proof. exact (@lem1485966 True). Qed.
Lemma lem1485968 (m : nat) : (term26 m) = True.
Proof. exact (TRANS (@lem1485963 m) (@lem1485967)). Qed.
Lemma lem1485969 : term75 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1485968 m)). Qed.
Lemma lem1485970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1485971 : term76 = term48.
Proof. exact (MK_COMB (@lem1485970) (@lem1485969)). Qed.
Lemma lem1485973 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1485974 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1485973 nat t). Qed.
Lemma lem1485975 : term48 = True.
Proof. exact (@lem1485974 True). Qed.
Lemma lem1485976 : term76 = True.
Proof. exact (TRANS (@lem1485971) (@lem1485975)). Qed.
Lemma lem1485977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1485978 : term77 = (and True).
Proof. exact (MK_COMB (@lem1485977) (@lem1485976)). Qed.
Lemma lem1485992 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem1485738 m n) (@lem1485737 m n)). Qed.
Lemma lem1485993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1485994 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem1485993) (@lem1485992 m n)). Qed.
Lemma lem1485995 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1485996 (m : nat) (n : nat) : ((term23 m n) = (term24 m n)) = ((term24 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem1485994 m n) (@lem1485995 m n)). Qed.
Lemma lem1485998 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1485999 (m : nat) (n : nat) : ((term24 m n) = (term24 m n)) = ((Nat.max m n) = (Nat.max m n)).
Proof. exact (@lem1485998 (Nat.max m n) (Nat.max m n)). Qed.
Lemma lem1486001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486002 (x : nat) : (x = x) = True.
Proof. exact (@lem1486001 nat x). Qed.
Lemma lem1486003 (m : nat) (n : nat) : ((Nat.max m n) = (Nat.max m n)) = True.
Proof. exact (@lem1486002 (Nat.max m n)). Qed.
Lemma lem1486004 (m : nat) (n : nat) : ((term24 m n) = (term24 m n)) = True.
Proof. exact (TRANS (@lem1485999 m n) (@lem1486003 m n)). Qed.
Lemma lem1486005 (m : nat) (n : nat) : ((term23 m n) = (term24 m n)) = True.
Proof. exact (TRANS (@lem1485996 m n) (@lem1486004 m n)). Qed.
Lemma lem1486006 (m : nat) : (term80 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1486005 m n)). Qed.
Lemma lem1486007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486008 (m : nat) : (term21 m) = term48.
Proof. exact (MK_COMB (@lem1486007) (@lem1486006 m)). Qed.
Lemma lem1486010 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486011 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486010 nat t). Qed.
Lemma lem1486012 : term48 = True.
Proof. exact (@lem1486011 True). Qed.
Lemma lem1486013 (m : nat) : (term21 m) = True.
Proof. exact (TRANS (@lem1486008 m) (@lem1486012)). Qed.
Lemma lem1486014 : term81 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1486013 m)). Qed.
Lemma lem1486015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486016 : term82 = term48.
Proof. exact (MK_COMB (@lem1486015) (@lem1486014)). Qed.
Lemma lem1486018 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486019 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486018 nat t). Qed.
Lemma lem1486020 : term48 = True.
Proof. exact (@lem1486019 True). Qed.
Lemma lem1486021 : term82 = True.
Proof. exact (TRANS (@lem1486016) (@lem1486020)). Qed.
Lemma lem1486022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486023 : term83 = (and True).
Proof. exact (MK_COMB (@lem1486022) (@lem1486021)). Qed.
Lemma lem1486037 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem1485732 m n) (@lem1485731 m n)). Qed.
Lemma lem1486038 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1486039 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem1486038) (@lem1486037 m n)). Qed.
Lemma lem1486040 (m : nat) (n : nat) : (term19 m n) = (term19 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1486041 (m : nat) (n : nat) : ((term18 m n) = (term19 m n)) = ((term19 m n) = (term19 m n)).
Proof. exact (MK_COMB (@lem1486039 m n) (@lem1486040 m n)). Qed.
Lemma lem1486043 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1486044 (m : nat) (n : nat) : ((term19 m n) = (term19 m n)) = ((Nat.min m n) = (Nat.min m n)).
Proof. exact (@lem1486043 (Nat.min m n) (Nat.min m n)). Qed.
Lemma lem1486046 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486047 (x : nat) : (x = x) = True.
Proof. exact (@lem1486046 nat x). Qed.
Lemma lem1486048 (m : nat) (n : nat) : ((Nat.min m n) = (Nat.min m n)) = True.
Proof. exact (@lem1486047 (Nat.min m n)). Qed.
Lemma lem1486049 (m : nat) (n : nat) : ((term19 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem1486044 m n) (@lem1486048 m n)). Qed.
Lemma lem1486050 (m : nat) (n : nat) : ((term18 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem1486041 m n) (@lem1486049 m n)). Qed.
Lemma lem1486051 (m : nat) : (term86 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1486050 m n)). Qed.
Lemma lem1486052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486053 (m : nat) : (term16 m) = term48.
Proof. exact (MK_COMB (@lem1486052) (@lem1486051 m)). Qed.
Lemma lem1486055 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486056 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486055 nat t). Qed.
Lemma lem1486057 : term48 = True.
Proof. exact (@lem1486056 True). Qed.
Lemma lem1486058 (m : nat) : (term16 m) = True.
Proof. exact (TRANS (@lem1486053 m) (@lem1486057)). Qed.
Lemma lem1486059 : term87 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1486058 m)). Qed.
Lemma lem1486060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486061 : term88 = term48.
Proof. exact (MK_COMB (@lem1486060) (@lem1486059)). Qed.
Lemma lem1486063 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486064 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486063 nat t). Qed.
Lemma lem1486065 : term48 = True.
Proof. exact (@lem1486064 True). Qed.
Lemma lem1486066 : term88 = True.
Proof. exact (TRANS (@lem1486061) (@lem1486065)). Qed.
Lemma lem1486067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486068 : term89 = (and True).
Proof. exact (MK_COMB (@lem1486067) (@lem1486066)). Qed.
Lemma lem1486082 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem1485726 m n) (@lem1485725 m n)). Qed.
Lemma lem1486083 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1486084 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem1486083) (@lem1486082 m n)). Qed.
Lemma lem1486085 (m : nat) (n : nat) : (term14 m n) = (term14 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1486086 (m : nat) (n : nat) : ((term13 m n) = (term14 m n)) = ((term14 m n) = (term14 m n)).
Proof. exact (MK_COMB (@lem1486084 m n) (@lem1486085 m n)). Qed.
Lemma lem1486088 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1486089 (m : nat) (n : nat) : ((term14 m n) = (term14 m n)) = ((Nat.add m n) = (Nat.add m n)).
Proof. exact (@lem1486088 (Nat.add m n) (Nat.add m n)). Qed.
Lemma lem1486091 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486092 (x : nat) : (x = x) = True.
Proof. exact (@lem1486091 nat x). Qed.
Lemma lem1486093 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add m n)) = True.
Proof. exact (@lem1486092 (Nat.add m n)). Qed.
Lemma lem1486094 (m : nat) (n : nat) : ((term14 m n) = (term14 m n)) = True.
Proof. exact (TRANS (@lem1486089 m n) (@lem1486093 m n)). Qed.
Lemma lem1486095 (m : nat) (n : nat) : ((term13 m n) = (term14 m n)) = True.
Proof. exact (TRANS (@lem1486086 m n) (@lem1486094 m n)). Qed.
Lemma lem1486096 (m : nat) : (term92 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1486095 m n)). Qed.
Lemma lem1486097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486098 (m : nat) : (term11 m) = term48.
Proof. exact (MK_COMB (@lem1486097) (@lem1486096 m)). Qed.
Lemma lem1486100 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486101 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486100 nat t). Qed.
Lemma lem1486102 : term48 = True.
Proof. exact (@lem1486101 True). Qed.
Lemma lem1486103 (m : nat) : (term11 m) = True.
Proof. exact (TRANS (@lem1486098 m) (@lem1486102)). Qed.
Lemma lem1486104 : term93 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1486103 m)). Qed.
Lemma lem1486105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486106 : term94 = term48.
Proof. exact (MK_COMB (@lem1486105) (@lem1486104)). Qed.
Lemma lem1486108 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486109 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486108 nat t). Qed.
Lemma lem1486110 : term48 = True.
Proof. exact (@lem1486109 True). Qed.
Lemma lem1486111 : term94 = True.
Proof. exact (TRANS (@lem1486106) (@lem1486110)). Qed.
Lemma lem1486112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486113 : term95 = (and True).
Proof. exact (MK_COMB (@lem1486112) (@lem1486111)). Qed.
Lemma lem1486127 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (EQ_MP (@lem1485720 m n) (@lem1485719 m n)). Qed.
Lemma lem1486128 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1486129 (m : nat) (n : nat) : (term96 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem1486128) (@lem1486127 m n)). Qed.
Lemma lem1486130 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1486131 (m : nat) (n : nat) : ((term8 m n) = (term9 m n)) = ((term9 m n) = (term9 m n)).
Proof. exact (MK_COMB (@lem1486129 m n) (@lem1486130 m n)). Qed.
Lemma lem1486133 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1486134 (m : nat) (n : nat) : ((term9 m n) = (term9 m n)) = ((Nat.mul m n) = (Nat.mul m n)).
Proof. exact (@lem1486133 (Nat.mul m n) (Nat.mul m n)). Qed.
Lemma lem1486136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486137 (x : nat) : (x = x) = True.
Proof. exact (@lem1486136 nat x). Qed.
Lemma lem1486138 (m : nat) (n : nat) : ((Nat.mul m n) = (Nat.mul m n)) = True.
Proof. exact (@lem1486137 (Nat.mul m n)). Qed.
Lemma lem1486139 (m : nat) (n : nat) : ((term9 m n) = (term9 m n)) = True.
Proof. exact (TRANS (@lem1486134 m n) (@lem1486138 m n)). Qed.
Lemma lem1486140 (m : nat) (n : nat) : ((term8 m n) = (term9 m n)) = True.
Proof. exact (TRANS (@lem1486131 m n) (@lem1486139 m n)). Qed.
Lemma lem1486141 (m : nat) : (term98 m) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1486140 m n)). Qed.
Lemma lem1486142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486143 (m : nat) : (term6 m) = term48.
Proof. exact (MK_COMB (@lem1486142) (@lem1486141 m)). Qed.
Lemma lem1486145 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486146 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486145 nat t). Qed.
Lemma lem1486147 : term48 = True.
Proof. exact (@lem1486146 True). Qed.
Lemma lem1486148 (m : nat) : (term6 m) = True.
Proof. exact (TRANS (@lem1486143 m) (@lem1486147)). Qed.
Lemma lem1486149 : term99 = term47.
Proof. exact (fun_ext (fun m : nat => @lem1486148 m)). Qed.
Lemma lem1486150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486151 : term100 = term48.
Proof. exact (MK_COMB (@lem1486150) (@lem1486149)). Qed.
Lemma lem1486153 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486154 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486153 nat t). Qed.
Lemma lem1486155 : term48 = True.
Proof. exact (@lem1486154 True). Qed.
Lemma lem1486156 : term100 = True.
Proof. exact (TRANS (@lem1486151) (@lem1486155)). Qed.
Lemma lem1486157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486158 : term101 = (and True).
Proof. exact (MK_COMB (@lem1486157) (@lem1486156)). Qed.
Lemma lem1486170 (x : nat) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem1485714 x n) (@lem1485713 x n)). Qed.
Lemma lem1486171 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1486172 (x : nat) (n : nat) : (term102 x n) = (term103 x n).
Proof. exact (MK_COMB (@lem1486171) (@lem1486170 x n)). Qed.
Lemma lem1486173 (x : nat) (n : nat) : (term4 x n) = (term4 x n).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem1486174 (x : nat) (n : nat) : ((term3 x n) = (term4 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem1486172 x n) (@lem1486173 x n)). Qed.
Lemma lem1486176 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1485768 m n) (@lem1485767 m n)). Qed.
Lemma lem1486177 (x : nat) (n : nat) : ((term4 x n) = (term4 x n)) = ((Nat.pow x n) = (Nat.pow x n)).
Proof. exact (@lem1486176 (Nat.pow x n) (Nat.pow x n)). Qed.
Lemma lem1486179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486180 (x : nat) : (x = x) = True.
Proof. exact (@lem1486179 nat x). Qed.
Lemma lem1486181 (x : nat) (n : nat) : ((Nat.pow x n) = (Nat.pow x n)) = True.
Proof. exact (@lem1486180 (Nat.pow x n)). Qed.
Lemma lem1486182 (x : nat) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (TRANS (@lem1486177 x n) (@lem1486181 x n)). Qed.
Lemma lem1486183 (x : nat) (n : nat) : ((term3 x n) = (term4 x n)) = True.
Proof. exact (TRANS (@lem1486174 x n) (@lem1486182 x n)). Qed.
Lemma lem1486184 (x : nat) : (term104 x) = term47.
Proof. exact (fun_ext (fun n : nat => @lem1486183 x n)). Qed.
Lemma lem1486185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486186 (x : nat) : (term1 x) = term48.
Proof. exact (MK_COMB (@lem1486185) (@lem1486184 x)). Qed.
Lemma lem1486188 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486189 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486188 nat t). Qed.
Lemma lem1486190 : term48 = True.
Proof. exact (@lem1486189 True). Qed.
Lemma lem1486191 (x : nat) : (term1 x) = True.
Proof. exact (TRANS (@lem1486186 x) (@lem1486190)). Qed.
Lemma lem1486192 : term105 = term47.
Proof. exact (fun_ext (fun x : nat => @lem1486191 x)). Qed.
Lemma lem1486193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1486194 : term106 = term48.
Proof. exact (MK_COMB (@lem1486193) (@lem1486192)). Qed.
Lemma lem1486196 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1486197 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1486196 nat t). Qed.
Lemma lem1486198 : term48 = True.
Proof. exact (@lem1486197 True). Qed.
Lemma lem1486199 : term106 = True.
Proof. exact (TRANS (@lem1486194) (@lem1486198)). Qed.
Lemma lem1486200 : term107 = (True /\ True).
Proof. exact (MK_COMB (@lem1486158) (@lem1486199)). Qed.
Lemma lem1486202 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486203 : (True /\ True) = True.
Proof. exact (@lem1486202 True). Qed.
Lemma lem1486204 : term107 = True.
Proof. exact (TRANS (@lem1486200) (@lem1486203)). Qed.
Lemma lem1486205 : term108 = (True /\ True).
Proof. exact (MK_COMB (@lem1486113) (@lem1486204)). Qed.
Lemma lem1486207 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486208 : (True /\ True) = True.
Proof. exact (@lem1486207 True). Qed.
Lemma lem1486209 : term108 = True.
Proof. exact (TRANS (@lem1486205) (@lem1486208)). Qed.
Lemma lem1486210 : term109 = (True /\ True).
Proof. exact (MK_COMB (@lem1486068) (@lem1486209)). Qed.
Lemma lem1486212 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486213 : (True /\ True) = True.
Proof. exact (@lem1486212 True). Qed.
Lemma lem1486214 : term109 = True.
Proof. exact (TRANS (@lem1486210) (@lem1486213)). Qed.
Lemma lem1486215 : term110 = (True /\ True).
Proof. exact (MK_COMB (@lem1486023) (@lem1486214)). Qed.
Lemma lem1486217 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486218 : (True /\ True) = True.
Proof. exact (@lem1486217 True). Qed.
Lemma lem1486219 : term110 = True.
Proof. exact (TRANS (@lem1486215) (@lem1486218)). Qed.
Lemma lem1486220 : term111 = (True /\ True).
Proof. exact (MK_COMB (@lem1485978) (@lem1486219)). Qed.
Lemma lem1486222 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486223 : (True /\ True) = True.
Proof. exact (@lem1486222 True). Qed.
Lemma lem1486224 : term111 = True.
Proof. exact (TRANS (@lem1486220) (@lem1486223)). Qed.
Lemma lem1486225 : term112 = (True /\ True).
Proof. exact (MK_COMB (@lem1485937) (@lem1486224)). Qed.
Lemma lem1486227 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486228 : (True /\ True) = True.
Proof. exact (@lem1486227 True). Qed.
Lemma lem1486229 : term112 = True.
Proof. exact (TRANS (@lem1486225) (@lem1486228)). Qed.
Lemma lem1486230 : term113 = (True /\ True).
Proof. exact (MK_COMB (@lem1485896) (@lem1486229)). Qed.
Lemma lem1486232 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486233 : (True /\ True) = True.
Proof. exact (@lem1486232 True). Qed.
Lemma lem1486234 : term113 = True.
Proof. exact (TRANS (@lem1486230) (@lem1486233)). Qed.
Lemma lem1486235 : term114 = (True /\ True).
Proof. exact (MK_COMB (@lem1485855) (@lem1486234)). Qed.
Lemma lem1486237 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486238 : (True /\ True) = True.
Proof. exact (@lem1486237 True). Qed.
Lemma lem1486239 : term114 = True.
Proof. exact (TRANS (@lem1486235) (@lem1486238)). Qed.
Lemma lem1486240 : term115 = (True /\ True).
Proof. exact (MK_COMB (@lem1485814) (@lem1486239)). Qed.
Lemma lem1486242 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486243 : (True /\ True) = True.
Proof. exact (@lem1486242 True). Qed.
Lemma lem1486244 : term115 = True.
Proof. exact (TRANS (@lem1486240) (@lem1486243)). Qed.
Lemma lem1486245 : True = term115.
Proof. exact (SYM (@lem1486244)). Qed.
Lemma lem1486246 : term115.
Proof. exact (EQ_MP (@lem1486245) (@lem0)). Qed.
