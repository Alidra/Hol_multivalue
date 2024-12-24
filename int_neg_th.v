Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_neg_th_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Require Import EXISTS_REFL_spec.
Require Import REAL_EQ_NEG2_spec.
Require Import REAL_NEG_NEG_spec.
Require Import dest_int_rep_spec.
Require Import int_neg_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Require Import thm2267742_spec.
Require Import thm7_spec.
Lemma lem2272665 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2272666 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2272665 A x a h1)). Qed.
Lemma lem2272667 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2272668 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2272667 A a x h1)). Qed.
Lemma lem2272669 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2272666 A x a h1) (fun h1 : a = x => @lem2272668 A a x h1)). Qed.
Lemma lem2272670 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2272669 A a x)). Qed.
Lemma lem2272671 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2272672 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2272671 A) (@lem2272670 A a)). Qed.
Lemma lem2272673 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2272672 A a)). Qed.
Lemma lem2272674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2272675 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2272674 A) (@lem2272673 A)). Qed.
Lemma lem2272676 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2272675 A) (@lem4363 A)). Qed.
Lemma lem2272677 (x : int) : term8 x.
Proof. exact (@lem2267790 x). Qed.
Lemma lem2272678 (x : int) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem2272679 (x : int) : term9 x.
Proof. exact (EQ_MP (@lem2272678 x) (@lem2272677 x)). Qed.
Lemma lem2272680 (r : real) (h1 : (integer r) = ((term10 r) = r)) : (integer r) = ((term10 r) = r).
Proof. exact (h1). Qed.
Lemma lem2272681 (r : real) (h1 : (integer r) = ((term10 r) = r)) : ((term10 r) = r) = (integer r).
Proof. exact (SYM (@lem2272680 r h1)). Qed.
Lemma lem2272682 (r : real) (h1 : ((term10 r) = r) = (integer r)) : ((term10 r) = r) = (integer r).
Proof. exact (h1). Qed.
Lemma lem2272683 (r : real) (h1 : ((term10 r) = r) = (integer r)) : (integer r) = ((term10 r) = r).
Proof. exact (SYM (@lem2272682 r h1)). Qed.
Lemma lem2272684 (r : real) : ((integer r) = ((term10 r) = r)) = (((term10 r) = r) = (integer r)).
Proof. exact (prop_ext (fun h1 : (integer r) = ((term10 r) = r) => @lem2272681 r h1) (fun h1 : ((term10 r) = r) = (integer r) => @lem2272683 r h1)). Qed.
Lemma lem2272686 (i : int) : term11 i.
Proof. exact (@lem2272662 i). Qed.
Lemma lem2272687 (i : int) : (term11 i) = ((int_neg i) = (term12 i)).
Proof. exact (eq_refl (term11 i)). Qed.
Lemma lem2272696 (i : int) : (int_neg i) = (term12 i).
Proof. exact (EQ_MP (@lem2272687 i) (@lem2272686 i)). Qed.
Lemma lem2272697 (x : int) : (int_neg x) = (term12 x).
Proof. exact (@lem2272696 x). Qed.
Lemma lem2272698 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2272699 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2272698) (@lem2272697 x)). Qed.
Lemma lem2272700 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2272701 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2272700) (@lem2272699 x)). Qed.
Lemma lem2272702 (x : int) : (term17 x) = (term17 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem2272703 (x : int) : ((term13 x) = (term17 x)) = ((term14 x) = (term17 x)).
Proof. exact (MK_COMB (@lem2272701 x) (@lem2272702 x)). Qed.
Lemma lem2272705 (r : real) : ((term10 r) = r) = (integer r).
Proof. exact (EQ_MP (@lem2272684 r) (@lem2267742 r)). Qed.
Lemma lem2272706 (x : int) : ((term14 x) = (term17 x)) = (term18 x).
Proof. exact (@lem2272705 (term17 x)). Qed.
Lemma lem2272708 (x : real) : (integer x) = (term19 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.
Lemma lem2272709 (x : int) : (term18 x) = (term20 x).
Proof. exact (@lem2272708 (term17 x)). Qed.
Lemma lem2272720 (x : int) : ((term14 x) = (term17 x)) = (term20 x).
Proof. exact (TRANS (@lem2272706 x) (@lem2272709 x)). Qed.
Lemma lem2272721 (x : int) : ((term13 x) = (term17 x)) = (term20 x).
Proof. exact (TRANS (@lem2272703 x) (@lem2272720 x)). Qed.
Lemma lem2272722 : term21 = term22.
Proof. exact (fun_ext (fun x : int => @lem2272721 x)). Qed.
Lemma lem2272723 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2272724 : term23 = term24.
Proof. exact (MK_COMB (@lem2272723) (@lem2272722)). Qed.
Lemma lem2272729 : term24 = term23.
Proof. exact (SYM (@lem2272724)). Qed.
Lemma lem2272730 (x : int) (n : nat) (h1 : term25 x n) : term25 x n.
Proof. exact (h1). Qed.
Lemma lem2272731 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (real_of_int x) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2272732 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (real_of_int x) = (term26 n).
Proof. exact (h1). Qed.
Lemma lem2272733 {A : Type'} (a : A) : term27 A a.
Proof. exact (@lem2272676 A a). Qed.
Lemma lem2272734 {A : Type'} (a : A) : (term27 A a) = (term3 A a).
Proof. exact (eq_refl (term27 A a)). Qed.
Lemma lem2272735 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2272734 A a) (@lem2272733 A a)). Qed.
Lemma lem2272736 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2272738 (m : nat) : term28 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2272739 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem2272740 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem2272739 m) (@lem2272738 m)). Qed.
Lemma lem2272741 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem2272740 m n). Qed.
Lemma lem2272742 (m : nat) (n : nat) : (term30 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem2272744 (x : real) : term31 x.
Proof. exact (@lem1525370 x). Qed.
Lemma lem2272745 (x : real) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2272746 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem2272745 x) (@lem2272744 x)). Qed.
Lemma lem2272747 (x : real) (y : real) : term33 x y.
Proof. exact (@lem2272746 x y). Qed.
Lemma lem2272748 (x : real) (y : real) : (term33 x y) = (((real_neg x) = (real_neg y)) = (x = y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem2272750 {A : Type'} (P : A -> Prop) : term34 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2272751 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem2272752 {A : Type'} (P : A -> Prop) : term35 A P.
Proof. exact (EQ_MP (@lem2272751 A P) (@lem2272750 A P)). Qed.
Lemma lem2272753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term36 A P Q.
Proof. exact (@lem2272752 A P Q). Qed.
Lemma lem2272754 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem2272760 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem2272754 A P Q) (@lem2272753 A P Q)). Qed.
Lemma lem2272761 (P : nat -> Prop) (Q : nat -> Prop) : (term39 P Q) = (term40 P Q).
Proof. exact (@lem2272760 nat P Q). Qed.
Lemma lem2272762 (x : int) : (term41 x) = (term42 x).
Proof. exact (@lem2272761 (term43 x) (term44 x)). Qed.
Lemma lem2272763 (x : int) (n : nat) : (term45 x n) = ((term17 x) = (real_of_num n)).
Proof. exact (eq_refl (term45 x n)). Qed.
Lemma lem2272764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2272765 (x : int) (n : nat) : (term46 x n) = (term47 x n).
Proof. exact (MK_COMB (@lem2272764) (@lem2272763 x n)). Qed.
Lemma lem2272766 (x : int) (n : nat) : (term48 x n) = ((term17 x) = (term26 n)).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2272767 (x : int) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem2272765 x n) (@lem2272766 x n)). Qed.
Lemma lem2272768 (x : int) : (term51 x) = (term52 x).
Proof. exact (fun_ext (fun n : nat => @lem2272767 x n)). Qed.
Lemma lem2272769 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272770 (x : int) : (term41 x) = (term20 x).
Proof. exact (MK_COMB (@lem2272769) (@lem2272768 x)). Qed.
Lemma lem2272771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2272772 (x : int) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem2272771) (@lem2272770 x)). Qed.
Lemma lem2272773 (x : int) (n : nat) : (term45 x n) = ((term17 x) = (real_of_num n)).
Proof. exact (eq_refl (term45 x n)). Qed.
Lemma lem2272774 (x : int) : (term55 x) = (term43 x).
Proof. exact (fun_ext (fun n : nat => @lem2272773 x n)). Qed.
Lemma lem2272775 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272776 (x : int) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem2272775) (@lem2272774 x)). Qed.
Lemma lem2272777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2272778 (x : int) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem2272777) (@lem2272776 x)). Qed.
Lemma lem2272779 (x : int) (n : nat) : (term48 x n) = ((term17 x) = (term26 n)).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2272780 (x : int) : (term60 x) = (term44 x).
Proof. exact (fun_ext (fun n : nat => @lem2272779 x n)). Qed.
Lemma lem2272781 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272782 (x : int) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem2272781) (@lem2272780 x)). Qed.
Lemma lem2272783 (x : int) : (term42 x) = (term63 x).
Proof. exact (MK_COMB (@lem2272778 x) (@lem2272782 x)). Qed.
Lemma lem2272784 (x : int) : ((term41 x) = (term42 x)) = ((term20 x) = (term63 x)).
Proof. exact (MK_COMB (@lem2272772 x) (@lem2272783 x)). Qed.
Lemma lem2272785 (x : int) : (term20 x) = (term63 x).
Proof. exact (EQ_MP (@lem2272784 x) (@lem2272762 x)). Qed.
Lemma lem2272809 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (real_of_int x) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2272810 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2272811 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term17 x) = (term26 n).
Proof. exact (MK_COMB (@lem2272810) (@lem2272809 x n h1)). Qed.
Lemma lem2272812 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2272813 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term64 x) = (term65 n).
Proof. exact (MK_COMB (@lem2272812) (@lem2272811 x n h1)). Qed.
Lemma lem2272814 (_28672 : nat) : (real_of_num _28672) = (real_of_num _28672).
Proof. exact (eq_refl (real_of_num _28672)). Qed.
Lemma lem2272815 (_28672 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : ((term17 x) = (real_of_num _28672)) = ((term26 n) = (real_of_num _28672)).
Proof. exact (MK_COMB (@lem2272813 x n h1) (@lem2272814 _28672)). Qed.
Lemma lem2272820 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term43 x) = (term66 n).
Proof. exact (fun_ext (fun _28672 : nat => @lem2272815 _28672 x n h1)). Qed.
Lemma lem2272821 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272822 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term57 x) = (term67 n).
Proof. exact (MK_COMB (@lem2272821) (@lem2272820 x n h1)). Qed.
Lemma lem2272829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2272830 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term59 x) = (term68 n).
Proof. exact (MK_COMB (@lem2272829) (@lem2272822 x n h1)). Qed.
Lemma lem2272859 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2272748 x y) (@lem2272747 x y)). Qed.
Lemma lem2272860 (x : int) (_28673 : nat) : ((term17 x) = (term26 _28673)) = ((real_of_int x) = (real_of_num _28673)).
Proof. exact (@lem2272859 (real_of_int x) (real_of_num _28673)). Qed.
Lemma lem2272864 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (real_of_int x) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2272865 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2272866 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term69 x) = (term70 n).
Proof. exact (MK_COMB (@lem2272865) (@lem2272864 x n h1)). Qed.
Lemma lem2272867 (_28673 : nat) : (real_of_num _28673) = (real_of_num _28673).
Proof. exact (eq_refl (real_of_num _28673)). Qed.
Lemma lem2272868 (_28673 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : ((real_of_int x) = (real_of_num _28673)) = ((real_of_num n) = (real_of_num _28673)).
Proof. exact (MK_COMB (@lem2272866 x n h1) (@lem2272867 _28673)). Qed.
Lemma lem2272870 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2272742 m n) (@lem2272741 m n)). Qed.
Lemma lem2272871 (n : nat) (_28673 : nat) : ((real_of_num n) = (real_of_num _28673)) = (n = _28673).
Proof. exact (@lem2272870 n _28673). Qed.
Lemma lem2272874 (_28673 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : ((real_of_int x) = (real_of_num _28673)) = (n = _28673).
Proof. exact (TRANS (@lem2272868 _28673 x n h1) (@lem2272871 n _28673)). Qed.
Lemma lem2272875 (_28673 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : ((term17 x) = (term26 _28673)) = (n = _28673).
Proof. exact (TRANS (@lem2272860 x _28673) (@lem2272874 _28673 x n h1)). Qed.
Lemma lem2272878 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term44 x) = (term71 n).
Proof. exact (fun_ext (fun _28673 : nat => @lem2272875 _28673 x n h1)). Qed.
Lemma lem2272879 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272880 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term62 x) = (term72 n).
Proof. exact (MK_COMB (@lem2272879) (@lem2272878 x n h1)). Qed.
Lemma lem2272882 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2272736 A a) (@lem2272735 A a)). Qed.
Lemma lem2272883 (a : nat) : (term72 a) = True.
Proof. exact (@lem2272882 nat a). Qed.
Lemma lem2272884 (n : nat) : (term72 n) = True.
Proof. exact (@lem2272883 n). Qed.
Lemma lem2272885 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term62 x) = True.
Proof. exact (TRANS (@lem2272880 x n h1) (@lem2272884 n)). Qed.
Lemma lem2272886 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term63 x) = (term73 n).
Proof. exact (MK_COMB (@lem2272830 x n h1) (@lem2272885 x n h1)). Qed.
Lemma lem2272888 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2272889 (n : nat) : (term73 n) = True.
Proof. exact (@lem2272888 (term67 n)). Qed.
Lemma lem2272890 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term63 x) = True.
Proof. exact (TRANS (@lem2272886 x n h1) (@lem2272889 n)). Qed.
Lemma lem2272891 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term20 x) = True.
Proof. exact (TRANS (@lem2272785 x) (@lem2272890 x n h1)). Qed.
Lemma lem2272892 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : True = (term20 x).
Proof. exact (SYM (@lem2272891 x n h1)). Qed.
Lemma lem2272893 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : term20 x.
Proof. exact (EQ_MP (@lem2272892 x n h1) (@lem0)). Qed.
Lemma lem2272894 {A : Type'} (a : A) : term27 A a.
Proof. exact (@lem2272676 A a). Qed.
Lemma lem2272895 {A : Type'} (a : A) : (term27 A a) = (term3 A a).
Proof. exact (eq_refl (term27 A a)). Qed.
Lemma lem2272896 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2272895 A a) (@lem2272894 A a)). Qed.
Lemma lem2272897 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2272899 (m : nat) : term28 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2272900 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem2272901 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem2272900 m) (@lem2272899 m)). Qed.
Lemma lem2272902 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem2272901 m n). Qed.
Lemma lem2272903 (m : nat) (n : nat) : (term30 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem2272905 (x : real) : term31 x.
Proof. exact (@lem1525370 x). Qed.
Lemma lem2272906 (x : real) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2272907 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem2272906 x) (@lem2272905 x)). Qed.
Lemma lem2272908 (x : real) (y : real) : term33 x y.
Proof. exact (@lem2272907 x y). Qed.
Lemma lem2272909 (x : real) (y : real) : (term33 x y) = (((real_neg x) = (real_neg y)) = (x = y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem2272911 {A : Type'} (P : A -> Prop) : term34 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2272912 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem2272913 {A : Type'} (P : A -> Prop) : term35 A P.
Proof. exact (EQ_MP (@lem2272912 A P) (@lem2272911 A P)). Qed.
Lemma lem2272914 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term36 A P Q.
Proof. exact (@lem2272913 A P Q). Qed.
Lemma lem2272915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem2272917 (x : real) : term74 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem2272918 (x : real) : (term74 x) = ((term75 x) = x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem2272921 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem2272915 A P Q) (@lem2272914 A P Q)). Qed.
Lemma lem2272922 (P : nat -> Prop) (Q : nat -> Prop) : (term39 P Q) = (term40 P Q).
Proof. exact (@lem2272921 nat P Q). Qed.
Lemma lem2272923 (x : int) : (term41 x) = (term42 x).
Proof. exact (@lem2272922 (term43 x) (term44 x)). Qed.
Lemma lem2272924 (x : int) (n : nat) : (term45 x n) = ((term17 x) = (real_of_num n)).
Proof. exact (eq_refl (term45 x n)). Qed.
Lemma lem2272925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2272926 (x : int) (n : nat) : (term46 x n) = (term47 x n).
Proof. exact (MK_COMB (@lem2272925) (@lem2272924 x n)). Qed.
Lemma lem2272927 (x : int) (n : nat) : (term48 x n) = ((term17 x) = (term26 n)).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2272928 (x : int) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem2272926 x n) (@lem2272927 x n)). Qed.
Lemma lem2272929 (x : int) : (term51 x) = (term52 x).
Proof. exact (fun_ext (fun n : nat => @lem2272928 x n)). Qed.
Lemma lem2272930 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272931 (x : int) : (term41 x) = (term20 x).
Proof. exact (MK_COMB (@lem2272930) (@lem2272929 x)). Qed.
Lemma lem2272932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2272933 (x : int) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem2272932) (@lem2272931 x)). Qed.
Lemma lem2272934 (x : int) (n : nat) : (term45 x n) = ((term17 x) = (real_of_num n)).
Proof. exact (eq_refl (term45 x n)). Qed.
Lemma lem2272935 (x : int) : (term55 x) = (term43 x).
Proof. exact (fun_ext (fun n : nat => @lem2272934 x n)). Qed.
Lemma lem2272936 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272937 (x : int) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem2272936) (@lem2272935 x)). Qed.
Lemma lem2272938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2272939 (x : int) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem2272938) (@lem2272937 x)). Qed.
Lemma lem2272940 (x : int) (n : nat) : (term48 x n) = ((term17 x) = (term26 n)).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem2272941 (x : int) : (term60 x) = (term44 x).
Proof. exact (fun_ext (fun n : nat => @lem2272940 x n)). Qed.
Lemma lem2272942 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2272943 (x : int) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem2272942) (@lem2272941 x)). Qed.
Lemma lem2272944 (x : int) : (term42 x) = (term63 x).
Proof. exact (MK_COMB (@lem2272939 x) (@lem2272943 x)). Qed.
Lemma lem2272945 (x : int) : ((term41 x) = (term42 x)) = ((term20 x) = (term63 x)).
Proof. exact (MK_COMB (@lem2272933 x) (@lem2272944 x)). Qed.
Lemma lem2272946 (x : int) : (term20 x) = (term63 x).
Proof. exact (EQ_MP (@lem2272945 x) (@lem2272923 x)). Qed.
Lemma lem2272981 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (real_of_int x) = (term26 n).
Proof. exact (h1). Qed.
Lemma lem2272982 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2272983 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term17 x) = (term76 n).
Proof. exact (MK_COMB (@lem2272982) (@lem2272981 x n h1)). Qed.
Lemma lem2272985 (x : real) : (term75 x) = x.
Proof. exact (EQ_MP (@lem2272918 x) (@lem2272917 x)). Qed.
Lemma lem2272986 (n : nat) : (term76 n) = (real_of_num n).
Proof. exact (@lem2272985 (real_of_num n)). Qed.
Lemma lem2272987 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term17 x) = (real_of_num n).
Proof. exact (TRANS (@lem2272983 x n h1) (@lem2272986 n)). Qed.
Lemma lem2272988 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2272989 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term64 x) = (term70 n).
Proof. exact (MK_COMB (@lem2272988) (@lem2272987 x n h1)). Qed.
Lemma lem2272990 (_28674 : nat) : (real_of_num _28674) = (real_of_num _28674).
Proof. exact (eq_refl (real_of_num _28674)). Qed.
Lemma lem2272991 (_28674 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : ((term17 x) = (real_of_num _28674)) = ((real_of_num n) = (real_of_num _28674)).
Proof. exact (MK_COMB (@lem2272989 x n h1) (@lem2272990 _28674)). Qed.
Lemma lem2272993 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2272903 m n) (@lem2272902 m n)). Qed.
Lemma lem2272994 (n : nat) (_28674 : nat) : ((real_of_num n) = (real_of_num _28674)) = (n = _28674).
Proof. exact (@lem2272993 n _28674). Qed.
Lemma lem2272997 (_28674 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : ((term17 x) = (real_of_num _28674)) = (n = _28674).
Proof. exact (TRANS (@lem2272991 _28674 x n h1) (@lem2272994 n _28674)). Qed.
Lemma lem2273000 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term43 x) = (term71 n).
Proof. exact (fun_ext (fun _28674 : nat => @lem2272997 _28674 x n h1)). Qed.
Lemma lem2273001 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2273002 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term57 x) = (term72 n).
Proof. exact (MK_COMB (@lem2273001) (@lem2273000 x n h1)). Qed.
Lemma lem2273004 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2272897 A a) (@lem2272896 A a)). Qed.
Lemma lem2273005 (a : nat) : (term72 a) = True.
Proof. exact (@lem2273004 nat a). Qed.
Lemma lem2273006 (n : nat) : (term72 n) = True.
Proof. exact (@lem2273005 n). Qed.
Lemma lem2273007 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term57 x) = True.
Proof. exact (TRANS (@lem2273002 x n h1) (@lem2273006 n)). Qed.
Lemma lem2273008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2273009 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term59 x) = (or True).
Proof. exact (MK_COMB (@lem2273008) (@lem2273007 x n h1)). Qed.
Lemma lem2273031 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2272909 x y) (@lem2272908 x y)). Qed.
Lemma lem2273032 (x : int) (_28675 : nat) : ((term17 x) = (term26 _28675)) = ((real_of_int x) = (real_of_num _28675)).
Proof. exact (@lem2273031 (real_of_int x) (real_of_num _28675)). Qed.
Lemma lem2273036 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (real_of_int x) = (term26 n).
Proof. exact (h1). Qed.
Lemma lem2273037 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2273038 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term69 x) = (term65 n).
Proof. exact (MK_COMB (@lem2273037) (@lem2273036 x n h1)). Qed.
Lemma lem2273039 (_28675 : nat) : (real_of_num _28675) = (real_of_num _28675).
Proof. exact (eq_refl (real_of_num _28675)). Qed.
Lemma lem2273040 (_28675 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : ((real_of_int x) = (real_of_num _28675)) = ((term26 n) = (real_of_num _28675)).
Proof. exact (MK_COMB (@lem2273038 x n h1) (@lem2273039 _28675)). Qed.
Lemma lem2273043 (_28675 : nat) (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : ((term17 x) = (term26 _28675)) = ((term26 n) = (real_of_num _28675)).
Proof. exact (TRANS (@lem2273032 x _28675) (@lem2273040 _28675 x n h1)). Qed.
Lemma lem2273046 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term44 x) = (term66 n).
Proof. exact (fun_ext (fun _28675 : nat => @lem2273043 _28675 x n h1)). Qed.
Lemma lem2273047 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2273048 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term62 x) = (term67 n).
Proof. exact (MK_COMB (@lem2273047) (@lem2273046 x n h1)). Qed.
Lemma lem2273055 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term63 x) = (term77 n).
Proof. exact (MK_COMB (@lem2273009 x n h1) (@lem2273048 x n h1)). Qed.
Lemma lem2273057 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2273058 (n : nat) : (term77 n) = True.
Proof. exact (@lem2273057 (term67 n)). Qed.
Lemma lem2273059 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term63 x) = True.
Proof. exact (TRANS (@lem2273055 x n h1) (@lem2273058 n)). Qed.
Lemma lem2273060 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : (term20 x) = True.
Proof. exact (TRANS (@lem2272946 x) (@lem2273059 x n h1)). Qed.
Lemma lem2273061 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : True = (term20 x).
Proof. exact (SYM (@lem2273060 x n h1)). Qed.
Lemma lem2273062 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : term20 x.
Proof. exact (EQ_MP (@lem2273061 x n h1) (@lem0)). Qed.
Lemma lem2273063 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : ((real_of_int x) = (term26 n)) = (term20 x).
Proof. exact (prop_ext (fun h2 : (real_of_int x) = (term26 n) => @lem2273062 x n h1) (fun h2 : term20 x => @lem2272732 x n h1)). Qed.
Lemma lem2273064 (x : int) (n : nat) (h1 : (real_of_int x) = (term26 n)) : term20 x.
Proof. exact (EQ_MP (@lem2273063 x n h1) (@lem2272732 x n h1)). Qed.
Lemma lem2273065 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : ((real_of_int x) = (real_of_num n)) = (term20 x).
Proof. exact (prop_ext (fun h2 : (real_of_int x) = (real_of_num n) => @lem2272893 x n h1) (fun h2 : term20 x => @lem2272731 x n h1)). Qed.
Lemma lem2273066 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : term20 x.
Proof. exact (EQ_MP (@lem2273065 x n h1) (@lem2272731 x n h1)). Qed.
Lemma lem2273067 (x : int) (n : nat) (h1 : term25 x n) : term20 x.
Proof. exact (or_elim (@lem2272730 x n h1) (fun h0 : (real_of_int x) = (real_of_num n) => @lem2273066 x n h0) (fun h0 : (real_of_int x) = (term26 n) => @lem2273064 x n h0)). Qed.
Lemma lem2273068 (x : int) : term20 x.
Proof. exact (ex_elim (@lem2272679 x) (fun n : nat => fun h0 : term78 x n => @lem2273067 x n h0)). Qed.
Lemma lem2273073 : term24.
Proof. exact (fun x : int => @lem2273068 x). Qed.
Lemma lem2273074 : term23.
Proof. exact (EQ_MP (@lem2272729) (@lem2273073)). Qed.
