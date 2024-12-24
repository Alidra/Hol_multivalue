Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_add_th_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Require Import EXISTS_REFL_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import OR_EXISTS_THM_spec.
Require Import REAL_EQ_NEG2_spec.
Require Import REAL_NEG_ADD_spec.
Require Import dest_int_rep_spec.
Require Import int_add_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1340231_spec.
Require Import thm1340339_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm17160_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982723_spec.
Require Import thm1982749_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Require Import thm2267742_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem2273786 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2273787 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2273786 A x a h1)). Qed.
Lemma lem2273788 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2273789 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2273788 A a x h1)). Qed.
Lemma lem2273790 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2273787 A x a h1) (fun h1 : a = x => @lem2273789 A a x h1)). Qed.
Lemma lem2273791 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2273790 A a x)). Qed.
Lemma lem2273792 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2273793 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2273792 A) (@lem2273791 A a)). Qed.
Lemma lem2273794 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2273793 A a)). Qed.
Lemma lem2273795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2273796 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2273795 A) (@lem2273794 A)). Qed.
Lemma lem2273797 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2273796 A) (@lem4363 A)). Qed.
Lemma lem2273800 (x : real) (y : real) (h1 : (term8 x y) = (term9 x y)) : (term8 x y) = (term9 x y).
Proof. exact (h1). Qed.
Lemma lem2273801 (x : real) (y : real) (h1 : (term8 x y) = (term9 x y)) : (term9 x y) = (term8 x y).
Proof. exact (SYM (@lem2273800 x y h1)). Qed.
Lemma lem2273802 (x : real) (y : real) (h1 : (term9 x y) = (term8 x y)) : (term9 x y) = (term8 x y).
Proof. exact (h1). Qed.
Lemma lem2273803 (x : real) (y : real) (h1 : (term9 x y) = (term8 x y)) : (term8 x y) = (term9 x y).
Proof. exact (SYM (@lem2273802 x y h1)). Qed.
Lemma lem2273804 (x : real) (y : real) : ((term8 x y) = (term9 x y)) = ((term9 x y) = (term8 x y)).
Proof. exact (prop_ext (fun h1 : (term8 x y) = (term9 x y) => @lem2273801 x y h1) (fun h1 : (term9 x y) = (term8 x y) => @lem2273803 x y h1)). Qed.
Lemma lem2273805 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem2273804 x y)). Qed.
Lemma lem2273806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2273807 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2273806) (@lem2273805 x)). Qed.
Lemma lem2273808 : term14 = term15.
Proof. exact (fun_ext (fun x : real => @lem2273807 x)). Qed.
Lemma lem2273809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2273810 : term16 = term17.
Proof. exact (MK_COMB (@lem2273809) (@lem2273808)). Qed.
Lemma lem2273811 : term17.
Proof. exact (EQ_MP (@lem2273810) (@lem1361095)). Qed.
Lemma lem2273812 {A : Type'} (a : A) : term18 A a.
Proof. exact (@lem2273797 A a). Qed.
Lemma lem2273813 {A : Type'} (a : A) : (term18 A a) = (term3 A a).
Proof. exact (eq_refl (term18 A a)). Qed.
Lemma lem2273814 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2273813 A a) (@lem2273812 A a)). Qed.
Lemma lem2273815 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2273817 (m : nat) : term19 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2273818 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem2273819 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem2273818 m) (@lem2273817 m)). Qed.
Lemma lem2273820 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem2273819 m n). Qed.
Lemma lem2273821 (m : nat) (n : nat) : (term21 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem2273823 (m : nat) : term22 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem2273824 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem2273825 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem2273824 m) (@lem2273823 m)). Qed.
Lemma lem2273826 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem2273825 m n). Qed.
Lemma lem2273827 (m : nat) (n : nat) : (term24 m n) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2273829 (x : real) : term27 x.
Proof. exact (@lem1525370 x). Qed.
Lemma lem2273830 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem2273831 (x : real) : term28 x.
Proof. exact (EQ_MP (@lem2273830 x) (@lem2273829 x)). Qed.
Lemma lem2273832 (x : real) (y : real) : term29 x y.
Proof. exact (@lem2273831 x y). Qed.
Lemma lem2273833 (x : real) (y : real) : (term29 x y) = (((real_neg x) = (real_neg y)) = (x = y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem2273835 (x : real) : term30 x.
Proof. exact (@lem2273811 x). Qed.
Lemma lem2273836 (x : real) : (term30 x) = (term13 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem2273837 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem2273836 x) (@lem2273835 x)). Qed.
Lemma lem2273838 (x : real) (y : real) : term31 x y.
Proof. exact (@lem2273837 x y). Qed.
Lemma lem2273839 (x : real) (y : real) : (term31 x y) = ((term9 x y) = (term8 x y)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem2273841 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2273842 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem2273843 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (EQ_MP (@lem2273842 A P) (@lem2273841 A P)). Qed.
Lemma lem2273844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem2273843 A P Q). Qed.
Lemma lem2273845 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem2273849 (m : nat) (n : nat) (h1 : (term25 m n) = (term26 m n)) : (term25 m n) = (term26 m n).
Proof. exact (h1). Qed.
Lemma lem2273850 (m : nat) (n : nat) (h1 : (term25 m n) = (term26 m n)) : (term26 m n) = (term25 m n).
Proof. exact (SYM (@lem2273849 m n h1)). Qed.
Lemma lem2273851 (m : nat) (n : nat) (h1 : (term26 m n) = (term25 m n)) : (term26 m n) = (term25 m n).
Proof. exact (h1). Qed.
Lemma lem2273852 (m : nat) (n : nat) (h1 : (term26 m n) = (term25 m n)) : (term25 m n) = (term26 m n).
Proof. exact (SYM (@lem2273851 m n h1)). Qed.
Lemma lem2273853 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term26 m n) = (term25 m n)).
Proof. exact (prop_ext (fun h1 : (term25 m n) = (term26 m n) => @lem2273850 m n h1) (fun h1 : (term26 m n) = (term25 m n) => @lem2273852 m n h1)). Qed.
Lemma lem2273854 (m : nat) : (term37 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem2273853 m n)). Qed.
Lemma lem2273855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2273856 (m : nat) : (term23 m) = (term39 m).
Proof. exact (MK_COMB (@lem2273855) (@lem2273854 m)). Qed.
Lemma lem2273857 : term40 = term41.
Proof. exact (fun_ext (fun m : nat => @lem2273856 m)). Qed.
Lemma lem2273858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2273859 : term42 = term43.
Proof. exact (MK_COMB (@lem2273858) (@lem2273857)). Qed.
Lemma lem2273860 : term43.
Proof. exact (EQ_MP (@lem2273859) (@lem1340339)). Qed.
Lemma lem2273861 (x : real) : term44 x.
Proof. exact (@lem1361095 x). Qed.
Lemma lem2273862 (x : real) : (term44 x) = (term12 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem2273863 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem2273862 x) (@lem2273861 x)). Qed.
Lemma lem2273864 (x : real) (y : real) : term45 x y.
Proof. exact (@lem2273863 x y). Qed.
Lemma lem2273865 (x : real) (y : real) : (term45 x y) = ((term8 x y) = (term9 x y)).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem2273867 {A : Type'} (P : A -> Prop) : term46 A P.
Proof. exact (@lem5488 A P). Qed.
Lemma lem2273868 {A : Type'} (P : A -> Prop) : (term46 A P) = (term47 A P).
Proof. exact (eq_refl (term46 A P)). Qed.
Lemma lem2273869 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (EQ_MP (@lem2273868 A P) (@lem2273867 A P)). Qed.
Lemma lem2273870 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term48 A P Q.
Proof. exact (@lem2273869 A P Q). Qed.
Lemma lem2273871 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = ((term36 A P Q) = (term35 A P Q)).
Proof. exact (eq_refl (term48 A P Q)). Qed.
Lemma lem2273873 (m : nat) : term49 m.
Proof. exact (@lem2273860 m). Qed.
Lemma lem2273874 (m : nat) : (term49 m) = (term39 m).
Proof. exact (eq_refl (term49 m)). Qed.
Lemma lem2273875 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem2273874 m) (@lem2273873 m)). Qed.
Lemma lem2273876 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem2273875 m n). Qed.
Lemma lem2273877 (m : nat) (n : nat) : (term50 m n) = ((term26 m n) = (term25 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem2273879 (m : nat) : term51 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem2273880 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem2273881 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem2273880 m) (@lem2273879 m)). Qed.
Lemma lem2273882 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem2273881 m n). Qed.
Lemma lem2273883 (n : nat) (m : nat) : (term53 m n) = ((Peano.le m n) = (term54 n m)).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem2273885 (m : nat) : term55 m.
Proof. exact (@lem96155 m). Qed.
Lemma lem2273886 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem2273887 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem2273886 m) (@lem2273885 m)). Qed.
Lemma lem2273888 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem2273887 m n). Qed.
Lemma lem2273889 (n : nat) (m : nat) : (term57 m n) = (term58 n m).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem2273890 (n : nat) (m : nat) : term58 n m.
Proof. exact (EQ_MP (@lem2273889 n m) (@lem2273888 m n)). Qed.
Lemma lem2273891 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem2273892 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem2273895 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2273896 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2273895 A x a h1)). Qed.
Lemma lem2273897 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2273898 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2273897 A a x h1)). Qed.
Lemma lem2273899 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2273896 A x a h1) (fun h1 : a = x => @lem2273898 A a x h1)). Qed.
Lemma lem2273900 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2273899 A a x)). Qed.
Lemma lem2273901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2273902 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2273901 A) (@lem2273900 A a)). Qed.
Lemma lem2273903 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2273902 A a)). Qed.
Lemma lem2273904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2273905 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2273904 A) (@lem2273903 A)). Qed.
Lemma lem2273906 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2273905 A) (@lem4363 A)). Qed.
Lemma lem2273907 {A : Type'} (a : A) : term18 A a.
Proof. exact (@lem2273906 A a). Qed.
Lemma lem2273908 {A : Type'} (a : A) : (term18 A a) = (term3 A a).
Proof. exact (eq_refl (term18 A a)). Qed.
Lemma lem2273909 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2273908 A a) (@lem2273907 A a)). Qed.
Lemma lem2273910 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2273912 (y : int) : term59 y.
Proof. exact (@lem2267790 y). Qed.
Lemma lem2273913 (y : int) : (term59 y) = (term60 y).
Proof. exact (eq_refl (term59 y)). Qed.
Lemma lem2273914 (y : int) : term60 y.
Proof. exact (EQ_MP (@lem2273913 y) (@lem2273912 y)). Qed.
Lemma lem2273915 (y : int) (n : nat) (h1 : term61 y n) : term61 y n.
Proof. exact (h1). Qed.
Lemma lem2273916 (x : int) : term59 x.
Proof. exact (@lem2267790 x). Qed.
Lemma lem2273917 (x : int) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem2273918 (x : int) : term60 x.
Proof. exact (EQ_MP (@lem2273917 x) (@lem2273916 x)). Qed.
Lemma lem2273919 (x : int) (m : nat) (h1 : term61 x m) : term61 x m.
Proof. exact (h1). Qed.
Lemma lem2273920 (r : real) (h1 : (integer r) = ((term62 r) = r)) : (integer r) = ((term62 r) = r).
Proof. exact (h1). Qed.
Lemma lem2273921 (r : real) (h1 : (integer r) = ((term62 r) = r)) : ((term62 r) = r) = (integer r).
Proof. exact (SYM (@lem2273920 r h1)). Qed.
Lemma lem2273922 (r : real) (h1 : ((term62 r) = r) = (integer r)) : ((term62 r) = r) = (integer r).
Proof. exact (h1). Qed.
Lemma lem2273923 (r : real) (h1 : ((term62 r) = r) = (integer r)) : (integer r) = ((term62 r) = r).
Proof. exact (SYM (@lem2273922 r h1)). Qed.
Lemma lem2273924 (r : real) : ((integer r) = ((term62 r) = r)) = (((term62 r) = r) = (integer r)).
Proof. exact (prop_ext (fun h1 : (integer r) = ((term62 r) = r) => @lem2273921 r h1) (fun h1 : ((term62 r) = r) = (integer r) => @lem2273923 r h1)). Qed.
Lemma lem2273926 (x : int) : term63 x.
Proof. exact (@lem2273783 x). Qed.
Lemma lem2273927 (x : int) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem2273928 (x : int) : term64 x.
Proof. exact (EQ_MP (@lem2273927 x) (@lem2273926 x)). Qed.
Lemma lem2273929 (x : int) (y : int) : term65 x y.
Proof. exact (@lem2273928 x y). Qed.
Lemma lem2273930 (x : int) (y : int) : (term65 x y) = ((int_add x y) = (term66 x y)).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem2273943 (x : int) (y : int) : (int_add x y) = (term66 x y).
Proof. exact (EQ_MP (@lem2273930 x y) (@lem2273929 x y)). Qed.
Lemma lem2273944 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2273945 (x : int) (y : int) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2273944) (@lem2273943 x y)). Qed.
Lemma lem2273946 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2273947 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem2273946) (@lem2273945 x y)). Qed.
Lemma lem2273948 (x : int) (y : int) : (term71 x y) = (term71 x y).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem2273949 (x : int) (y : int) : ((term67 x y) = (term71 x y)) = ((term68 x y) = (term71 x y)).
Proof. exact (MK_COMB (@lem2273947 x y) (@lem2273948 x y)). Qed.
Lemma lem2273951 (r : real) : ((term62 r) = r) = (integer r).
Proof. exact (EQ_MP (@lem2273924 r) (@lem2267742 r)). Qed.
Lemma lem2273952 (x : int) (y : int) : ((term68 x y) = (term71 x y)) = (term72 x y).
Proof. exact (@lem2273951 (term71 x y)). Qed.
Lemma lem2273954 (x : real) : (integer x) = (term73 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.
Lemma lem2273955 (x : int) (y : int) : (term72 x y) = (term74 x y).
Proof. exact (@lem2273954 (term71 x y)). Qed.
Lemma lem2273966 (x : int) (y : int) : ((term68 x y) = (term71 x y)) = (term74 x y).
Proof. exact (TRANS (@lem2273952 x y) (@lem2273955 x y)). Qed.
Lemma lem2273967 (x : int) (y : int) : ((term67 x y) = (term71 x y)) = (term74 x y).
Proof. exact (TRANS (@lem2273949 x y) (@lem2273966 x y)). Qed.
Lemma lem2273968 (x : int) : (term75 x) = (term76 x).
Proof. exact (fun_ext (fun y : int => @lem2273967 x y)). Qed.
Lemma lem2273969 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2273970 (x : int) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem2273969) (@lem2273968 x)). Qed.
Lemma lem2273975 : term79 = term80.
Proof. exact (fun_ext (fun x : int => @lem2273970 x)). Qed.
Lemma lem2273976 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2273977 : term81 = term82.
Proof. exact (MK_COMB (@lem2273976) (@lem2273975)). Qed.
Lemma lem2273982 : term82 = term81.
Proof. exact (SYM (@lem2273977)). Qed.
Lemma lem2273989 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2273990 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem2273991 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (EQ_MP (@lem2273990 A P) (@lem2273989 A P)). Qed.
Lemma lem2273992 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem2273991 A P Q). Qed.
Lemma lem2273993 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem2273995 (m : nat) : term19 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2273996 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem2273997 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem2273996 m) (@lem2273995 m)). Qed.
Lemma lem2273998 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem2273997 m n). Qed.
Lemma lem2273999 (m : nat) (n : nat) : (term21 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem2274001 (m : nat) : term22 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem2274002 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem2274003 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem2274002 m) (@lem2274001 m)). Qed.
Lemma lem2274004 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem2274003 m n). Qed.
Lemma lem2274005 (m : nat) (n : nat) : (term24 m n) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2274008 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2273993 A P Q) (@lem2273992 A P Q)). Qed.
Lemma lem2274009 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2274008 nat P Q). Qed.
Lemma lem2274010 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (@lem2274009 (term87 x y) (term88 x y)). Qed.
Lemma lem2274011 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274013 (x : int) (y : int) (n : nat) : (term90 x y n) = (term91 x y n).
Proof. exact (MK_COMB (@lem2274012) (@lem2274011 x y n)). Qed.
Lemma lem2274014 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274015 (x : int) (y : int) (n : nat) : (term94 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem2274013 x y n) (@lem2274014 x y n)). Qed.
Lemma lem2274016 (x : int) (y : int) : (term96 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274015 x y n)). Qed.
Lemma lem2274017 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274018 (x : int) (y : int) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2274017) (@lem2274016 x y)). Qed.
Lemma lem2274019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274020 (x : int) (y : int) : (term98 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2274019) (@lem2274018 x y)). Qed.
Lemma lem2274021 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274022 (x : int) (y : int) : (term100 x y) = (term87 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274021 x y n)). Qed.
Lemma lem2274023 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274024 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem2274023) (@lem2274022 x y)). Qed.
Lemma lem2274025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274026 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem2274025) (@lem2274024 x y)). Qed.
Lemma lem2274027 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274028 (x : int) (y : int) : (term105 x y) = (term88 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274027 x y n)). Qed.
Lemma lem2274029 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274030 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2274029) (@lem2274028 x y)). Qed.
Lemma lem2274031 (x : int) (y : int) : (term86 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem2274026 x y) (@lem2274030 x y)). Qed.
Lemma lem2274032 (x : int) (y : int) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem2274020 x y) (@lem2274031 x y)). Qed.
Lemma lem2274033 (x : int) (y : int) : (term74 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem2274032 x y) (@lem2274010 x y)). Qed.
Lemma lem2274065 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2274066 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274067 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term109 x) = (term110 m).
Proof. exact (MK_COMB (@lem2274066) (@lem2274065 x m h1)). Qed.
Lemma lem2274069 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2274070 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term25 m n).
Proof. exact (MK_COMB (@lem2274067 x m h1) (@lem2274069 y n h2)). Qed.
Lemma lem2274072 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2274005 m n) (@lem2274004 m n)). Qed.
Lemma lem2274073 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term26 m n).
Proof. exact (TRANS (@lem2274070 x m y n h1 h2) (@lem2274072 m n)). Qed.
Lemma lem2274074 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274075 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term111 x y) = (term112 m n).
Proof. exact (MK_COMB (@lem2274074) (@lem2274073 x m y n h1 h2)). Qed.
Lemma lem2274076 (_28688 : nat) : (real_of_num _28688) = (real_of_num _28688).
Proof. exact (eq_refl (real_of_num _28688)). Qed.
Lemma lem2274077 (_28688 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term71 x y) = (real_of_num _28688)) = ((term26 m n) = (real_of_num _28688)).
Proof. exact (MK_COMB (@lem2274075 x m y n h1 h2) (@lem2274076 _28688)). Qed.
Lemma lem2274079 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2273999 m n) (@lem2273998 m n)). Qed.
Lemma lem2274080 (m : nat) (n : nat) (_28688 : nat) : ((term26 m n) = (real_of_num _28688)) = ((Nat.add m n) = _28688).
Proof. exact (@lem2274079 (Nat.add m n) _28688). Qed.
Lemma lem2274083 (_28688 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term71 x y) = (real_of_num _28688)) = ((Nat.add m n) = _28688).
Proof. exact (TRANS (@lem2274077 _28688 x m y n h1 h2) (@lem2274080 m n _28688)). Qed.
Lemma lem2274086 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term87 x y) = (term113 m n).
Proof. exact (fun_ext (fun _28688 : nat => @lem2274083 _28688 x m y n h1 h2)). Qed.
Lemma lem2274087 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274088 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term102 x y) = (term114 m n).
Proof. exact (MK_COMB (@lem2274087) (@lem2274086 x m y n h1 h2)). Qed.
Lemma lem2274093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274094 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term104 x y) = (term115 m n).
Proof. exact (MK_COMB (@lem2274093) (@lem2274088 x m y n h1 h2)). Qed.
Lemma lem2274120 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2274121 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274122 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term109 x) = (term110 m).
Proof. exact (MK_COMB (@lem2274121) (@lem2274120 x m h1)). Qed.
Lemma lem2274124 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2274125 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term25 m n).
Proof. exact (MK_COMB (@lem2274122 x m h1) (@lem2274124 y n h2)). Qed.
Lemma lem2274127 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2274005 m n) (@lem2274004 m n)). Qed.
Lemma lem2274128 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term26 m n).
Proof. exact (TRANS (@lem2274125 x m y n h1 h2) (@lem2274127 m n)). Qed.
Lemma lem2274129 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274130 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term111 x y) = (term112 m n).
Proof. exact (MK_COMB (@lem2274129) (@lem2274128 x m y n h1 h2)). Qed.
Lemma lem2274131 (_28689 : nat) : (term93 _28689) = (term93 _28689).
Proof. exact (eq_refl (term93 _28689)). Qed.
Lemma lem2274132 (_28689 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term71 x y) = (term93 _28689)) = ((term26 m n) = (term93 _28689)).
Proof. exact (MK_COMB (@lem2274130 x m y n h1 h2) (@lem2274131 _28689)). Qed.
Lemma lem2274137 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term88 x y) = (term116 m n).
Proof. exact (fun_ext (fun _28689 : nat => @lem2274132 _28689 x m y n h1 h2)). Qed.
Lemma lem2274138 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274139 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term107 x y) = (term117 m n).
Proof. exact (MK_COMB (@lem2274138) (@lem2274137 x m y n h1 h2)). Qed.
Lemma lem2274144 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term108 x y) = (term118 m n).
Proof. exact (MK_COMB (@lem2274094 x m y n h1 h2) (@lem2274139 x m y n h1 h2)). Qed.
Lemma lem2274147 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term74 x y) = (term118 m n).
Proof. exact (TRANS (@lem2274033 x y) (@lem2274144 x m y n h1 h2)). Qed.
Lemma lem2274148 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term118 m n) = (term74 x y).
Proof. exact (SYM (@lem2274147 x m y n h1 h2)). Qed.
Lemma lem2274149 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2274150 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem2274151 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (EQ_MP (@lem2274150 A P) (@lem2274149 A P)). Qed.
Lemma lem2274152 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem2274151 A P Q). Qed.
Lemma lem2274153 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem2274168 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2274153 A P Q) (@lem2274152 A P Q)). Qed.
Lemma lem2274169 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2274168 nat P Q). Qed.
Lemma lem2274170 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (@lem2274169 (term87 x y) (term88 x y)). Qed.
Lemma lem2274171 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274173 (x : int) (y : int) (n : nat) : (term90 x y n) = (term91 x y n).
Proof. exact (MK_COMB (@lem2274172) (@lem2274171 x y n)). Qed.
Lemma lem2274174 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274175 (x : int) (y : int) (n : nat) : (term94 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem2274173 x y n) (@lem2274174 x y n)). Qed.
Lemma lem2274176 (x : int) (y : int) : (term96 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274175 x y n)). Qed.
Lemma lem2274177 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274178 (x : int) (y : int) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2274177) (@lem2274176 x y)). Qed.
Lemma lem2274179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274180 (x : int) (y : int) : (term98 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2274179) (@lem2274178 x y)). Qed.
Lemma lem2274181 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274182 (x : int) (y : int) : (term100 x y) = (term87 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274181 x y n)). Qed.
Lemma lem2274183 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274184 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem2274183) (@lem2274182 x y)). Qed.
Lemma lem2274185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274186 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem2274185) (@lem2274184 x y)). Qed.
Lemma lem2274187 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274188 (x : int) (y : int) : (term105 x y) = (term88 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274187 x y n)). Qed.
Lemma lem2274189 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274190 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2274189) (@lem2274188 x y)). Qed.
Lemma lem2274191 (x : int) (y : int) : (term86 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem2274186 x y) (@lem2274190 x y)). Qed.
Lemma lem2274192 (x : int) (y : int) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem2274180 x y) (@lem2274191 x y)). Qed.
Lemma lem2274193 (x : int) (y : int) : (term74 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem2274192 x y) (@lem2274170 x y)). Qed.
Lemma lem2274218 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2274219 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274220 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term109 x) = (term110 m).
Proof. exact (MK_COMB (@lem2274219) (@lem2274218 x m h1)). Qed.
Lemma lem2274222 (y : int) (n : nat) (h1 : (real_of_int y) = (term93 n)) : (real_of_int y) = (term93 n).
Proof. exact (h1). Qed.
Lemma lem2274223 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term71 x y) = (term119 m n).
Proof. exact (MK_COMB (@lem2274220 x m h1) (@lem2274222 y n h2)). Qed.
Lemma lem2274224 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274225 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term111 x y) = (term120 m n).
Proof. exact (MK_COMB (@lem2274224) (@lem2274223 x m y n h1 h2)). Qed.
Lemma lem2274226 (_28690 : nat) : (real_of_num _28690) = (real_of_num _28690).
Proof. exact (eq_refl (real_of_num _28690)). Qed.
Lemma lem2274227 (_28690 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : ((term71 x y) = (real_of_num _28690)) = ((term119 m n) = (real_of_num _28690)).
Proof. exact (MK_COMB (@lem2274225 x m y n h1 h2) (@lem2274226 _28690)). Qed.
Lemma lem2274232 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term87 x y) = (term121 m n).
Proof. exact (fun_ext (fun _28690 : nat => @lem2274227 _28690 x m y n h1 h2)). Qed.
Lemma lem2274233 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274234 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term102 x y) = (term122 m n).
Proof. exact (MK_COMB (@lem2274233) (@lem2274232 x m y n h1 h2)). Qed.
Lemma lem2274239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274240 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term104 x y) = (term123 m n).
Proof. exact (MK_COMB (@lem2274239) (@lem2274234 x m y n h1 h2)). Qed.
Lemma lem2274263 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2274264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274265 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term109 x) = (term110 m).
Proof. exact (MK_COMB (@lem2274264) (@lem2274263 x m h1)). Qed.
Lemma lem2274267 (y : int) (n : nat) (h1 : (real_of_int y) = (term93 n)) : (real_of_int y) = (term93 n).
Proof. exact (h1). Qed.
Lemma lem2274268 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term71 x y) = (term119 m n).
Proof. exact (MK_COMB (@lem2274265 x m h1) (@lem2274267 y n h2)). Qed.
Lemma lem2274269 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274270 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term111 x y) = (term120 m n).
Proof. exact (MK_COMB (@lem2274269) (@lem2274268 x m y n h1 h2)). Qed.
Lemma lem2274271 (_28691 : nat) : (term93 _28691) = (term93 _28691).
Proof. exact (eq_refl (term93 _28691)). Qed.
Lemma lem2274272 (_28691 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : ((term71 x y) = (term93 _28691)) = ((term119 m n) = (term93 _28691)).
Proof. exact (MK_COMB (@lem2274270 x m y n h1 h2) (@lem2274271 _28691)). Qed.
Lemma lem2274277 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term88 x y) = (term124 m n).
Proof. exact (fun_ext (fun _28691 : nat => @lem2274272 _28691 x m y n h1 h2)). Qed.
Lemma lem2274278 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274279 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term107 x y) = (term125 m n).
Proof. exact (MK_COMB (@lem2274278) (@lem2274277 x m y n h1 h2)). Qed.
Lemma lem2274284 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term108 x y) = (term126 m n).
Proof. exact (MK_COMB (@lem2274240 x m y n h1 h2) (@lem2274279 x m y n h1 h2)). Qed.
Lemma lem2274287 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term74 x y) = (term126 m n).
Proof. exact (TRANS (@lem2274193 x y) (@lem2274284 x m y n h1 h2)). Qed.
Lemma lem2274288 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : (term126 m n) = (term74 x y).
Proof. exact (SYM (@lem2274287 x m y n h1 h2)). Qed.
Lemma lem2274289 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2274290 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem2274291 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (EQ_MP (@lem2274290 A P) (@lem2274289 A P)). Qed.
Lemma lem2274292 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem2274291 A P Q). Qed.
Lemma lem2274293 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem2274308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2274293 A P Q) (@lem2274292 A P Q)). Qed.
Lemma lem2274309 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2274308 nat P Q). Qed.
Lemma lem2274310 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (@lem2274309 (term87 x y) (term88 x y)). Qed.
Lemma lem2274311 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274312 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274313 (x : int) (y : int) (n : nat) : (term90 x y n) = (term91 x y n).
Proof. exact (MK_COMB (@lem2274312) (@lem2274311 x y n)). Qed.
Lemma lem2274314 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274315 (x : int) (y : int) (n : nat) : (term94 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem2274313 x y n) (@lem2274314 x y n)). Qed.
Lemma lem2274316 (x : int) (y : int) : (term96 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274315 x y n)). Qed.
Lemma lem2274317 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274318 (x : int) (y : int) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2274317) (@lem2274316 x y)). Qed.
Lemma lem2274319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274320 (x : int) (y : int) : (term98 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2274319) (@lem2274318 x y)). Qed.
Lemma lem2274321 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274322 (x : int) (y : int) : (term100 x y) = (term87 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274321 x y n)). Qed.
Lemma lem2274323 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274324 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem2274323) (@lem2274322 x y)). Qed.
Lemma lem2274325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274326 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem2274325) (@lem2274324 x y)). Qed.
Lemma lem2274327 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274328 (x : int) (y : int) : (term105 x y) = (term88 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274327 x y n)). Qed.
Lemma lem2274329 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274330 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2274329) (@lem2274328 x y)). Qed.
Lemma lem2274331 (x : int) (y : int) : (term86 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem2274326 x y) (@lem2274330 x y)). Qed.
Lemma lem2274332 (x : int) (y : int) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem2274320 x y) (@lem2274331 x y)). Qed.
Lemma lem2274333 (x : int) (y : int) : (term74 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem2274332 x y) (@lem2274310 x y)). Qed.
Lemma lem2274358 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (real_of_int x) = (term93 m).
Proof. exact (h1). Qed.
Lemma lem2274359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274360 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (term109 x) = (term127 m).
Proof. exact (MK_COMB (@lem2274359) (@lem2274358 x m h1)). Qed.
Lemma lem2274362 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2274363 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term128 m n).
Proof. exact (MK_COMB (@lem2274360 x m h1) (@lem2274362 y n h2)). Qed.
Lemma lem2274364 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274365 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term111 x y) = (term129 m n).
Proof. exact (MK_COMB (@lem2274364) (@lem2274363 x m y n h1 h2)). Qed.
Lemma lem2274366 (_28692 : nat) : (real_of_num _28692) = (real_of_num _28692).
Proof. exact (eq_refl (real_of_num _28692)). Qed.
Lemma lem2274367 (_28692 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term71 x y) = (real_of_num _28692)) = ((term128 m n) = (real_of_num _28692)).
Proof. exact (MK_COMB (@lem2274365 x m y n h1 h2) (@lem2274366 _28692)). Qed.
Lemma lem2274372 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term87 x y) = (term130 m n).
Proof. exact (fun_ext (fun _28692 : nat => @lem2274367 _28692 x m y n h1 h2)). Qed.
Lemma lem2274373 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274374 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term102 x y) = (term131 m n).
Proof. exact (MK_COMB (@lem2274373) (@lem2274372 x m y n h1 h2)). Qed.
Lemma lem2274379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274380 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term104 x y) = (term132 m n).
Proof. exact (MK_COMB (@lem2274379) (@lem2274374 x m y n h1 h2)). Qed.
Lemma lem2274403 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (real_of_int x) = (term93 m).
Proof. exact (h1). Qed.
Lemma lem2274404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274405 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (term109 x) = (term127 m).
Proof. exact (MK_COMB (@lem2274404) (@lem2274403 x m h1)). Qed.
Lemma lem2274407 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2274408 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term128 m n).
Proof. exact (MK_COMB (@lem2274405 x m h1) (@lem2274407 y n h2)). Qed.
Lemma lem2274409 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274410 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term111 x y) = (term129 m n).
Proof. exact (MK_COMB (@lem2274409) (@lem2274408 x m y n h1 h2)). Qed.
Lemma lem2274411 (_28693 : nat) : (term93 _28693) = (term93 _28693).
Proof. exact (eq_refl (term93 _28693)). Qed.
Lemma lem2274412 (_28693 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term71 x y) = (term93 _28693)) = ((term128 m n) = (term93 _28693)).
Proof. exact (MK_COMB (@lem2274410 x m y n h1 h2) (@lem2274411 _28693)). Qed.
Lemma lem2274417 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term88 x y) = (term133 m n).
Proof. exact (fun_ext (fun _28693 : nat => @lem2274412 _28693 x m y n h1 h2)). Qed.
Lemma lem2274418 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274419 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term107 x y) = (term134 m n).
Proof. exact (MK_COMB (@lem2274418) (@lem2274417 x m y n h1 h2)). Qed.
Lemma lem2274424 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term108 x y) = (term135 m n).
Proof. exact (MK_COMB (@lem2274380 x m y n h1 h2) (@lem2274419 x m y n h1 h2)). Qed.
Lemma lem2274427 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term74 x y) = (term135 m n).
Proof. exact (TRANS (@lem2274333 x y) (@lem2274424 x m y n h1 h2)). Qed.
Lemma lem2274428 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term135 m n) = (term74 x y).
Proof. exact (SYM (@lem2274427 x m y n h1 h2)). Qed.
Lemma lem2274429 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2274430 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem2274431 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (EQ_MP (@lem2274430 A P) (@lem2274429 A P)). Qed.
Lemma lem2274432 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem2274431 A P Q). Qed.
Lemma lem2274433 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem2274448 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2274433 A P Q) (@lem2274432 A P Q)). Qed.
Lemma lem2274449 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2274448 nat P Q). Qed.
Lemma lem2274450 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (@lem2274449 (term87 x y) (term88 x y)). Qed.
Lemma lem2274451 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274453 (x : int) (y : int) (n : nat) : (term90 x y n) = (term91 x y n).
Proof. exact (MK_COMB (@lem2274452) (@lem2274451 x y n)). Qed.
Lemma lem2274454 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274455 (x : int) (y : int) (n : nat) : (term94 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem2274453 x y n) (@lem2274454 x y n)). Qed.
Lemma lem2274456 (x : int) (y : int) : (term96 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274455 x y n)). Qed.
Lemma lem2274457 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274458 (x : int) (y : int) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2274457) (@lem2274456 x y)). Qed.
Lemma lem2274459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274460 (x : int) (y : int) : (term98 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2274459) (@lem2274458 x y)). Qed.
Lemma lem2274461 (x : int) (y : int) (n : nat) : (term89 x y n) = ((term71 x y) = (real_of_num n)).
Proof. exact (eq_refl (term89 x y n)). Qed.
Lemma lem2274462 (x : int) (y : int) : (term100 x y) = (term87 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274461 x y n)). Qed.
Lemma lem2274463 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274464 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem2274463) (@lem2274462 x y)). Qed.
Lemma lem2274465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274466 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem2274465) (@lem2274464 x y)). Qed.
Lemma lem2274467 (x : int) (y : int) (n : nat) : (term92 x y n) = ((term71 x y) = (term93 n)).
Proof. exact (eq_refl (term92 x y n)). Qed.
Lemma lem2274468 (x : int) (y : int) : (term105 x y) = (term88 x y).
Proof. exact (fun_ext (fun n : nat => @lem2274467 x y n)). Qed.
Lemma lem2274469 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274470 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2274469) (@lem2274468 x y)). Qed.
Lemma lem2274471 (x : int) (y : int) : (term86 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem2274466 x y) (@lem2274470 x y)). Qed.
Lemma lem2274472 (x : int) (y : int) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem2274460 x y) (@lem2274471 x y)). Qed.
Lemma lem2274473 (x : int) (y : int) : (term74 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem2274472 x y) (@lem2274450 x y)). Qed.
Lemma lem2274498 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (real_of_int x) = (term93 m).
Proof. exact (h1). Qed.
Lemma lem2274499 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274500 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (term109 x) = (term127 m).
Proof. exact (MK_COMB (@lem2274499) (@lem2274498 x m h1)). Qed.
Lemma lem2274502 (y : int) (n : nat) (h1 : (real_of_int y) = (term93 n)) : (real_of_int y) = (term93 n).
Proof. exact (h1). Qed.
Lemma lem2274503 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term71 x y) = (term136 m n).
Proof. exact (MK_COMB (@lem2274500 x m h1) (@lem2274502 y n h2)). Qed.
Lemma lem2274504 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274505 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term111 x y) = (term137 m n).
Proof. exact (MK_COMB (@lem2274504) (@lem2274503 x m y n h1 h2)). Qed.
Lemma lem2274506 (_28694 : nat) : (real_of_num _28694) = (real_of_num _28694).
Proof. exact (eq_refl (real_of_num _28694)). Qed.
Lemma lem2274507 (_28694 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : ((term71 x y) = (real_of_num _28694)) = ((term136 m n) = (real_of_num _28694)).
Proof. exact (MK_COMB (@lem2274505 x m y n h1 h2) (@lem2274506 _28694)). Qed.
Lemma lem2274512 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term87 x y) = (term138 m n).
Proof. exact (fun_ext (fun _28694 : nat => @lem2274507 _28694 x m y n h1 h2)). Qed.
Lemma lem2274513 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274514 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term102 x y) = (term139 m n).
Proof. exact (MK_COMB (@lem2274513) (@lem2274512 x m y n h1 h2)). Qed.
Lemma lem2274519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274520 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term104 x y) = (term140 m n).
Proof. exact (MK_COMB (@lem2274519) (@lem2274514 x m y n h1 h2)). Qed.
Lemma lem2274543 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (real_of_int x) = (term93 m).
Proof. exact (h1). Qed.
Lemma lem2274544 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2274545 (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : (term109 x) = (term127 m).
Proof. exact (MK_COMB (@lem2274544) (@lem2274543 x m h1)). Qed.
Lemma lem2274547 (y : int) (n : nat) (h1 : (real_of_int y) = (term93 n)) : (real_of_int y) = (term93 n).
Proof. exact (h1). Qed.
Lemma lem2274548 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term71 x y) = (term136 m n).
Proof. exact (MK_COMB (@lem2274545 x m h1) (@lem2274547 y n h2)). Qed.
Lemma lem2274549 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274550 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term111 x y) = (term137 m n).
Proof. exact (MK_COMB (@lem2274549) (@lem2274548 x m y n h1 h2)). Qed.
Lemma lem2274551 (_28695 : nat) : (term93 _28695) = (term93 _28695).
Proof. exact (eq_refl (term93 _28695)). Qed.
Lemma lem2274552 (_28695 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : ((term71 x y) = (term93 _28695)) = ((term136 m n) = (term93 _28695)).
Proof. exact (MK_COMB (@lem2274550 x m y n h1 h2) (@lem2274551 _28695)). Qed.
Lemma lem2274557 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term88 x y) = (term141 m n).
Proof. exact (fun_ext (fun _28695 : nat => @lem2274552 _28695 x m y n h1 h2)). Qed.
Lemma lem2274558 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274559 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term107 x y) = (term142 m n).
Proof. exact (MK_COMB (@lem2274558) (@lem2274557 x m y n h1 h2)). Qed.
Lemma lem2274564 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term108 x y) = (term143 m n).
Proof. exact (MK_COMB (@lem2274520 x m y n h1 h2) (@lem2274559 x m y n h1 h2)). Qed.
Lemma lem2274567 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term74 x y) = (term143 m n).
Proof. exact (TRANS (@lem2274473 x y) (@lem2274564 x m y n h1 h2)). Qed.
Lemma lem2274568 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : (term143 m n) = (term74 x y).
Proof. exact (SYM (@lem2274567 x m y n h1 h2)). Qed.
Lemma lem2274572 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2273910 A a) (@lem2273909 A a)). Qed.
Lemma lem2274573 (a : nat) : (term144 a) = True.
Proof. exact (@lem2274572 nat a). Qed.
Lemma lem2274574 (m : nat) (n : nat) : (term114 m n) = True.
Proof. exact (@lem2274573 (Nat.add m n)). Qed.
Lemma lem2274575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274576 (m : nat) (n : nat) : (term115 m n) = (or True).
Proof. exact (MK_COMB (@lem2274575) (@lem2274574 m n)). Qed.
Lemma lem2274585 (m : nat) (n : nat) : (term117 m n) = (term117 m n).
Proof. exact (eq_refl (term117 m n)). Qed.
Lemma lem2274586 (m : nat) (n : nat) : (term118 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem2274576 m n) (@lem2274585 m n)). Qed.
Lemma lem2274588 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2274589 (m : nat) (n : nat) : (term145 m n) = True.
Proof. exact (@lem2274588 (term117 m n)). Qed.
Lemma lem2274590 (m : nat) (n : nat) : (term118 m n) = True.
Proof. exact (TRANS (@lem2274586 m n) (@lem2274589 m n)). Qed.
Lemma lem2274591 (m : nat) (n : nat) : True = (term118 m n).
Proof. exact (SYM (@lem2274590 m n)). Qed.
Lemma lem2274592 (m : nat) (n : nat) : term118 m n.
Proof. exact (EQ_MP (@lem2274591 m n) (@lem0)). Qed.
Lemma lem2274656 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274664 (n : nat) (m : nat) : (term146 m n) = (term147 n m).
Proof. exact (MK_COMB (@lem2274663) (@lem2274656 n m)). Qed.
Lemma lem2274679 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem2274680 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (MK_COMB (@lem2274664 n m) (@lem2274679 m n)). Qed.
Lemma lem2274683 (m : nat) (n : nat) : (term149 m n) = (term148 m n).
Proof. exact (SYM (@lem2274680 m n)). Qed.
Lemma lem2274687 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274688 (m : nat) (n : nat) : (Peano.le n m) = (term54 m n).
Proof. exact (@lem2274687 m n). Qed.
Lemma lem2274695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274696 (m : nat) (n : nat) : (term146 n m) = (term147 m n).
Proof. exact (MK_COMB (@lem2274695) (@lem2274688 m n)). Qed.
Lemma lem2274711 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem2274712 (m : nat) (n : nat) : (term150 m n) = (term151 m n).
Proof. exact (MK_COMB (@lem2274696 m n) (@lem2274711 m n)). Qed.
Lemma lem2274715 (m : nat) (n : nat) : (term151 m n) = (term150 m n).
Proof. exact (SYM (@lem2274712 m n)). Qed.
Lemma lem2274719 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274726 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274727 (n : nat) (m : nat) : (term146 m n) = (term147 n m).
Proof. exact (MK_COMB (@lem2274726) (@lem2274719 n m)). Qed.
Lemma lem2274742 (m : nat) (n : nat) : (term135 m n) = (term135 m n).
Proof. exact (eq_refl (term135 m n)). Qed.
Lemma lem2274743 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (MK_COMB (@lem2274727 n m) (@lem2274742 m n)). Qed.
Lemma lem2274746 (m : nat) (n : nat) : (term153 m n) = (term152 m n).
Proof. exact (SYM (@lem2274743 m n)). Qed.
Lemma lem2274750 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274751 (m : nat) (n : nat) : (Peano.le n m) = (term54 m n).
Proof. exact (@lem2274750 m n). Qed.
Lemma lem2274758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274759 (m : nat) (n : nat) : (term146 n m) = (term147 m n).
Proof. exact (MK_COMB (@lem2274758) (@lem2274751 m n)). Qed.
Lemma lem2274774 (m : nat) (n : nat) : (term135 m n) = (term135 m n).
Proof. exact (eq_refl (term135 m n)). Qed.
Lemma lem2274775 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (MK_COMB (@lem2274759 m n) (@lem2274774 m n)). Qed.
Lemma lem2274778 (m : nat) (n : nat) : (term155 m n) = (term154 m n).
Proof. exact (SYM (@lem2274775 m n)). Qed.
Lemma lem2274782 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274790 (n : nat) (m : nat) : (term146 m n) = (term147 n m).
Proof. exact (MK_COMB (@lem2274789) (@lem2274782 n m)). Qed.
Lemma lem2274805 (m : nat) (n : nat) : (term143 m n) = (term143 m n).
Proof. exact (eq_refl (term143 m n)). Qed.
Lemma lem2274806 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem2274790 n m) (@lem2274805 m n)). Qed.
Lemma lem2274809 (m : nat) (n : nat) : (term157 m n) = (term156 m n).
Proof. exact (SYM (@lem2274806 m n)). Qed.
Lemma lem2274813 (n : nat) (m : nat) : (Peano.le m n) = (term54 n m).
Proof. exact (EQ_MP (@lem2273883 n m) (@lem2273882 m n)). Qed.
Lemma lem2274814 (m : nat) (n : nat) : (Peano.le n m) = (term54 m n).
Proof. exact (@lem2274813 m n). Qed.
Lemma lem2274821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2274822 (m : nat) (n : nat) : (term146 n m) = (term147 m n).
Proof. exact (MK_COMB (@lem2274821) (@lem2274814 m n)). Qed.
Lemma lem2274837 (m : nat) (n : nat) : (term143 m n) = (term143 m n).
Proof. exact (eq_refl (term143 m n)). Qed.
Lemma lem2274838 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (MK_COMB (@lem2274822 m n) (@lem2274837 m n)). Qed.
Lemma lem2274841 (m : nat) (n : nat) : (term159 m n) = (term158 m n).
Proof. exact (SYM (@lem2274838 m n)). Qed.
Lemma lem2274842 (n : nat) (m : nat) (h1 : term54 n m) : term54 n m.
Proof. exact (h1). Qed.
Lemma lem2274843 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem2274844 (m : nat) : (term160 m) = (term160 m).
Proof. exact (eq_refl (term160 m)). Qed.
Lemma lem2274845 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term161 m n) = (term162 m d).
Proof. exact (MK_COMB (@lem2274844 m) (@lem2274843 n m d h1)). Qed.
Lemma lem2274846 (m : nat) (d : nat) : (term162 m d) = (term163 m d).
Proof. exact (eq_refl (term162 m d)). Qed.
Lemma lem2274847 (m : nat) (n : nat) : (term164 m n) = (term164 m n).
Proof. exact (eq_refl (term164 m n)). Qed.
Lemma lem2274848 (n : nat) (m : nat) (d : nat) : ((term161 m n) = (term162 m d)) = ((term161 m n) = (term163 m d)).
Proof. exact (MK_COMB (@lem2274847 m n) (@lem2274846 m d)). Qed.
Lemma lem2274849 (m : nat) (n : nat) : (term161 m n) = (term126 m n).
Proof. exact (eq_refl (term161 m n)). Qed.
Lemma lem2274850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274851 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem2274850) (@lem2274849 m n)). Qed.
Lemma lem2274852 (m : nat) (d : nat) : (term163 m d) = (term163 m d).
Proof. exact (eq_refl (term163 m d)). Qed.
Lemma lem2274853 (n : nat) (m : nat) (d : nat) : ((term161 m n) = (term163 m d)) = ((term126 m n) = (term163 m d)).
Proof. exact (MK_COMB (@lem2274851 m n) (@lem2274852 m d)). Qed.
Lemma lem2274854 (n : nat) (m : nat) (d : nat) : ((term161 m n) = (term162 m d)) = ((term126 m n) = (term163 m d)).
Proof. exact (TRANS (@lem2274848 n m d) (@lem2274853 n m d)). Qed.
Lemma lem2274855 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term126 m n) = (term163 m d).
Proof. exact (EQ_MP (@lem2274854 n m d) (@lem2274845 n m d h1)). Qed.
Lemma lem2274856 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term163 m d) = (term126 m n).
Proof. exact (SYM (@lem2274855 n m d h1)). Qed.
Lemma lem2274857 (m : nat) (n : nat) (h1 : term54 m n) : term54 m n.
Proof. exact (h1). Qed.
Lemma lem2274858 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem2274859 (n : nat) : (term166 n) = (term166 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem2274860 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term167 n m) = (term168 n d).
Proof. exact (MK_COMB (@lem2274859 n) (@lem2274858 m n d h1)). Qed.
Lemma lem2274861 (d : nat) (n : nat) : (term168 n d) = (term169 d n).
Proof. exact (eq_refl (term168 n d)). Qed.
Lemma lem2274862 (n : nat) (m : nat) : (term170 n m) = (term170 n m).
Proof. exact (eq_refl (term170 n m)). Qed.
Lemma lem2274863 (m : nat) (d : nat) (n : nat) : ((term167 n m) = (term168 n d)) = ((term167 n m) = (term169 d n)).
Proof. exact (MK_COMB (@lem2274862 n m) (@lem2274861 d n)). Qed.
Lemma lem2274864 (m : nat) (n : nat) : (term167 n m) = (term126 m n).
Proof. exact (eq_refl (term167 n m)). Qed.
Lemma lem2274865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274866 (m : nat) (n : nat) : (term170 n m) = (term165 m n).
Proof. exact (MK_COMB (@lem2274865) (@lem2274864 m n)). Qed.
Lemma lem2274867 (d : nat) (n : nat) : (term169 d n) = (term169 d n).
Proof. exact (eq_refl (term169 d n)). Qed.
Lemma lem2274868 (m : nat) (d : nat) (n : nat) : ((term167 n m) = (term169 d n)) = ((term126 m n) = (term169 d n)).
Proof. exact (MK_COMB (@lem2274866 m n) (@lem2274867 d n)). Qed.
Lemma lem2274869 (m : nat) (d : nat) (n : nat) : ((term167 n m) = (term168 n d)) = ((term126 m n) = (term169 d n)).
Proof. exact (TRANS (@lem2274863 m d n) (@lem2274868 m d n)). Qed.
Lemma lem2274870 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term126 m n) = (term169 d n).
Proof. exact (EQ_MP (@lem2274869 m d n) (@lem2274860 m n d h1)). Qed.
Lemma lem2274871 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term169 d n) = (term126 m n).
Proof. exact (SYM (@lem2274870 m n d h1)). Qed.
Lemma lem2274872 (n : nat) (m : nat) (h1 : term54 n m) : term54 n m.
Proof. exact (h1). Qed.
Lemma lem2274873 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem2274874 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem2274875 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term172 m n) = (term173 m d).
Proof. exact (MK_COMB (@lem2274874 m) (@lem2274873 n m d h1)). Qed.
Lemma lem2274876 (m : nat) (d : nat) : (term173 m d) = (term174 m d).
Proof. exact (eq_refl (term173 m d)). Qed.
Lemma lem2274877 (m : nat) (n : nat) : (term175 m n) = (term175 m n).
Proof. exact (eq_refl (term175 m n)). Qed.
Lemma lem2274878 (n : nat) (m : nat) (d : nat) : ((term172 m n) = (term173 m d)) = ((term172 m n) = (term174 m d)).
Proof. exact (MK_COMB (@lem2274877 m n) (@lem2274876 m d)). Qed.
Lemma lem2274879 (m : nat) (n : nat) : (term172 m n) = (term135 m n).
Proof. exact (eq_refl (term172 m n)). Qed.
Lemma lem2274880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274881 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (MK_COMB (@lem2274880) (@lem2274879 m n)). Qed.
Lemma lem2274882 (m : nat) (d : nat) : (term174 m d) = (term174 m d).
Proof. exact (eq_refl (term174 m d)). Qed.
Lemma lem2274883 (n : nat) (m : nat) (d : nat) : ((term172 m n) = (term174 m d)) = ((term135 m n) = (term174 m d)).
Proof. exact (MK_COMB (@lem2274881 m n) (@lem2274882 m d)). Qed.
Lemma lem2274884 (n : nat) (m : nat) (d : nat) : ((term172 m n) = (term173 m d)) = ((term135 m n) = (term174 m d)).
Proof. exact (TRANS (@lem2274878 n m d) (@lem2274883 n m d)). Qed.
Lemma lem2274885 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term135 m n) = (term174 m d).
Proof. exact (EQ_MP (@lem2274884 n m d) (@lem2274875 n m d h1)). Qed.
Lemma lem2274886 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term174 m d) = (term135 m n).
Proof. exact (SYM (@lem2274885 n m d h1)). Qed.
Lemma lem2274887 (m : nat) (n : nat) (h1 : term54 m n) : term54 m n.
Proof. exact (h1). Qed.
Lemma lem2274888 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem2274889 (n : nat) : (term177 n) = (term177 n).
Proof. exact (eq_refl (term177 n)). Qed.
Lemma lem2274890 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term178 n m) = (term179 n d).
Proof. exact (MK_COMB (@lem2274889 n) (@lem2274888 m n d h1)). Qed.
Lemma lem2274891 (d : nat) (n : nat) : (term179 n d) = (term180 d n).
Proof. exact (eq_refl (term179 n d)). Qed.
Lemma lem2274892 (n : nat) (m : nat) : (term181 n m) = (term181 n m).
Proof. exact (eq_refl (term181 n m)). Qed.
Lemma lem2274893 (m : nat) (d : nat) (n : nat) : ((term178 n m) = (term179 n d)) = ((term178 n m) = (term180 d n)).
Proof. exact (MK_COMB (@lem2274892 n m) (@lem2274891 d n)). Qed.
Lemma lem2274894 (m : nat) (n : nat) : (term178 n m) = (term135 m n).
Proof. exact (eq_refl (term178 n m)). Qed.
Lemma lem2274895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274896 (m : nat) (n : nat) : (term181 n m) = (term176 m n).
Proof. exact (MK_COMB (@lem2274895) (@lem2274894 m n)). Qed.
Lemma lem2274897 (d : nat) (n : nat) : (term180 d n) = (term180 d n).
Proof. exact (eq_refl (term180 d n)). Qed.
Lemma lem2274898 (m : nat) (d : nat) (n : nat) : ((term178 n m) = (term180 d n)) = ((term135 m n) = (term180 d n)).
Proof. exact (MK_COMB (@lem2274896 m n) (@lem2274897 d n)). Qed.
Lemma lem2274899 (m : nat) (d : nat) (n : nat) : ((term178 n m) = (term179 n d)) = ((term135 m n) = (term180 d n)).
Proof. exact (TRANS (@lem2274893 m d n) (@lem2274898 m d n)). Qed.
Lemma lem2274900 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term135 m n) = (term180 d n).
Proof. exact (EQ_MP (@lem2274899 m d n) (@lem2274890 m n d h1)). Qed.
Lemma lem2274901 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term180 d n) = (term135 m n).
Proof. exact (SYM (@lem2274900 m n d h1)). Qed.
Lemma lem2274902 (n : nat) (m : nat) (h1 : term54 n m) : term54 n m.
Proof. exact (h1). Qed.
Lemma lem2274903 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem2274904 (m : nat) : (term182 m) = (term182 m).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem2274905 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term183 m n) = (term184 m d).
Proof. exact (MK_COMB (@lem2274904 m) (@lem2274903 n m d h1)). Qed.
Lemma lem2274906 (m : nat) (d : nat) : (term184 m d) = (term185 m d).
Proof. exact (eq_refl (term184 m d)). Qed.
Lemma lem2274907 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem2274908 (n : nat) (m : nat) (d : nat) : ((term183 m n) = (term184 m d)) = ((term183 m n) = (term185 m d)).
Proof. exact (MK_COMB (@lem2274907 m n) (@lem2274906 m d)). Qed.
Lemma lem2274909 (m : nat) (n : nat) : (term183 m n) = (term143 m n).
Proof. exact (eq_refl (term183 m n)). Qed.
Lemma lem2274910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274911 (m : nat) (n : nat) : (term186 m n) = (term187 m n).
Proof. exact (MK_COMB (@lem2274910) (@lem2274909 m n)). Qed.
Lemma lem2274912 (m : nat) (d : nat) : (term185 m d) = (term185 m d).
Proof. exact (eq_refl (term185 m d)). Qed.
Lemma lem2274913 (n : nat) (m : nat) (d : nat) : ((term183 m n) = (term185 m d)) = ((term143 m n) = (term185 m d)).
Proof. exact (MK_COMB (@lem2274911 m n) (@lem2274912 m d)). Qed.
Lemma lem2274914 (n : nat) (m : nat) (d : nat) : ((term183 m n) = (term184 m d)) = ((term143 m n) = (term185 m d)).
Proof. exact (TRANS (@lem2274908 n m d) (@lem2274913 n m d)). Qed.
Lemma lem2274915 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term143 m n) = (term185 m d).
Proof. exact (EQ_MP (@lem2274914 n m d) (@lem2274905 n m d h1)). Qed.
Lemma lem2274916 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term185 m d) = (term143 m n).
Proof. exact (SYM (@lem2274915 n m d h1)). Qed.
Lemma lem2274917 (m : nat) (n : nat) (h1 : term54 m n) : term54 m n.
Proof. exact (h1). Qed.
Lemma lem2274918 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem2274919 (n : nat) : (term188 n) = (term188 n).
Proof. exact (eq_refl (term188 n)). Qed.
Lemma lem2274920 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term189 n m) = (term190 n d).
Proof. exact (MK_COMB (@lem2274919 n) (@lem2274918 m n d h1)). Qed.
Lemma lem2274921 (d : nat) (n : nat) : (term190 n d) = (term191 d n).
Proof. exact (eq_refl (term190 n d)). Qed.
Lemma lem2274922 (n : nat) (m : nat) : (term192 n m) = (term192 n m).
Proof. exact (eq_refl (term192 n m)). Qed.
Lemma lem2274923 (m : nat) (d : nat) (n : nat) : ((term189 n m) = (term190 n d)) = ((term189 n m) = (term191 d n)).
Proof. exact (MK_COMB (@lem2274922 n m) (@lem2274921 d n)). Qed.
Lemma lem2274924 (m : nat) (n : nat) : (term189 n m) = (term143 m n).
Proof. exact (eq_refl (term189 n m)). Qed.
Lemma lem2274925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274926 (m : nat) (n : nat) : (term192 n m) = (term187 m n).
Proof. exact (MK_COMB (@lem2274925) (@lem2274924 m n)). Qed.
Lemma lem2274927 (d : nat) (n : nat) : (term191 d n) = (term191 d n).
Proof. exact (eq_refl (term191 d n)). Qed.
Lemma lem2274928 (m : nat) (d : nat) (n : nat) : ((term189 n m) = (term191 d n)) = ((term143 m n) = (term191 d n)).
Proof. exact (MK_COMB (@lem2274926 m n) (@lem2274927 d n)). Qed.
Lemma lem2274929 (m : nat) (d : nat) (n : nat) : ((term189 n m) = (term190 n d)) = ((term143 m n) = (term191 d n)).
Proof. exact (TRANS (@lem2274923 m d n) (@lem2274928 m d n)). Qed.
Lemma lem2274930 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term143 m n) = (term191 d n).
Proof. exact (EQ_MP (@lem2274929 m d n) (@lem2274920 m n d h1)). Qed.
Lemma lem2274931 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term191 d n) = (term143 m n).
Proof. exact (SYM (@lem2274930 m n d h1)). Qed.
Lemma lem2274933 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2274934 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2274933 nat P Q). Qed.
Lemma lem2274935 (m : nat) (d : nat) : (term193 m d) = (term194 m d).
Proof. exact (@lem2274934 (term195 m d) (term196 m d)). Qed.
Lemma lem2274936 (m : nat) (d : nat) (n' : nat) : (term197 m d n') = ((term198 m d) = (real_of_num n')).
Proof. exact (eq_refl (term197 m d n')). Qed.
Lemma lem2274937 (m : nat) (d : nat) : (term199 m d) = (term195 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2274936 m d n')). Qed.
Lemma lem2274938 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274939 (m : nat) (d : nat) : (term200 m d) = (term201 m d).
Proof. exact (MK_COMB (@lem2274938) (@lem2274937 m d)). Qed.
Lemma lem2274940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274941 (m : nat) (d : nat) : (term202 m d) = (term203 m d).
Proof. exact (MK_COMB (@lem2274940) (@lem2274939 m d)). Qed.
Lemma lem2274942 (m : nat) (d : nat) (n' : nat) : (term204 m d n') = ((term198 m d) = (term93 n')).
Proof. exact (eq_refl (term204 m d n')). Qed.
Lemma lem2274943 (m : nat) (d : nat) : (term205 m d) = (term196 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2274942 m d n')). Qed.
Lemma lem2274944 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274945 (m : nat) (d : nat) : (term206 m d) = (term207 m d).
Proof. exact (MK_COMB (@lem2274944) (@lem2274943 m d)). Qed.
Lemma lem2274946 (m : nat) (d : nat) : (term193 m d) = (term163 m d).
Proof. exact (MK_COMB (@lem2274941 m d) (@lem2274945 m d)). Qed.
Lemma lem2274947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2274948 (m : nat) (d : nat) : (term208 m d) = (term209 m d).
Proof. exact (MK_COMB (@lem2274947) (@lem2274946 m d)). Qed.
Lemma lem2274949 (m : nat) (d : nat) (n' : nat) : (term197 m d n') = ((term198 m d) = (real_of_num n')).
Proof. exact (eq_refl (term197 m d n')). Qed.
Lemma lem2274950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274951 (m : nat) (d : nat) (n' : nat) : (term210 m d n') = (term211 m d n').
Proof. exact (MK_COMB (@lem2274950) (@lem2274949 m d n')). Qed.
Lemma lem2274952 (m : nat) (d : nat) (n' : nat) : (term204 m d n') = ((term198 m d) = (term93 n')).
Proof. exact (eq_refl (term204 m d n')). Qed.
Lemma lem2274953 (m : nat) (d : nat) (n' : nat) : (term212 m d n') = (term213 m d n').
Proof. exact (MK_COMB (@lem2274951 m d n') (@lem2274952 m d n')). Qed.
Lemma lem2274954 (m : nat) (d : nat) : (term214 m d) = (term215 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2274953 m d n')). Qed.
Lemma lem2274955 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2274956 (m : nat) (d : nat) : (term194 m d) = (term216 m d).
Proof. exact (MK_COMB (@lem2274955) (@lem2274954 m d)). Qed.
Lemma lem2274957 (m : nat) (d : nat) : ((term193 m d) = (term194 m d)) = ((term163 m d) = (term216 m d)).
Proof. exact (MK_COMB (@lem2274948 m d) (@lem2274956 m d)). Qed.
Lemma lem2274958 (m : nat) (d : nat) : (term163 m d) = (term216 m d).
Proof. exact (EQ_MP (@lem2274957 m d) (@lem2274935 m d)). Qed.
Lemma lem2274968 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2274969 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2274968 m d). Qed.
Lemma lem2274970 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2274971 (m : nat) (d : nat) : (term217 m d) = (term218 m d).
Proof. exact (MK_COMB (@lem2274970) (@lem2274969 m d)). Qed.
Lemma lem2274973 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2274974 (m : nat) (d : nat) : (term218 m d) = (term136 m d).
Proof. exact (@lem2274973 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2274975 (m : nat) (d : nat) : (term217 m d) = (term136 m d).
Proof. exact (TRANS (@lem2274971 m d) (@lem2274974 m d)). Qed.
Lemma lem2274976 (m : nat) : (term110 m) = (term110 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem2274977 (m : nat) (d : nat) : (term198 m d) = (term219 m d).
Proof. exact (MK_COMB (@lem2274976 m) (@lem2274975 m d)). Qed.
Lemma lem2274978 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2274979 (m : nat) (d : nat) : (term220 m d) = (term221 m d).
Proof. exact (MK_COMB (@lem2274978) (@lem2274977 m d)). Qed.
Lemma lem2274980 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2274981 (m : nat) (d : nat) (n' : nat) : ((term198 m d) = (real_of_num n')) = ((term219 m d) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2274979 m d) (@lem2274980 n')). Qed.
Lemma lem2274984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2274985 (m : nat) (d : nat) (n' : nat) : (term211 m d n') = (term222 m d n').
Proof. exact (MK_COMB (@lem2274984) (@lem2274981 m d n')). Qed.
Lemma lem2274989 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2274990 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2274989 m d). Qed.
Lemma lem2274991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2274992 (m : nat) (d : nat) : (term217 m d) = (term218 m d).
Proof. exact (MK_COMB (@lem2274991) (@lem2274990 m d)). Qed.
Lemma lem2274994 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2274995 (m : nat) (d : nat) : (term218 m d) = (term136 m d).
Proof. exact (@lem2274994 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2274996 (m : nat) (d : nat) : (term217 m d) = (term136 m d).
Proof. exact (TRANS (@lem2274992 m d) (@lem2274995 m d)). Qed.
Lemma lem2274997 (m : nat) : (term110 m) = (term110 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem2274998 (m : nat) (d : nat) : (term198 m d) = (term219 m d).
Proof. exact (MK_COMB (@lem2274997 m) (@lem2274996 m d)). Qed.
Lemma lem2274999 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275000 (m : nat) (d : nat) : (term220 m d) = (term221 m d).
Proof. exact (MK_COMB (@lem2274999) (@lem2274998 m d)). Qed.
Lemma lem2275001 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275002 (m : nat) (d : nat) (n' : nat) : ((term198 m d) = (term93 n')) = ((term219 m d) = (term93 n')).
Proof. exact (MK_COMB (@lem2275000 m d) (@lem2275001 n')). Qed.
Lemma lem2275005 (m : nat) (d : nat) (n' : nat) : (term213 m d n') = (term223 m d n').
Proof. exact (MK_COMB (@lem2274985 m d n') (@lem2275002 m d n')). Qed.
Lemma lem2275008 (m : nat) (d : nat) : (term215 m d) = (term224 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275005 m d n')). Qed.
Lemma lem2275009 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275010 (m : nat) (d : nat) : (term216 m d) = (term225 m d).
Proof. exact (MK_COMB (@lem2275009) (@lem2275008 m d)). Qed.
Lemma lem2275015 (m : nat) (d : nat) : (term163 m d) = (term225 m d).
Proof. exact (TRANS (@lem2274958 m d) (@lem2275010 m d)). Qed.
Lemma lem2275016 (m : nat) (d : nat) : (term225 m d) = (term163 m d).
Proof. exact (SYM (@lem2275015 m d)). Qed.
Lemma lem2275018 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2275019 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2275018 nat P Q). Qed.
Lemma lem2275020 (d : nat) (n : nat) : (term226 d n) = (term227 d n).
Proof. exact (@lem2275019 (term228 d n) (term229 d n)). Qed.
Lemma lem2275021 (d : nat) (n : nat) (n' : nat) : (term230 d n n') = ((term231 d n) = (real_of_num n')).
Proof. exact (eq_refl (term230 d n n')). Qed.
Lemma lem2275022 (d : nat) (n : nat) : (term232 d n) = (term228 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275021 d n n')). Qed.
Lemma lem2275023 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275024 (d : nat) (n : nat) : (term233 d n) = (term234 d n).
Proof. exact (MK_COMB (@lem2275023) (@lem2275022 d n)). Qed.
Lemma lem2275025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275026 (d : nat) (n : nat) : (term235 d n) = (term236 d n).
Proof. exact (MK_COMB (@lem2275025) (@lem2275024 d n)). Qed.
Lemma lem2275027 (d : nat) (n : nat) (n' : nat) : (term237 d n n') = ((term231 d n) = (term93 n')).
Proof. exact (eq_refl (term237 d n n')). Qed.
Lemma lem2275028 (d : nat) (n : nat) : (term238 d n) = (term229 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275027 d n n')). Qed.
Lemma lem2275029 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275030 (d : nat) (n : nat) : (term239 d n) = (term240 d n).
Proof. exact (MK_COMB (@lem2275029) (@lem2275028 d n)). Qed.
Lemma lem2275031 (d : nat) (n : nat) : (term226 d n) = (term169 d n).
Proof. exact (MK_COMB (@lem2275026 d n) (@lem2275030 d n)). Qed.
Lemma lem2275032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2275033 (d : nat) (n : nat) : (term241 d n) = (term242 d n).
Proof. exact (MK_COMB (@lem2275032) (@lem2275031 d n)). Qed.
Lemma lem2275034 (d : nat) (n : nat) (n' : nat) : (term230 d n n') = ((term231 d n) = (real_of_num n')).
Proof. exact (eq_refl (term230 d n n')). Qed.
Lemma lem2275035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275036 (d : nat) (n : nat) (n' : nat) : (term243 d n n') = (term244 d n n').
Proof. exact (MK_COMB (@lem2275035) (@lem2275034 d n n')). Qed.
Lemma lem2275037 (d : nat) (n : nat) (n' : nat) : (term237 d n n') = ((term231 d n) = (term93 n')).
Proof. exact (eq_refl (term237 d n n')). Qed.
Lemma lem2275038 (d : nat) (n : nat) (n' : nat) : (term245 d n n') = (term246 d n n').
Proof. exact (MK_COMB (@lem2275036 d n n') (@lem2275037 d n n')). Qed.
Lemma lem2275039 (d : nat) (n : nat) : (term247 d n) = (term248 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275038 d n n')). Qed.
Lemma lem2275040 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275041 (d : nat) (n : nat) : (term227 d n) = (term249 d n).
Proof. exact (MK_COMB (@lem2275040) (@lem2275039 d n)). Qed.
Lemma lem2275042 (d : nat) (n : nat) : ((term226 d n) = (term227 d n)) = ((term169 d n) = (term249 d n)).
Proof. exact (MK_COMB (@lem2275033 d n) (@lem2275041 d n)). Qed.
Lemma lem2275043 (d : nat) (n : nat) : (term169 d n) = (term249 d n).
Proof. exact (EQ_MP (@lem2275042 d n) (@lem2275020 d n)). Qed.
Lemma lem2275053 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275054 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275053 n d). Qed.
Lemma lem2275055 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275056 (n : nat) (d : nat) : (term250 n d) = (term251 n d).
Proof. exact (MK_COMB (@lem2275055) (@lem2275054 n d)). Qed.
Lemma lem2275057 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2275058 (d : nat) (n : nat) : (term231 d n) = (term252 d n).
Proof. exact (MK_COMB (@lem2275056 n d) (@lem2275057 n)). Qed.
Lemma lem2275059 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275060 (d : nat) (n : nat) : (term253 d n) = (term254 d n).
Proof. exact (MK_COMB (@lem2275059) (@lem2275058 d n)). Qed.
Lemma lem2275061 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2275062 (d : nat) (n : nat) (n' : nat) : ((term231 d n) = (real_of_num n')) = ((term252 d n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2275060 d n) (@lem2275061 n')). Qed.
Lemma lem2275065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275066 (d : nat) (n : nat) (n' : nat) : (term244 d n n') = (term255 d n n').
Proof. exact (MK_COMB (@lem2275065) (@lem2275062 d n n')). Qed.
Lemma lem2275070 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275071 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275070 n d). Qed.
Lemma lem2275072 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275073 (n : nat) (d : nat) : (term250 n d) = (term251 n d).
Proof. exact (MK_COMB (@lem2275072) (@lem2275071 n d)). Qed.
Lemma lem2275074 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2275075 (d : nat) (n : nat) : (term231 d n) = (term252 d n).
Proof. exact (MK_COMB (@lem2275073 n d) (@lem2275074 n)). Qed.
Lemma lem2275076 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275077 (d : nat) (n : nat) : (term253 d n) = (term254 d n).
Proof. exact (MK_COMB (@lem2275076) (@lem2275075 d n)). Qed.
Lemma lem2275078 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275079 (d : nat) (n : nat) (n' : nat) : ((term231 d n) = (term93 n')) = ((term252 d n) = (term93 n')).
Proof. exact (MK_COMB (@lem2275077 d n) (@lem2275078 n')). Qed.
Lemma lem2275082 (d : nat) (n : nat) (n' : nat) : (term246 d n n') = (term256 d n n').
Proof. exact (MK_COMB (@lem2275066 d n n') (@lem2275079 d n n')). Qed.
Lemma lem2275085 (d : nat) (n : nat) : (term248 d n) = (term257 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275082 d n n')). Qed.
Lemma lem2275086 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275087 (d : nat) (n : nat) : (term249 d n) = (term258 d n).
Proof. exact (MK_COMB (@lem2275086) (@lem2275085 d n)). Qed.
Lemma lem2275092 (d : nat) (n : nat) : (term169 d n) = (term258 d n).
Proof. exact (TRANS (@lem2275043 d n) (@lem2275087 d n)). Qed.
Lemma lem2275093 (d : nat) (n : nat) : (term258 d n) = (term169 d n).
Proof. exact (SYM (@lem2275092 d n)). Qed.
Lemma lem2275095 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2275096 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2275095 nat P Q). Qed.
Lemma lem2275097 (m : nat) (d : nat) : (term259 m d) = (term260 m d).
Proof. exact (@lem2275096 (term261 m d) (term262 m d)). Qed.
Lemma lem2275098 (m : nat) (d : nat) (n' : nat) : (term263 m d n') = ((term264 m d) = (real_of_num n')).
Proof. exact (eq_refl (term263 m d n')). Qed.
Lemma lem2275099 (m : nat) (d : nat) : (term265 m d) = (term261 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275098 m d n')). Qed.
Lemma lem2275100 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275101 (m : nat) (d : nat) : (term266 m d) = (term267 m d).
Proof. exact (MK_COMB (@lem2275100) (@lem2275099 m d)). Qed.
Lemma lem2275102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275103 (m : nat) (d : nat) : (term268 m d) = (term269 m d).
Proof. exact (MK_COMB (@lem2275102) (@lem2275101 m d)). Qed.
Lemma lem2275104 (m : nat) (d : nat) (n' : nat) : (term270 m d n') = ((term264 m d) = (term93 n')).
Proof. exact (eq_refl (term270 m d n')). Qed.
Lemma lem2275105 (m : nat) (d : nat) : (term271 m d) = (term262 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275104 m d n')). Qed.
Lemma lem2275106 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275107 (m : nat) (d : nat) : (term272 m d) = (term273 m d).
Proof. exact (MK_COMB (@lem2275106) (@lem2275105 m d)). Qed.
Lemma lem2275108 (m : nat) (d : nat) : (term259 m d) = (term174 m d).
Proof. exact (MK_COMB (@lem2275103 m d) (@lem2275107 m d)). Qed.
Lemma lem2275109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2275110 (m : nat) (d : nat) : (term274 m d) = (term275 m d).
Proof. exact (MK_COMB (@lem2275109) (@lem2275108 m d)). Qed.
Lemma lem2275111 (m : nat) (d : nat) (n' : nat) : (term263 m d n') = ((term264 m d) = (real_of_num n')).
Proof. exact (eq_refl (term263 m d n')). Qed.
Lemma lem2275112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275113 (m : nat) (d : nat) (n' : nat) : (term276 m d n') = (term277 m d n').
Proof. exact (MK_COMB (@lem2275112) (@lem2275111 m d n')). Qed.
Lemma lem2275114 (m : nat) (d : nat) (n' : nat) : (term270 m d n') = ((term264 m d) = (term93 n')).
Proof. exact (eq_refl (term270 m d n')). Qed.
Lemma lem2275115 (m : nat) (d : nat) (n' : nat) : (term278 m d n') = (term279 m d n').
Proof. exact (MK_COMB (@lem2275113 m d n') (@lem2275114 m d n')). Qed.
Lemma lem2275116 (m : nat) (d : nat) : (term280 m d) = (term281 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275115 m d n')). Qed.
Lemma lem2275117 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275118 (m : nat) (d : nat) : (term260 m d) = (term282 m d).
Proof. exact (MK_COMB (@lem2275117) (@lem2275116 m d)). Qed.
Lemma lem2275119 (m : nat) (d : nat) : ((term259 m d) = (term260 m d)) = ((term174 m d) = (term282 m d)).
Proof. exact (MK_COMB (@lem2275110 m d) (@lem2275118 m d)). Qed.
Lemma lem2275120 (m : nat) (d : nat) : (term174 m d) = (term282 m d).
Proof. exact (EQ_MP (@lem2275119 m d) (@lem2275097 m d)). Qed.
Lemma lem2275130 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275131 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2275130 m d). Qed.
Lemma lem2275132 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2275133 (m : nat) (d : nat) : (term264 m d) = (term283 m d).
Proof. exact (MK_COMB (@lem2275132 m) (@lem2275131 m d)). Qed.
Lemma lem2275134 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275135 (m : nat) (d : nat) : (term284 m d) = (term285 m d).
Proof. exact (MK_COMB (@lem2275134) (@lem2275133 m d)). Qed.
Lemma lem2275136 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2275137 (m : nat) (d : nat) (n' : nat) : ((term264 m d) = (real_of_num n')) = ((term283 m d) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2275135 m d) (@lem2275136 n')). Qed.
Lemma lem2275140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275141 (m : nat) (d : nat) (n' : nat) : (term277 m d n') = (term286 m d n').
Proof. exact (MK_COMB (@lem2275140) (@lem2275137 m d n')). Qed.
Lemma lem2275145 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275146 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2275145 m d). Qed.
Lemma lem2275147 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2275148 (m : nat) (d : nat) : (term264 m d) = (term283 m d).
Proof. exact (MK_COMB (@lem2275147 m) (@lem2275146 m d)). Qed.
Lemma lem2275149 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275150 (m : nat) (d : nat) : (term284 m d) = (term285 m d).
Proof. exact (MK_COMB (@lem2275149) (@lem2275148 m d)). Qed.
Lemma lem2275151 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275152 (m : nat) (d : nat) (n' : nat) : ((term264 m d) = (term93 n')) = ((term283 m d) = (term93 n')).
Proof. exact (MK_COMB (@lem2275150 m d) (@lem2275151 n')). Qed.
Lemma lem2275155 (m : nat) (d : nat) (n' : nat) : (term279 m d n') = (term287 m d n').
Proof. exact (MK_COMB (@lem2275141 m d n') (@lem2275152 m d n')). Qed.
Lemma lem2275158 (m : nat) (d : nat) : (term281 m d) = (term288 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275155 m d n')). Qed.
Lemma lem2275159 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275160 (m : nat) (d : nat) : (term282 m d) = (term289 m d).
Proof. exact (MK_COMB (@lem2275159) (@lem2275158 m d)). Qed.
Lemma lem2275165 (m : nat) (d : nat) : (term174 m d) = (term289 m d).
Proof. exact (TRANS (@lem2275120 m d) (@lem2275160 m d)). Qed.
Lemma lem2275166 (m : nat) (d : nat) : (term289 m d) = (term174 m d).
Proof. exact (SYM (@lem2275165 m d)). Qed.
Lemma lem2275168 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2275169 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2275168 nat P Q). Qed.
Lemma lem2275170 (d : nat) (n : nat) : (term290 d n) = (term291 d n).
Proof. exact (@lem2275169 (term292 d n) (term293 d n)). Qed.
Lemma lem2275171 (d : nat) (n : nat) (n' : nat) : (term294 d n n') = ((term295 d n) = (real_of_num n')).
Proof. exact (eq_refl (term294 d n n')). Qed.
Lemma lem2275172 (d : nat) (n : nat) : (term296 d n) = (term292 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275171 d n n')). Qed.
Lemma lem2275173 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275174 (d : nat) (n : nat) : (term297 d n) = (term298 d n).
Proof. exact (MK_COMB (@lem2275173) (@lem2275172 d n)). Qed.
Lemma lem2275175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275176 (d : nat) (n : nat) : (term299 d n) = (term300 d n).
Proof. exact (MK_COMB (@lem2275175) (@lem2275174 d n)). Qed.
Lemma lem2275177 (d : nat) (n : nat) (n' : nat) : (term301 d n n') = ((term295 d n) = (term93 n')).
Proof. exact (eq_refl (term301 d n n')). Qed.
Lemma lem2275178 (d : nat) (n : nat) : (term302 d n) = (term293 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275177 d n n')). Qed.
Lemma lem2275179 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275180 (d : nat) (n : nat) : (term303 d n) = (term304 d n).
Proof. exact (MK_COMB (@lem2275179) (@lem2275178 d n)). Qed.
Lemma lem2275181 (d : nat) (n : nat) : (term290 d n) = (term180 d n).
Proof. exact (MK_COMB (@lem2275176 d n) (@lem2275180 d n)). Qed.
Lemma lem2275182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2275183 (d : nat) (n : nat) : (term305 d n) = (term306 d n).
Proof. exact (MK_COMB (@lem2275182) (@lem2275181 d n)). Qed.
Lemma lem2275184 (d : nat) (n : nat) (n' : nat) : (term294 d n n') = ((term295 d n) = (real_of_num n')).
Proof. exact (eq_refl (term294 d n n')). Qed.
Lemma lem2275185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275186 (d : nat) (n : nat) (n' : nat) : (term307 d n n') = (term308 d n n').
Proof. exact (MK_COMB (@lem2275185) (@lem2275184 d n n')). Qed.
Lemma lem2275187 (d : nat) (n : nat) (n' : nat) : (term301 d n n') = ((term295 d n) = (term93 n')).
Proof. exact (eq_refl (term301 d n n')). Qed.
Lemma lem2275188 (d : nat) (n : nat) (n' : nat) : (term309 d n n') = (term310 d n n').
Proof. exact (MK_COMB (@lem2275186 d n n') (@lem2275187 d n n')). Qed.
Lemma lem2275189 (d : nat) (n : nat) : (term311 d n) = (term312 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275188 d n n')). Qed.
Lemma lem2275190 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275191 (d : nat) (n : nat) : (term291 d n) = (term313 d n).
Proof. exact (MK_COMB (@lem2275190) (@lem2275189 d n)). Qed.
Lemma lem2275192 (d : nat) (n : nat) : ((term290 d n) = (term291 d n)) = ((term180 d n) = (term313 d n)).
Proof. exact (MK_COMB (@lem2275183 d n) (@lem2275191 d n)). Qed.
Lemma lem2275193 (d : nat) (n : nat) : (term180 d n) = (term313 d n).
Proof. exact (EQ_MP (@lem2275192 d n) (@lem2275170 d n)). Qed.
Lemma lem2275203 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275204 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275203 n d). Qed.
Lemma lem2275205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275206 (n : nat) (d : nat) : (term217 n d) = (term218 n d).
Proof. exact (MK_COMB (@lem2275205) (@lem2275204 n d)). Qed.
Lemma lem2275208 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275209 (n : nat) (d : nat) : (term218 n d) = (term136 n d).
Proof. exact (@lem2275208 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2275210 (n : nat) (d : nat) : (term217 n d) = (term136 n d).
Proof. exact (TRANS (@lem2275206 n d) (@lem2275209 n d)). Qed.
Lemma lem2275211 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275212 (n : nat) (d : nat) : (term314 n d) = (term315 n d).
Proof. exact (MK_COMB (@lem2275211) (@lem2275210 n d)). Qed.
Lemma lem2275213 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2275214 (d : nat) (n : nat) : (term295 d n) = (term316 d n).
Proof. exact (MK_COMB (@lem2275212 n d) (@lem2275213 n)). Qed.
Lemma lem2275215 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275216 (d : nat) (n : nat) : (term317 d n) = (term318 d n).
Proof. exact (MK_COMB (@lem2275215) (@lem2275214 d n)). Qed.
Lemma lem2275217 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2275218 (d : nat) (n : nat) (n' : nat) : ((term295 d n) = (real_of_num n')) = ((term316 d n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2275216 d n) (@lem2275217 n')). Qed.
Lemma lem2275221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275222 (d : nat) (n : nat) (n' : nat) : (term308 d n n') = (term319 d n n').
Proof. exact (MK_COMB (@lem2275221) (@lem2275218 d n n')). Qed.
Lemma lem2275226 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275227 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275226 n d). Qed.
Lemma lem2275228 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275229 (n : nat) (d : nat) : (term217 n d) = (term218 n d).
Proof. exact (MK_COMB (@lem2275228) (@lem2275227 n d)). Qed.
Lemma lem2275231 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275232 (n : nat) (d : nat) : (term218 n d) = (term136 n d).
Proof. exact (@lem2275231 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2275233 (n : nat) (d : nat) : (term217 n d) = (term136 n d).
Proof. exact (TRANS (@lem2275229 n d) (@lem2275232 n d)). Qed.
Lemma lem2275234 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275235 (n : nat) (d : nat) : (term314 n d) = (term315 n d).
Proof. exact (MK_COMB (@lem2275234) (@lem2275233 n d)). Qed.
Lemma lem2275236 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2275237 (d : nat) (n : nat) : (term295 d n) = (term316 d n).
Proof. exact (MK_COMB (@lem2275235 n d) (@lem2275236 n)). Qed.
Lemma lem2275238 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275239 (d : nat) (n : nat) : (term317 d n) = (term318 d n).
Proof. exact (MK_COMB (@lem2275238) (@lem2275237 d n)). Qed.
Lemma lem2275240 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275241 (d : nat) (n : nat) (n' : nat) : ((term295 d n) = (term93 n')) = ((term316 d n) = (term93 n')).
Proof. exact (MK_COMB (@lem2275239 d n) (@lem2275240 n')). Qed.
Lemma lem2275244 (d : nat) (n : nat) (n' : nat) : (term310 d n n') = (term320 d n n').
Proof. exact (MK_COMB (@lem2275222 d n n') (@lem2275241 d n n')). Qed.
Lemma lem2275247 (d : nat) (n : nat) : (term312 d n) = (term321 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275244 d n n')). Qed.
Lemma lem2275248 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275249 (d : nat) (n : nat) : (term313 d n) = (term322 d n).
Proof. exact (MK_COMB (@lem2275248) (@lem2275247 d n)). Qed.
Lemma lem2275254 (d : nat) (n : nat) : (term180 d n) = (term322 d n).
Proof. exact (TRANS (@lem2275193 d n) (@lem2275249 d n)). Qed.
Lemma lem2275255 (d : nat) (n : nat) : (term322 d n) = (term180 d n).
Proof. exact (SYM (@lem2275254 d n)). Qed.
Lemma lem2275257 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2275258 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2275257 nat P Q). Qed.
Lemma lem2275259 (m : nat) (d : nat) : (term323 m d) = (term324 m d).
Proof. exact (@lem2275258 (term325 m d) (term326 m d)). Qed.
Lemma lem2275260 (m : nat) (d : nat) (n' : nat) : (term327 m d n') = ((term328 m d) = (real_of_num n')).
Proof. exact (eq_refl (term327 m d n')). Qed.
Lemma lem2275261 (m : nat) (d : nat) : (term329 m d) = (term325 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275260 m d n')). Qed.
Lemma lem2275262 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275263 (m : nat) (d : nat) : (term330 m d) = (term331 m d).
Proof. exact (MK_COMB (@lem2275262) (@lem2275261 m d)). Qed.
Lemma lem2275264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275265 (m : nat) (d : nat) : (term332 m d) = (term333 m d).
Proof. exact (MK_COMB (@lem2275264) (@lem2275263 m d)). Qed.
Lemma lem2275266 (m : nat) (d : nat) (n' : nat) : (term334 m d n') = ((term328 m d) = (term93 n')).
Proof. exact (eq_refl (term334 m d n')). Qed.
Lemma lem2275267 (m : nat) (d : nat) : (term335 m d) = (term326 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275266 m d n')). Qed.
Lemma lem2275268 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275269 (m : nat) (d : nat) : (term336 m d) = (term337 m d).
Proof. exact (MK_COMB (@lem2275268) (@lem2275267 m d)). Qed.
Lemma lem2275270 (m : nat) (d : nat) : (term323 m d) = (term185 m d).
Proof. exact (MK_COMB (@lem2275265 m d) (@lem2275269 m d)). Qed.
Lemma lem2275271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2275272 (m : nat) (d : nat) : (term338 m d) = (term339 m d).
Proof. exact (MK_COMB (@lem2275271) (@lem2275270 m d)). Qed.
Lemma lem2275273 (m : nat) (d : nat) (n' : nat) : (term327 m d n') = ((term328 m d) = (real_of_num n')).
Proof. exact (eq_refl (term327 m d n')). Qed.
Lemma lem2275274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275275 (m : nat) (d : nat) (n' : nat) : (term340 m d n') = (term341 m d n').
Proof. exact (MK_COMB (@lem2275274) (@lem2275273 m d n')). Qed.
Lemma lem2275276 (m : nat) (d : nat) (n' : nat) : (term334 m d n') = ((term328 m d) = (term93 n')).
Proof. exact (eq_refl (term334 m d n')). Qed.
Lemma lem2275277 (m : nat) (d : nat) (n' : nat) : (term342 m d n') = (term343 m d n').
Proof. exact (MK_COMB (@lem2275275 m d n') (@lem2275276 m d n')). Qed.
Lemma lem2275278 (m : nat) (d : nat) : (term344 m d) = (term345 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275277 m d n')). Qed.
Lemma lem2275279 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275280 (m : nat) (d : nat) : (term324 m d) = (term346 m d).
Proof. exact (MK_COMB (@lem2275279) (@lem2275278 m d)). Qed.
Lemma lem2275281 (m : nat) (d : nat) : ((term323 m d) = (term324 m d)) = ((term185 m d) = (term346 m d)).
Proof. exact (MK_COMB (@lem2275272 m d) (@lem2275280 m d)). Qed.
Lemma lem2275282 (m : nat) (d : nat) : (term185 m d) = (term346 m d).
Proof. exact (EQ_MP (@lem2275281 m d) (@lem2275259 m d)). Qed.
Lemma lem2275292 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275293 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2275292 m d). Qed.
Lemma lem2275294 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275295 (m : nat) (d : nat) : (term217 m d) = (term218 m d).
Proof. exact (MK_COMB (@lem2275294) (@lem2275293 m d)). Qed.
Lemma lem2275297 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275298 (m : nat) (d : nat) : (term218 m d) = (term136 m d).
Proof. exact (@lem2275297 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2275299 (m : nat) (d : nat) : (term217 m d) = (term136 m d).
Proof. exact (TRANS (@lem2275295 m d) (@lem2275298 m d)). Qed.
Lemma lem2275300 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2275301 (m : nat) (d : nat) : (term328 m d) = (term347 m d).
Proof. exact (MK_COMB (@lem2275300 m) (@lem2275299 m d)). Qed.
Lemma lem2275302 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275303 (m : nat) (d : nat) : (term348 m d) = (term349 m d).
Proof. exact (MK_COMB (@lem2275302) (@lem2275301 m d)). Qed.
Lemma lem2275304 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2275305 (m : nat) (d : nat) (n' : nat) : ((term328 m d) = (real_of_num n')) = ((term347 m d) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2275303 m d) (@lem2275304 n')). Qed.
Lemma lem2275308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275309 (m : nat) (d : nat) (n' : nat) : (term341 m d n') = (term350 m d n').
Proof. exact (MK_COMB (@lem2275308) (@lem2275305 m d n')). Qed.
Lemma lem2275313 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275314 (m : nat) (d : nat) : (term26 m d) = (term25 m d).
Proof. exact (@lem2275313 m d). Qed.
Lemma lem2275315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275316 (m : nat) (d : nat) : (term217 m d) = (term218 m d).
Proof. exact (MK_COMB (@lem2275315) (@lem2275314 m d)). Qed.
Lemma lem2275318 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275319 (m : nat) (d : nat) : (term218 m d) = (term136 m d).
Proof. exact (@lem2275318 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2275320 (m : nat) (d : nat) : (term217 m d) = (term136 m d).
Proof. exact (TRANS (@lem2275316 m d) (@lem2275319 m d)). Qed.
Lemma lem2275321 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2275322 (m : nat) (d : nat) : (term328 m d) = (term347 m d).
Proof. exact (MK_COMB (@lem2275321 m) (@lem2275320 m d)). Qed.
Lemma lem2275323 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275324 (m : nat) (d : nat) : (term348 m d) = (term349 m d).
Proof. exact (MK_COMB (@lem2275323) (@lem2275322 m d)). Qed.
Lemma lem2275325 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275326 (m : nat) (d : nat) (n' : nat) : ((term328 m d) = (term93 n')) = ((term347 m d) = (term93 n')).
Proof. exact (MK_COMB (@lem2275324 m d) (@lem2275325 n')). Qed.
Lemma lem2275329 (m : nat) (d : nat) (n' : nat) : (term343 m d n') = (term351 m d n').
Proof. exact (MK_COMB (@lem2275309 m d n') (@lem2275326 m d n')). Qed.
Lemma lem2275332 (m : nat) (d : nat) : (term345 m d) = (term352 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2275329 m d n')). Qed.
Lemma lem2275333 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275334 (m : nat) (d : nat) : (term346 m d) = (term353 m d).
Proof. exact (MK_COMB (@lem2275333) (@lem2275332 m d)). Qed.
Lemma lem2275339 (m : nat) (d : nat) : (term185 m d) = (term353 m d).
Proof. exact (TRANS (@lem2275282 m d) (@lem2275334 m d)). Qed.
Lemma lem2275340 (m : nat) (d : nat) : (term353 m d) = (term185 m d).
Proof. exact (SYM (@lem2275339 m d)). Qed.
Lemma lem2275342 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem2273871 A P Q) (@lem2273870 A P Q)). Qed.
Lemma lem2275343 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem2275342 nat P Q). Qed.
Lemma lem2275344 (d : nat) (n : nat) : (term354 d n) = (term355 d n).
Proof. exact (@lem2275343 (term356 d n) (term357 d n)). Qed.
Lemma lem2275345 (d : nat) (n : nat) (n' : nat) : (term358 d n n') = ((term359 d n) = (real_of_num n')).
Proof. exact (eq_refl (term358 d n n')). Qed.
Lemma lem2275346 (d : nat) (n : nat) : (term360 d n) = (term356 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275345 d n n')). Qed.
Lemma lem2275347 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275348 (d : nat) (n : nat) : (term361 d n) = (term362 d n).
Proof. exact (MK_COMB (@lem2275347) (@lem2275346 d n)). Qed.
Lemma lem2275349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275350 (d : nat) (n : nat) : (term363 d n) = (term364 d n).
Proof. exact (MK_COMB (@lem2275349) (@lem2275348 d n)). Qed.
Lemma lem2275351 (d : nat) (n : nat) (n' : nat) : (term365 d n n') = ((term359 d n) = (term93 n')).
Proof. exact (eq_refl (term365 d n n')). Qed.
Lemma lem2275352 (d : nat) (n : nat) : (term366 d n) = (term357 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275351 d n n')). Qed.
Lemma lem2275353 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275354 (d : nat) (n : nat) : (term367 d n) = (term368 d n).
Proof. exact (MK_COMB (@lem2275353) (@lem2275352 d n)). Qed.
Lemma lem2275355 (d : nat) (n : nat) : (term354 d n) = (term191 d n).
Proof. exact (MK_COMB (@lem2275350 d n) (@lem2275354 d n)). Qed.
Lemma lem2275356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2275357 (d : nat) (n : nat) : (term369 d n) = (term370 d n).
Proof. exact (MK_COMB (@lem2275356) (@lem2275355 d n)). Qed.
Lemma lem2275358 (d : nat) (n : nat) (n' : nat) : (term358 d n n') = ((term359 d n) = (real_of_num n')).
Proof. exact (eq_refl (term358 d n n')). Qed.
Lemma lem2275359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275360 (d : nat) (n : nat) (n' : nat) : (term371 d n n') = (term372 d n n').
Proof. exact (MK_COMB (@lem2275359) (@lem2275358 d n n')). Qed.
Lemma lem2275361 (d : nat) (n : nat) (n' : nat) : (term365 d n n') = ((term359 d n) = (term93 n')).
Proof. exact (eq_refl (term365 d n n')). Qed.
Lemma lem2275362 (d : nat) (n : nat) (n' : nat) : (term373 d n n') = (term374 d n n').
Proof. exact (MK_COMB (@lem2275360 d n n') (@lem2275361 d n n')). Qed.
Lemma lem2275363 (d : nat) (n : nat) : (term375 d n) = (term376 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275362 d n n')). Qed.
Lemma lem2275364 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275365 (d : nat) (n : nat) : (term355 d n) = (term377 d n).
Proof. exact (MK_COMB (@lem2275364) (@lem2275363 d n)). Qed.
Lemma lem2275366 (d : nat) (n : nat) : ((term354 d n) = (term355 d n)) = ((term191 d n) = (term377 d n)).
Proof. exact (MK_COMB (@lem2275357 d n) (@lem2275365 d n)). Qed.
Lemma lem2275367 (d : nat) (n : nat) : (term191 d n) = (term377 d n).
Proof. exact (EQ_MP (@lem2275366 d n) (@lem2275344 d n)). Qed.
Lemma lem2275377 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275378 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275377 n d). Qed.
Lemma lem2275379 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275380 (n : nat) (d : nat) : (term217 n d) = (term218 n d).
Proof. exact (MK_COMB (@lem2275379) (@lem2275378 n d)). Qed.
Lemma lem2275382 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275383 (n : nat) (d : nat) : (term218 n d) = (term136 n d).
Proof. exact (@lem2275382 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2275384 (n : nat) (d : nat) : (term217 n d) = (term136 n d).
Proof. exact (TRANS (@lem2275380 n d) (@lem2275383 n d)). Qed.
Lemma lem2275385 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275386 (n : nat) (d : nat) : (term314 n d) = (term315 n d).
Proof. exact (MK_COMB (@lem2275385) (@lem2275384 n d)). Qed.
Lemma lem2275387 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2275388 (d : nat) (n : nat) : (term359 d n) = (term378 d n).
Proof. exact (MK_COMB (@lem2275386 n d) (@lem2275387 n)). Qed.
Lemma lem2275389 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275390 (d : nat) (n : nat) : (term379 d n) = (term380 d n).
Proof. exact (MK_COMB (@lem2275389) (@lem2275388 d n)). Qed.
Lemma lem2275391 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2275392 (d : nat) (n : nat) (n' : nat) : ((term359 d n) = (real_of_num n')) = ((term378 d n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2275390 d n) (@lem2275391 n')). Qed.
Lemma lem2275395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275396 (d : nat) (n : nat) (n' : nat) : (term372 d n n') = (term381 d n n').
Proof. exact (MK_COMB (@lem2275395) (@lem2275392 d n n')). Qed.
Lemma lem2275400 (m : nat) (n : nat) : (term26 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2273877 m n) (@lem2273876 m n)). Qed.
Lemma lem2275401 (n : nat) (d : nat) : (term26 n d) = (term25 n d).
Proof. exact (@lem2275400 n d). Qed.
Lemma lem2275402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275403 (n : nat) (d : nat) : (term217 n d) = (term218 n d).
Proof. exact (MK_COMB (@lem2275402) (@lem2275401 n d)). Qed.
Lemma lem2275405 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2273865 x y) (@lem2273864 x y)). Qed.
Lemma lem2275406 (n : nat) (d : nat) : (term218 n d) = (term136 n d).
Proof. exact (@lem2275405 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2275407 (n : nat) (d : nat) : (term217 n d) = (term136 n d).
Proof. exact (TRANS (@lem2275403 n d) (@lem2275406 n d)). Qed.
Lemma lem2275408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275409 (n : nat) (d : nat) : (term314 n d) = (term315 n d).
Proof. exact (MK_COMB (@lem2275408) (@lem2275407 n d)). Qed.
Lemma lem2275410 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2275411 (d : nat) (n : nat) : (term359 d n) = (term378 d n).
Proof. exact (MK_COMB (@lem2275409 n d) (@lem2275410 n)). Qed.
Lemma lem2275412 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2275413 (d : nat) (n : nat) : (term379 d n) = (term380 d n).
Proof. exact (MK_COMB (@lem2275412) (@lem2275411 d n)). Qed.
Lemma lem2275414 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2275415 (d : nat) (n : nat) (n' : nat) : ((term359 d n) = (term93 n')) = ((term378 d n) = (term93 n')).
Proof. exact (MK_COMB (@lem2275413 d n) (@lem2275414 n')). Qed.
Lemma lem2275418 (d : nat) (n : nat) (n' : nat) : (term374 d n n') = (term382 d n n').
Proof. exact (MK_COMB (@lem2275396 d n n') (@lem2275415 d n n')). Qed.
Lemma lem2275421 (d : nat) (n : nat) : (term376 d n) = (term383 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2275418 d n n')). Qed.
Lemma lem2275422 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2275423 (d : nat) (n : nat) : (term377 d n) = (term384 d n).
Proof. exact (MK_COMB (@lem2275422) (@lem2275421 d n)). Qed.
Lemma lem2275428 (d : nat) (n : nat) : (term191 d n) = (term384 d n).
Proof. exact (TRANS (@lem2275367 d n) (@lem2275423 d n)). Qed.
Lemma lem2275429 (d : nat) (n : nat) : (term384 d n) = (term191 d n).
Proof. exact (SYM (@lem2275428 d n)). Qed.
Lemma lem2275453 (m : nat) (d : nat) : (term385 m d) = (term386 m d).
Proof. exact (@lem17160 ((term219 m d) = (real_of_num d)) ((term219 m d) = (term93 d))). Qed.
Lemma lem2275454 (m : nat) (d : nat) : (term387 m d) = (term388 m d).
Proof. exact (@lem1988318 (term219 m d) (real_of_num d)). Qed.
Lemma lem2275455 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2275462 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2275469 (m : nat) : (term93 m) = (term389 m).
Proof. exact (@lem1982785 (real_of_num m)). Qed.
Lemma lem2275470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275471 (m : nat) : (term127 m) = (term390 m).
Proof. exact (MK_COMB (@lem2275470) (@lem2275469 m)). Qed.
Lemma lem2275472 (m : nat) (d : nat) : (term136 m d) = (term391 m d).
Proof. exact (MK_COMB (@lem2275471 m) (@lem2275462 d)). Qed.
Lemma lem2275473 (d : nat) (m : nat) : (term391 m d) = (term391 d m).
Proof. exact (@lem1982761 (term389 d) (term389 m)). Qed.
Lemma lem2275474 (d : nat) (m : nat) : (term136 m d) = (term391 d m).
Proof. exact (TRANS (@lem2275472 m d) (@lem2275473 d m)). Qed.
Lemma lem2275477 (m : nat) : (term110 m) = (term110 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem2275478 (d : nat) (m : nat) : (term219 m d) = (term392 d m).
Proof. exact (MK_COMB (@lem2275477 m) (@lem2275474 d m)). Qed.
Lemma lem2275479 (d : nat) (m : nat) : (term392 d m) = (term393 d m).
Proof. exact (@lem1982757 (term389 d) (real_of_num m) (term389 m)). Qed.
Lemma lem2275480 (m : nat) : (term394 m) = (term395 m).
Proof. exact (@lem1982715 term396 (real_of_num m)). Qed.
Lemma lem2275482 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2275483 : term398 = term399.
Proof. exact (@lem2275482 term400). Qed.
Lemma lem2275485 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275486 : term396 = term402.
Proof. exact (@lem2275485 term400). Qed.
Lemma lem2275487 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275488 : term403 = term404.
Proof. exact (MK_COMB (@lem2275487) (@lem2275486)). Qed.
Lemma lem2275489 : term405 = term406.
Proof. exact (MK_COMB (@lem2275488) (@lem2275483)). Qed.
Lemma lem2275490 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2275492 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275493 : term410 = term411.
Proof. exact (@lem2275492 (NUMERAL 0) term400). Qed.
Lemma lem2275494 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275495 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275496 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275495 h1) (fun h1 : term411 = True => @lem2275494)). Qed.
Lemma lem2275497 : term411 = True.
Proof. exact (EQ_MP (@lem2275496) (@lem2275494)). Qed.
Lemma lem2275498 : term410 = True.
Proof. exact (TRANS (@lem2275493) (@lem2275497)). Qed.
Lemma lem2275499 : True = term410.
Proof. exact (SYM (@lem2275498)). Qed.
Lemma lem2275500 : term410.
Proof. exact (EQ_MP (@lem2275499) (@lem0)). Qed.
Lemma lem2275501 : term413.
Proof. exact (@lem2275490 (@lem2275500)). Qed.
Lemma lem2275503 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275504 : term410 = term411.
Proof. exact (@lem2275503 (NUMERAL 0) term400). Qed.
Lemma lem2275505 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275506 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275507 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275506 h1) (fun h1 : term411 = True => @lem2275505)). Qed.
Lemma lem2275508 : term411 = True.
Proof. exact (EQ_MP (@lem2275507) (@lem2275505)). Qed.
Lemma lem2275509 : term410 = True.
Proof. exact (TRANS (@lem2275504) (@lem2275508)). Qed.
Lemma lem2275510 : True = term410.
Proof. exact (SYM (@lem2275509)). Qed.
Lemma lem2275511 : term410.
Proof. exact (EQ_MP (@lem2275510) (@lem0)). Qed.
Lemma lem2275512 : term414.
Proof. exact (@lem2275501 (@lem2275511)). Qed.
Lemma lem2275514 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275515 : term410 = term411.
Proof. exact (@lem2275514 (NUMERAL 0) term400). Qed.
Lemma lem2275516 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275517 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275518 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275517 h1) (fun h1 : term411 = True => @lem2275516)). Qed.
Lemma lem2275519 : term411 = True.
Proof. exact (EQ_MP (@lem2275518) (@lem2275516)). Qed.
Lemma lem2275520 : term410 = True.
Proof. exact (TRANS (@lem2275515) (@lem2275519)). Qed.
Lemma lem2275521 : True = term410.
Proof. exact (SYM (@lem2275520)). Qed.
Lemma lem2275522 : term410.
Proof. exact (EQ_MP (@lem2275521) (@lem0)). Qed.
Lemma lem2275523 : term415.
Proof. exact (@lem2275512 (@lem2275522)). Qed.
Lemma lem2275525 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275526 : term418 = term419.
Proof. exact (@lem2275525 term400 term400). Qed.
Lemma lem2275527 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275528 : term421 = term400.
Proof. exact (EQ_MP (@lem2275527) (@lem940073)). Qed.
Lemma lem2275529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275530 : term419 = term398.
Proof. exact (MK_COMB (@lem2275529) (@lem2275528)). Qed.
Lemma lem2275531 : term418 = term398.
Proof. exact (TRANS (@lem2275526) (@lem2275530)). Qed.
Lemma lem2275533 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275534 : term424 = term425.
Proof. exact (@lem2275533 term400 term400). Qed.
Lemma lem2275535 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275536 : term421 = term400.
Proof. exact (EQ_MP (@lem2275535) (@lem940073)). Qed.
Lemma lem2275537 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275538 : term419 = term398.
Proof. exact (MK_COMB (@lem2275537) (@lem2275536)). Qed.
Lemma lem2275539 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275540 : term425 = term396.
Proof. exact (MK_COMB (@lem2275539) (@lem2275538)). Qed.
Lemma lem2275541 : term424 = term396.
Proof. exact (TRANS (@lem2275534) (@lem2275540)). Qed.
Lemma lem2275542 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275543 : term426 = term403.
Proof. exact (MK_COMB (@lem2275542) (@lem2275541)). Qed.
Lemma lem2275544 : term427 = term405.
Proof. exact (MK_COMB (@lem2275543) (@lem2275531)). Qed.
Lemma lem2275546 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2275547 : term405 = term408.
Proof. exact (@lem2275546 term400). Qed.
Lemma lem2275548 : term427 = term408.
Proof. exact (TRANS (@lem2275544) (@lem2275547)). Qed.
Lemma lem2275549 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275550 : term429 = term430.
Proof. exact (MK_COMB (@lem2275549) (@lem2275548)). Qed.
Lemma lem2275551 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2275552 : term431 = term432.
Proof. exact (MK_COMB (@lem2275550) (@lem2275551)). Qed.
Lemma lem2275554 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2275555 : term432 = term408.
Proof. exact (@lem2275554 term400). Qed.
Lemma lem2275556 : term431 = term408.
Proof. exact (TRANS (@lem2275552) (@lem2275555)). Qed.
Lemma lem2275558 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275559 : term418 = term419.
Proof. exact (@lem2275558 term400 term400). Qed.
Lemma lem2275560 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275561 : term421 = term400.
Proof. exact (EQ_MP (@lem2275560) (@lem940073)). Qed.
Lemma lem2275562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275563 : term419 = term398.
Proof. exact (MK_COMB (@lem2275562) (@lem2275561)). Qed.
Lemma lem2275564 : term418 = term398.
Proof. exact (TRANS (@lem2275559) (@lem2275563)). Qed.
Lemma lem2275565 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2275566 : term434 = term432.
Proof. exact (MK_COMB (@lem2275565) (@lem2275564)). Qed.
Lemma lem2275568 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2275569 : term432 = term408.
Proof. exact (@lem2275568 term400). Qed.
Lemma lem2275570 : term434 = term408.
Proof. exact (TRANS (@lem2275566) (@lem2275569)). Qed.
Lemma lem2275571 : term408 = term434.
Proof. exact (SYM (@lem2275570)). Qed.
Lemma lem2275572 : term431 = term434.
Proof. exact (TRANS (@lem2275556) (@lem2275571)). Qed.
Lemma lem2275573 : term406 = term435.
Proof. exact (@lem2275523 (@lem2275572)). Qed.
Lemma lem2275574 : term405 = term435.
Proof. exact (TRANS (@lem2275489) (@lem2275573)). Qed.
Lemma lem2275576 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2275577 : term435 = term408.
Proof. exact (@lem2275576 term408). Qed.
Lemma lem2275578 : term405 = term408.
Proof. exact (TRANS (@lem2275574) (@lem2275577)). Qed.
Lemma lem2275579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275580 : term437 = term430.
Proof. exact (MK_COMB (@lem2275579) (@lem2275578)). Qed.
Lemma lem2275581 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem2275582 (m : nat) : (term395 m) = (term433 m).
Proof. exact (MK_COMB (@lem2275580) (@lem2275581 m)). Qed.
Lemma lem2275583 (m : nat) : (term394 m) = (term433 m).
Proof. exact (TRANS (@lem2275480 m) (@lem2275582 m)). Qed.
Lemma lem2275584 (m : nat) : (term433 m) = term408.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem2275585 (m : nat) : (term394 m) = term408.
Proof. exact (TRANS (@lem2275583 m) (@lem2275584 m)). Qed.
Lemma lem2275586 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2275587 (m : nat) (d : nat) : (term393 d m) = (term438 d).
Proof. exact (MK_COMB (@lem2275586 d) (@lem2275585 m)). Qed.
Lemma lem2275588 (m : nat) (d : nat) : (term392 d m) = (term438 d).
Proof. exact (TRANS (@lem2275479 d m) (@lem2275587 m d)). Qed.
Lemma lem2275589 (d : nat) : (term438 d) = (term389 d).
Proof. exact (@lem1982723 (term389 d)). Qed.
Lemma lem2275590 (m : nat) (d : nat) : (term392 d m) = (term389 d).
Proof. exact (TRANS (@lem2275588 m d) (@lem2275589 d)). Qed.
Lemma lem2275591 (m : nat) (d : nat) : (term219 m d) = (term389 d).
Proof. exact (TRANS (@lem2275478 d m) (@lem2275590 m d)). Qed.
Lemma lem2275592 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2275593 (m : nat) (d : nat) : (term439 m d) = (term440 d).
Proof. exact (MK_COMB (@lem2275592) (@lem2275591 m d)). Qed.
Lemma lem2275594 (m : nat) (d : nat) : (term441 m d) = (term442 d).
Proof. exact (MK_COMB (@lem2275593 m d) (@lem2275455 d)). Qed.
Lemma lem2275595 (d : nat) : (term442 d) = (term443 d).
Proof. exact (@lem1982792 (term389 d) (real_of_num d)). Qed.
Lemma lem2275599 (d : nat) : (term443 d) = (term444 d).
Proof. exact (@lem1982711 term396 term396 (real_of_num d)). Qed.
Lemma lem2275601 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275602 : term396 = term402.
Proof. exact (@lem2275601 term400). Qed.
Lemma lem2275604 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275605 : term396 = term402.
Proof. exact (@lem2275604 term400). Qed.
Lemma lem2275606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275607 : term403 = term404.
Proof. exact (MK_COMB (@lem2275606) (@lem2275605)). Qed.
Lemma lem2275608 : term445 = term446.
Proof. exact (MK_COMB (@lem2275607) (@lem2275602)). Qed.
Lemma lem2275609 : term447.
Proof. exact (@lem1981473 term396 term398 term396 term398 term448 term398). Qed.
Lemma lem2275611 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275612 : term410 = term411.
Proof. exact (@lem2275611 (NUMERAL 0) term400). Qed.
Lemma lem2275613 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275614 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275615 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275614 h1) (fun h1 : term411 = True => @lem2275613)). Qed.
Lemma lem2275616 : term411 = True.
Proof. exact (EQ_MP (@lem2275615) (@lem2275613)). Qed.
Lemma lem2275617 : term410 = True.
Proof. exact (TRANS (@lem2275612) (@lem2275616)). Qed.
Lemma lem2275618 : True = term410.
Proof. exact (SYM (@lem2275617)). Qed.
Lemma lem2275619 : term410.
Proof. exact (EQ_MP (@lem2275618) (@lem0)). Qed.
Lemma lem2275620 : term449.
Proof. exact (@lem2275609 (@lem2275619)). Qed.
Lemma lem2275622 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275623 : term410 = term411.
Proof. exact (@lem2275622 (NUMERAL 0) term400). Qed.
Lemma lem2275624 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275625 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275626 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275625 h1) (fun h1 : term411 = True => @lem2275624)). Qed.
Lemma lem2275627 : term411 = True.
Proof. exact (EQ_MP (@lem2275626) (@lem2275624)). Qed.
Lemma lem2275628 : term410 = True.
Proof. exact (TRANS (@lem2275623) (@lem2275627)). Qed.
Lemma lem2275629 : True = term410.
Proof. exact (SYM (@lem2275628)). Qed.
Lemma lem2275630 : term410.
Proof. exact (EQ_MP (@lem2275629) (@lem0)). Qed.
Lemma lem2275631 : term450.
Proof. exact (@lem2275620 (@lem2275630)). Qed.
Lemma lem2275633 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275634 : term410 = term411.
Proof. exact (@lem2275633 (NUMERAL 0) term400). Qed.
Lemma lem2275635 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275636 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275637 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275636 h1) (fun h1 : term411 = True => @lem2275635)). Qed.
Lemma lem2275638 : term411 = True.
Proof. exact (EQ_MP (@lem2275637) (@lem2275635)). Qed.
Lemma lem2275639 : term410 = True.
Proof. exact (TRANS (@lem2275634) (@lem2275638)). Qed.
Lemma lem2275640 : True = term410.
Proof. exact (SYM (@lem2275639)). Qed.
Lemma lem2275641 : term410.
Proof. exact (EQ_MP (@lem2275640) (@lem0)). Qed.
Lemma lem2275642 : term451.
Proof. exact (@lem2275631 (@lem2275641)). Qed.
Lemma lem2275644 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275645 : term424 = term425.
Proof. exact (@lem2275644 term400 term400). Qed.
Lemma lem2275646 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275647 : term421 = term400.
Proof. exact (EQ_MP (@lem2275646) (@lem940073)). Qed.
Lemma lem2275648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275649 : term419 = term398.
Proof. exact (MK_COMB (@lem2275648) (@lem2275647)). Qed.
Lemma lem2275650 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275651 : term425 = term396.
Proof. exact (MK_COMB (@lem2275650) (@lem2275649)). Qed.
Lemma lem2275652 : term424 = term396.
Proof. exact (TRANS (@lem2275645) (@lem2275651)). Qed.
Lemma lem2275654 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275655 : term424 = term425.
Proof. exact (@lem2275654 term400 term400). Qed.
Lemma lem2275656 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275657 : term421 = term400.
Proof. exact (EQ_MP (@lem2275656) (@lem940073)). Qed.
Lemma lem2275658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275659 : term419 = term398.
Proof. exact (MK_COMB (@lem2275658) (@lem2275657)). Qed.
Lemma lem2275660 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275661 : term425 = term396.
Proof. exact (MK_COMB (@lem2275660) (@lem2275659)). Qed.
Lemma lem2275662 : term424 = term396.
Proof. exact (TRANS (@lem2275655) (@lem2275661)). Qed.
Lemma lem2275663 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275664 : term426 = term403.
Proof. exact (MK_COMB (@lem2275663) (@lem2275662)). Qed.
Lemma lem2275665 : term452 = term445.
Proof. exact (MK_COMB (@lem2275664) (@lem2275652)). Qed.
Lemma lem2275666 : term445 = term453.
Proof. exact (@lem1367763 term400 term400). Qed.
Lemma lem2275667 : term454 = term455.
Proof. exact (@lem706885). Qed.
Lemma lem2275668 : (term454 = term455) = (term456 = term457).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term455). Qed.
Lemma lem2275669 : term456 = term457.
Proof. exact (EQ_MP (@lem2275668) (@lem2275667)). Qed.
Lemma lem2275670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275671 : term458 = term459.
Proof. exact (MK_COMB (@lem2275670) (@lem2275669)). Qed.
Lemma lem2275672 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275673 : term453 = term448.
Proof. exact (MK_COMB (@lem2275672) (@lem2275671)). Qed.
Lemma lem2275674 : term445 = term448.
Proof. exact (TRANS (@lem2275666) (@lem2275673)). Qed.
Lemma lem2275675 : term452 = term448.
Proof. exact (TRANS (@lem2275665) (@lem2275674)). Qed.
Lemma lem2275676 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275677 : term460 = term461.
Proof. exact (MK_COMB (@lem2275676) (@lem2275675)). Qed.
Lemma lem2275678 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2275679 : term462 = term463.
Proof. exact (MK_COMB (@lem2275677) (@lem2275678)). Qed.
Lemma lem2275681 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275682 : term463 = term464.
Proof. exact (@lem2275681 term457 term400). Qed.
Lemma lem2275683 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2275684 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2275685 : term466 = term457.
Proof. exact (EQ_MP (@lem2275684) (@lem2275683)). Qed.
Lemma lem2275686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275687 : term467 = term459.
Proof. exact (MK_COMB (@lem2275686) (@lem2275685)). Qed.
Lemma lem2275688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275689 : term464 = term448.
Proof. exact (MK_COMB (@lem2275688) (@lem2275687)). Qed.
Lemma lem2275690 : term463 = term448.
Proof. exact (TRANS (@lem2275682) (@lem2275689)). Qed.
Lemma lem2275691 : term462 = term448.
Proof. exact (TRANS (@lem2275679) (@lem2275690)). Qed.
Lemma lem2275693 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275694 : term418 = term419.
Proof. exact (@lem2275693 term400 term400). Qed.
Lemma lem2275695 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275696 : term421 = term400.
Proof. exact (EQ_MP (@lem2275695) (@lem940073)). Qed.
Lemma lem2275697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275698 : term419 = term398.
Proof. exact (MK_COMB (@lem2275697) (@lem2275696)). Qed.
Lemma lem2275699 : term418 = term398.
Proof. exact (TRANS (@lem2275694) (@lem2275698)). Qed.
Lemma lem2275700 : term461 = term461.
Proof. exact (eq_refl term461). Qed.
Lemma lem2275701 : term468 = term463.
Proof. exact (MK_COMB (@lem2275700) (@lem2275699)). Qed.
Lemma lem2275703 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275704 : term463 = term464.
Proof. exact (@lem2275703 term457 term400). Qed.
Lemma lem2275705 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2275706 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2275707 : term466 = term457.
Proof. exact (EQ_MP (@lem2275706) (@lem2275705)). Qed.
Lemma lem2275708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275709 : term467 = term459.
Proof. exact (MK_COMB (@lem2275708) (@lem2275707)). Qed.
Lemma lem2275710 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275711 : term464 = term448.
Proof. exact (MK_COMB (@lem2275710) (@lem2275709)). Qed.
Lemma lem2275712 : term463 = term448.
Proof. exact (TRANS (@lem2275704) (@lem2275711)). Qed.
Lemma lem2275713 : term468 = term448.
Proof. exact (TRANS (@lem2275701) (@lem2275712)). Qed.
Lemma lem2275714 : term448 = term468.
Proof. exact (SYM (@lem2275713)). Qed.
Lemma lem2275715 : term462 = term468.
Proof. exact (TRANS (@lem2275691) (@lem2275714)). Qed.
Lemma lem2275716 : term446 = term469.
Proof. exact (@lem2275642 (@lem2275715)). Qed.
Lemma lem2275717 : term445 = term469.
Proof. exact (TRANS (@lem2275608) (@lem2275716)). Qed.
Lemma lem2275719 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2275720 : term469 = term448.
Proof. exact (@lem2275719 term448). Qed.
Lemma lem2275721 : term445 = term448.
Proof. exact (TRANS (@lem2275717) (@lem2275720)). Qed.
Lemma lem2275722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275723 : term470 = term461.
Proof. exact (MK_COMB (@lem2275722) (@lem2275721)). Qed.
Lemma lem2275724 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2275725 (d : nat) : (term444 d) = (term471 d).
Proof. exact (MK_COMB (@lem2275723) (@lem2275724 d)). Qed.
Lemma lem2275727 (d : nat) : (term443 d) = (term471 d).
Proof. exact (TRANS (@lem2275599 d) (@lem2275725 d)). Qed.
Lemma lem2275728 (d : nat) : (term442 d) = (term471 d).
Proof. exact (TRANS (@lem2275595 d) (@lem2275727 d)). Qed.
Lemma lem2275729 (m : nat) (d : nat) : (term441 m d) = (term471 d).
Proof. exact (TRANS (@lem2275594 m d) (@lem2275728 d)). Qed.
Lemma lem2275730 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275731 (m : nat) (d : nat) : (term472 m d) = (term473 d).
Proof. exact (MK_COMB (@lem2275730) (@lem2275729 m d)). Qed.
Lemma lem2275732 (d : nat) : (term473 d) = (term474 d).
Proof. exact (@lem1982785 (term471 d)). Qed.
Lemma lem2275733 (d : nat) : (term474 d) = (term475 d).
Proof. exact (@lem1982749 term396 term448 (real_of_num d)). Qed.
Lemma lem2275735 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275736 : term448 = term469.
Proof. exact (@lem2275735 term457). Qed.
Lemma lem2275738 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275739 : term396 = term402.
Proof. exact (@lem2275738 term400). Qed.
Lemma lem2275740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275741 : term476 = term477.
Proof. exact (MK_COMB (@lem2275740) (@lem2275739)). Qed.
Lemma lem2275742 : term478 = term479.
Proof. exact (MK_COMB (@lem2275741) (@lem2275736)). Qed.
Lemma lem2275743 : term479 = term480.
Proof. exact (@lem1981613 term396 term448 term398 term398). Qed.
Lemma lem2275745 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275746 : term418 = term419.
Proof. exact (@lem2275745 term400 term400). Qed.
Lemma lem2275747 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275748 : term421 = term400.
Proof. exact (EQ_MP (@lem2275747) (@lem940073)). Qed.
Lemma lem2275749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275750 : term419 = term398.
Proof. exact (MK_COMB (@lem2275749) (@lem2275748)). Qed.
Lemma lem2275751 : term418 = term398.
Proof. exact (TRANS (@lem2275746) (@lem2275750)). Qed.
Lemma lem2275753 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2275754 : term478 = term482.
Proof. exact (@lem2275753 term400 term457). Qed.
Lemma lem2275755 : term483 = term455.
Proof. exact (@lem996238 term455). Qed.
Lemma lem2275756 : (term483 = term455) = (term484 = term457).
Proof. exact (@lem1007663 (BIT1 0) term455 term455). Qed.
Lemma lem2275757 : term484 = term457.
Proof. exact (EQ_MP (@lem2275756) (@lem2275755)). Qed.
Lemma lem2275758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275759 : term482 = term459.
Proof. exact (MK_COMB (@lem2275758) (@lem2275757)). Qed.
Lemma lem2275760 : term478 = term459.
Proof. exact (TRANS (@lem2275754) (@lem2275759)). Qed.
Lemma lem2275761 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2275762 : term485 = term486.
Proof. exact (MK_COMB (@lem2275761) (@lem2275760)). Qed.
Lemma lem2275763 : term480 = term487.
Proof. exact (MK_COMB (@lem2275762) (@lem2275751)). Qed.
Lemma lem2275764 : term479 = term487.
Proof. exact (TRANS (@lem2275743) (@lem2275763)). Qed.
Lemma lem2275765 : term478 = term487.
Proof. exact (TRANS (@lem2275742) (@lem2275764)). Qed.
Lemma lem2275767 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2275768 : term487 = term459.
Proof. exact (@lem2275767 term459). Qed.
Lemma lem2275769 : term478 = term459.
Proof. exact (TRANS (@lem2275765) (@lem2275768)). Qed.
Lemma lem2275770 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275771 : term488 = term489.
Proof. exact (MK_COMB (@lem2275770) (@lem2275769)). Qed.
Lemma lem2275772 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2275773 (d : nat) : (term475 d) = (term490 d).
Proof. exact (MK_COMB (@lem2275771) (@lem2275772 d)). Qed.
Lemma lem2275774 (d : nat) : (term474 d) = (term490 d).
Proof. exact (TRANS (@lem2275733 d) (@lem2275773 d)). Qed.
Lemma lem2275775 (d : nat) : (term473 d) = (term490 d).
Proof. exact (TRANS (@lem2275732 d) (@lem2275774 d)). Qed.
Lemma lem2275776 (m : nat) (d : nat) : (term491 m d) = (term491 m d).
Proof. exact (eq_refl (term491 m d)). Qed.
Lemma lem2275777 (m : nat) (d : nat) : ((term472 m d) = (term473 d)) = ((term472 m d) = (term490 d)).
Proof. exact (MK_COMB (@lem2275776 m d) (@lem2275775 d)). Qed.
Lemma lem2275778 (m : nat) (d : nat) : (term472 m d) = (term490 d).
Proof. exact (EQ_MP (@lem2275777 m d) (@lem2275731 m d)). Qed.
Lemma lem2275779 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2275780 (m : nat) (d : nat) : (term492 m d) = (term493 d).
Proof. exact (MK_COMB (@lem2275779) (@lem2275778 m d)). Qed.
Lemma lem2275781 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2275782 (m : nat) (d : nat) : (term494 m d) = (term495 d).
Proof. exact (MK_COMB (@lem2275780 m d) (@lem2275781)). Qed.
Lemma lem2275783 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2275784 (m : nat) (d : nat) : (term496 m d) = (term497 d).
Proof. exact (MK_COMB (@lem2275783) (@lem2275729 m d)). Qed.
Lemma lem2275785 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2275786 (m : nat) (d : nat) : (term498 m d) = (term499 d).
Proof. exact (MK_COMB (@lem2275784 m d) (@lem2275785)). Qed.
Lemma lem2275787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2275788 (m : nat) (d : nat) : (term500 m d) = (term501 d).
Proof. exact (MK_COMB (@lem2275787) (@lem2275786 m d)). Qed.
Lemma lem2275789 (m : nat) (d : nat) : (term388 m d) = (term502 d).
Proof. exact (MK_COMB (@lem2275788 m d) (@lem2275782 m d)). Qed.
Lemma lem2275790 (m : nat) (d : nat) : (term387 m d) = (term502 d).
Proof. exact (TRANS (@lem2275454 m d) (@lem2275789 m d)). Qed.
Lemma lem2275791 (m : nat) (d : nat) : (term503 m d) = (term504 m d).
Proof. exact (@lem1988318 (term219 m d) (term93 d)). Qed.
Lemma lem2275798 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2275805 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2275812 (m : nat) : (term93 m) = (term389 m).
Proof. exact (@lem1982785 (real_of_num m)). Qed.
Lemma lem2275813 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275814 (m : nat) : (term127 m) = (term390 m).
Proof. exact (MK_COMB (@lem2275813) (@lem2275812 m)). Qed.
Lemma lem2275815 (m : nat) (d : nat) : (term136 m d) = (term391 m d).
Proof. exact (MK_COMB (@lem2275814 m) (@lem2275805 d)). Qed.
Lemma lem2275816 (d : nat) (m : nat) : (term391 m d) = (term391 d m).
Proof. exact (@lem1982761 (term389 d) (term389 m)). Qed.
Lemma lem2275817 (d : nat) (m : nat) : (term136 m d) = (term391 d m).
Proof. exact (TRANS (@lem2275815 m d) (@lem2275816 d m)). Qed.
Lemma lem2275820 (m : nat) : (term110 m) = (term110 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem2275821 (d : nat) (m : nat) : (term219 m d) = (term392 d m).
Proof. exact (MK_COMB (@lem2275820 m) (@lem2275817 d m)). Qed.
Lemma lem2275822 (d : nat) (m : nat) : (term392 d m) = (term393 d m).
Proof. exact (@lem1982757 (term389 d) (real_of_num m) (term389 m)). Qed.
Lemma lem2275823 (m : nat) : (term394 m) = (term395 m).
Proof. exact (@lem1982715 term396 (real_of_num m)). Qed.
Lemma lem2275825 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2275826 : term398 = term399.
Proof. exact (@lem2275825 term400). Qed.
Lemma lem2275828 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275829 : term396 = term402.
Proof. exact (@lem2275828 term400). Qed.
Lemma lem2275830 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275831 : term403 = term404.
Proof. exact (MK_COMB (@lem2275830) (@lem2275829)). Qed.
Lemma lem2275832 : term405 = term406.
Proof. exact (MK_COMB (@lem2275831) (@lem2275826)). Qed.
Lemma lem2275833 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2275835 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275836 : term410 = term411.
Proof. exact (@lem2275835 (NUMERAL 0) term400). Qed.
Lemma lem2275837 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275838 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275839 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275838 h1) (fun h1 : term411 = True => @lem2275837)). Qed.
Lemma lem2275840 : term411 = True.
Proof. exact (EQ_MP (@lem2275839) (@lem2275837)). Qed.
Lemma lem2275841 : term410 = True.
Proof. exact (TRANS (@lem2275836) (@lem2275840)). Qed.
Lemma lem2275842 : True = term410.
Proof. exact (SYM (@lem2275841)). Qed.
Lemma lem2275843 : term410.
Proof. exact (EQ_MP (@lem2275842) (@lem0)). Qed.
Lemma lem2275844 : term413.
Proof. exact (@lem2275833 (@lem2275843)). Qed.
Lemma lem2275846 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275847 : term410 = term411.
Proof. exact (@lem2275846 (NUMERAL 0) term400). Qed.
Lemma lem2275848 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275849 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275850 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275849 h1) (fun h1 : term411 = True => @lem2275848)). Qed.
Lemma lem2275851 : term411 = True.
Proof. exact (EQ_MP (@lem2275850) (@lem2275848)). Qed.
Lemma lem2275852 : term410 = True.
Proof. exact (TRANS (@lem2275847) (@lem2275851)). Qed.
Lemma lem2275853 : True = term410.
Proof. exact (SYM (@lem2275852)). Qed.
Lemma lem2275854 : term410.
Proof. exact (EQ_MP (@lem2275853) (@lem0)). Qed.
Lemma lem2275855 : term414.
Proof. exact (@lem2275844 (@lem2275854)). Qed.
Lemma lem2275857 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275858 : term410 = term411.
Proof. exact (@lem2275857 (NUMERAL 0) term400). Qed.
Lemma lem2275859 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275860 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2275861 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275860 h1) (fun h1 : term411 = True => @lem2275859)). Qed.
Lemma lem2275862 : term411 = True.
Proof. exact (EQ_MP (@lem2275861) (@lem2275859)). Qed.
Lemma lem2275863 : term410 = True.
Proof. exact (TRANS (@lem2275858) (@lem2275862)). Qed.
Lemma lem2275864 : True = term410.
Proof. exact (SYM (@lem2275863)). Qed.
Lemma lem2275865 : term410.
Proof. exact (EQ_MP (@lem2275864) (@lem0)). Qed.
Lemma lem2275866 : term415.
Proof. exact (@lem2275855 (@lem2275865)). Qed.
Lemma lem2275868 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275869 : term418 = term419.
Proof. exact (@lem2275868 term400 term400). Qed.
Lemma lem2275870 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275871 : term421 = term400.
Proof. exact (EQ_MP (@lem2275870) (@lem940073)). Qed.
Lemma lem2275872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275873 : term419 = term398.
Proof. exact (MK_COMB (@lem2275872) (@lem2275871)). Qed.
Lemma lem2275874 : term418 = term398.
Proof. exact (TRANS (@lem2275869) (@lem2275873)). Qed.
Lemma lem2275876 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2275877 : term424 = term425.
Proof. exact (@lem2275876 term400 term400). Qed.
Lemma lem2275878 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275879 : term421 = term400.
Proof. exact (EQ_MP (@lem2275878) (@lem940073)). Qed.
Lemma lem2275880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275881 : term419 = term398.
Proof. exact (MK_COMB (@lem2275880) (@lem2275879)). Qed.
Lemma lem2275882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2275883 : term425 = term396.
Proof. exact (MK_COMB (@lem2275882) (@lem2275881)). Qed.
Lemma lem2275884 : term424 = term396.
Proof. exact (TRANS (@lem2275877) (@lem2275883)). Qed.
Lemma lem2275885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275886 : term426 = term403.
Proof. exact (MK_COMB (@lem2275885) (@lem2275884)). Qed.
Lemma lem2275887 : term427 = term405.
Proof. exact (MK_COMB (@lem2275886) (@lem2275874)). Qed.
Lemma lem2275889 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2275890 : term405 = term408.
Proof. exact (@lem2275889 term400). Qed.
Lemma lem2275891 : term427 = term408.
Proof. exact (TRANS (@lem2275887) (@lem2275890)). Qed.
Lemma lem2275892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275893 : term429 = term430.
Proof. exact (MK_COMB (@lem2275892) (@lem2275891)). Qed.
Lemma lem2275894 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2275895 : term431 = term432.
Proof. exact (MK_COMB (@lem2275893) (@lem2275894)). Qed.
Lemma lem2275897 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2275898 : term432 = term408.
Proof. exact (@lem2275897 term400). Qed.
Lemma lem2275899 : term431 = term408.
Proof. exact (TRANS (@lem2275895) (@lem2275898)). Qed.
Lemma lem2275901 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275902 : term418 = term419.
Proof. exact (@lem2275901 term400 term400). Qed.
Lemma lem2275903 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275904 : term421 = term400.
Proof. exact (EQ_MP (@lem2275903) (@lem940073)). Qed.
Lemma lem2275905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275906 : term419 = term398.
Proof. exact (MK_COMB (@lem2275905) (@lem2275904)). Qed.
Lemma lem2275907 : term418 = term398.
Proof. exact (TRANS (@lem2275902) (@lem2275906)). Qed.
Lemma lem2275908 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2275909 : term434 = term432.
Proof. exact (MK_COMB (@lem2275908) (@lem2275907)). Qed.
Lemma lem2275911 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2275912 : term432 = term408.
Proof. exact (@lem2275911 term400). Qed.
Lemma lem2275913 : term434 = term408.
Proof. exact (TRANS (@lem2275909) (@lem2275912)). Qed.
Lemma lem2275914 : term408 = term434.
Proof. exact (SYM (@lem2275913)). Qed.
Lemma lem2275915 : term431 = term434.
Proof. exact (TRANS (@lem2275899) (@lem2275914)). Qed.
Lemma lem2275916 : term406 = term435.
Proof. exact (@lem2275866 (@lem2275915)). Qed.
Lemma lem2275917 : term405 = term435.
Proof. exact (TRANS (@lem2275832) (@lem2275916)). Qed.
Lemma lem2275919 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2275920 : term435 = term408.
Proof. exact (@lem2275919 term408). Qed.
Lemma lem2275921 : term405 = term408.
Proof. exact (TRANS (@lem2275917) (@lem2275920)). Qed.
Lemma lem2275922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275923 : term437 = term430.
Proof. exact (MK_COMB (@lem2275922) (@lem2275921)). Qed.
Lemma lem2275924 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem2275925 (m : nat) : (term395 m) = (term433 m).
Proof. exact (MK_COMB (@lem2275923) (@lem2275924 m)). Qed.
Lemma lem2275926 (m : nat) : (term394 m) = (term433 m).
Proof. exact (TRANS (@lem2275823 m) (@lem2275925 m)). Qed.
Lemma lem2275927 (m : nat) : (term433 m) = term408.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem2275928 (m : nat) : (term394 m) = term408.
Proof. exact (TRANS (@lem2275926 m) (@lem2275927 m)). Qed.
Lemma lem2275929 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2275930 (m : nat) (d : nat) : (term393 d m) = (term438 d).
Proof. exact (MK_COMB (@lem2275929 d) (@lem2275928 m)). Qed.
Lemma lem2275931 (m : nat) (d : nat) : (term392 d m) = (term438 d).
Proof. exact (TRANS (@lem2275822 d m) (@lem2275930 m d)). Qed.
Lemma lem2275932 (d : nat) : (term438 d) = (term389 d).
Proof. exact (@lem1982723 (term389 d)). Qed.
Lemma lem2275933 (m : nat) (d : nat) : (term392 d m) = (term389 d).
Proof. exact (TRANS (@lem2275931 m d) (@lem2275932 d)). Qed.
Lemma lem2275934 (m : nat) (d : nat) : (term219 m d) = (term389 d).
Proof. exact (TRANS (@lem2275821 d m) (@lem2275933 m d)). Qed.
Lemma lem2275935 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2275936 (m : nat) (d : nat) : (term439 m d) = (term440 d).
Proof. exact (MK_COMB (@lem2275935) (@lem2275934 m d)). Qed.
Lemma lem2275937 (m : nat) (d : nat) : (term505 m d) = (term506 d).
Proof. exact (MK_COMB (@lem2275936 m d) (@lem2275798 d)). Qed.
Lemma lem2275938 (d : nat) : (term506 d) = (term507 d).
Proof. exact (@lem1982792 (term389 d) (term389 d)). Qed.
Lemma lem2275939 (d : nat) : (term508 d) = (term509 d).
Proof. exact (@lem1982749 term396 term396 (real_of_num d)). Qed.
Lemma lem2275941 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275942 : term396 = term402.
Proof. exact (@lem2275941 term400). Qed.
Lemma lem2275944 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275945 : term396 = term402.
Proof. exact (@lem2275944 term400). Qed.
Lemma lem2275946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275947 : term476 = term477.
Proof. exact (MK_COMB (@lem2275946) (@lem2275945)). Qed.
Lemma lem2275948 : term510 = term511.
Proof. exact (MK_COMB (@lem2275947) (@lem2275942)). Qed.
Lemma lem2275949 : term511 = term512.
Proof. exact (@lem1981613 term396 term396 term398 term398). Qed.
Lemma lem2275951 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2275952 : term418 = term419.
Proof. exact (@lem2275951 term400 term400). Qed.
Lemma lem2275953 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275954 : term421 = term400.
Proof. exact (EQ_MP (@lem2275953) (@lem940073)). Qed.
Lemma lem2275955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275956 : term419 = term398.
Proof. exact (MK_COMB (@lem2275955) (@lem2275954)). Qed.
Lemma lem2275957 : term418 = term398.
Proof. exact (TRANS (@lem2275952) (@lem2275956)). Qed.
Lemma lem2275959 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2275960 : term510 = term419.
Proof. exact (@lem2275959 term400 term400). Qed.
Lemma lem2275961 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2275962 : term421 = term400.
Proof. exact (EQ_MP (@lem2275961) (@lem940073)). Qed.
Lemma lem2275963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2275964 : term419 = term398.
Proof. exact (MK_COMB (@lem2275963) (@lem2275962)). Qed.
Lemma lem2275965 : term510 = term398.
Proof. exact (TRANS (@lem2275960) (@lem2275964)). Qed.
Lemma lem2275966 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2275967 : term513 = term514.
Proof. exact (MK_COMB (@lem2275966) (@lem2275965)). Qed.
Lemma lem2275968 : term512 = term399.
Proof. exact (MK_COMB (@lem2275967) (@lem2275957)). Qed.
Lemma lem2275969 : term511 = term399.
Proof. exact (TRANS (@lem2275949) (@lem2275968)). Qed.
Lemma lem2275970 : term510 = term399.
Proof. exact (TRANS (@lem2275948) (@lem2275969)). Qed.
Lemma lem2275972 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2275973 : term399 = term398.
Proof. exact (@lem2275972 term398). Qed.
Lemma lem2275974 : term510 = term398.
Proof. exact (TRANS (@lem2275970) (@lem2275973)). Qed.
Lemma lem2275975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2275976 : term515 = term516.
Proof. exact (MK_COMB (@lem2275975) (@lem2275974)). Qed.
Lemma lem2275977 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2275978 (d : nat) : (term509 d) = (term517 d).
Proof. exact (MK_COMB (@lem2275976) (@lem2275977 d)). Qed.
Lemma lem2275979 (d : nat) : (term508 d) = (term517 d).
Proof. exact (TRANS (@lem2275939 d) (@lem2275978 d)). Qed.
Lemma lem2275980 (d : nat) : (term517 d) = (real_of_num d).
Proof. exact (@lem1982709 (real_of_num d)). Qed.
Lemma lem2275981 (d : nat) : (term508 d) = (real_of_num d).
Proof. exact (TRANS (@lem2275979 d) (@lem2275980 d)). Qed.
Lemma lem2275982 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2275983 (d : nat) : (term507 d) = (term518 d).
Proof. exact (MK_COMB (@lem2275982 d) (@lem2275981 d)). Qed.
Lemma lem2275984 (d : nat) : (term518 d) = (term395 d).
Proof. exact (@lem1982713 term396 (real_of_num d)). Qed.
Lemma lem2275986 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2275987 : term398 = term399.
Proof. exact (@lem2275986 term400). Qed.
Lemma lem2275989 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2275990 : term396 = term402.
Proof. exact (@lem2275989 term400). Qed.
Lemma lem2275991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2275992 : term403 = term404.
Proof. exact (MK_COMB (@lem2275991) (@lem2275990)). Qed.
Lemma lem2275993 : term405 = term406.
Proof. exact (MK_COMB (@lem2275992) (@lem2275987)). Qed.
Lemma lem2275994 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2275996 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2275997 : term410 = term411.
Proof. exact (@lem2275996 (NUMERAL 0) term400). Qed.
Lemma lem2275998 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2275999 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276000 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2275999 h1) (fun h1 : term411 = True => @lem2275998)). Qed.
Lemma lem2276001 : term411 = True.
Proof. exact (EQ_MP (@lem2276000) (@lem2275998)). Qed.
Lemma lem2276002 : term410 = True.
Proof. exact (TRANS (@lem2275997) (@lem2276001)). Qed.
Lemma lem2276003 : True = term410.
Proof. exact (SYM (@lem2276002)). Qed.
Lemma lem2276004 : term410.
Proof. exact (EQ_MP (@lem2276003) (@lem0)). Qed.
Lemma lem2276005 : term413.
Proof. exact (@lem2275994 (@lem2276004)). Qed.
Lemma lem2276007 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276008 : term410 = term411.
Proof. exact (@lem2276007 (NUMERAL 0) term400). Qed.
Lemma lem2276009 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276010 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276011 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276010 h1) (fun h1 : term411 = True => @lem2276009)). Qed.
Lemma lem2276012 : term411 = True.
Proof. exact (EQ_MP (@lem2276011) (@lem2276009)). Qed.
Lemma lem2276013 : term410 = True.
Proof. exact (TRANS (@lem2276008) (@lem2276012)). Qed.
Lemma lem2276014 : True = term410.
Proof. exact (SYM (@lem2276013)). Qed.
Lemma lem2276015 : term410.
Proof. exact (EQ_MP (@lem2276014) (@lem0)). Qed.
Lemma lem2276016 : term414.
Proof. exact (@lem2276005 (@lem2276015)). Qed.
Lemma lem2276018 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276019 : term410 = term411.
Proof. exact (@lem2276018 (NUMERAL 0) term400). Qed.
Lemma lem2276020 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276021 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276022 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276021 h1) (fun h1 : term411 = True => @lem2276020)). Qed.
Lemma lem2276023 : term411 = True.
Proof. exact (EQ_MP (@lem2276022) (@lem2276020)). Qed.
Lemma lem2276024 : term410 = True.
Proof. exact (TRANS (@lem2276019) (@lem2276023)). Qed.
Lemma lem2276025 : True = term410.
Proof. exact (SYM (@lem2276024)). Qed.
Lemma lem2276026 : term410.
Proof. exact (EQ_MP (@lem2276025) (@lem0)). Qed.
Lemma lem2276027 : term415.
Proof. exact (@lem2276016 (@lem2276026)). Qed.
Lemma lem2276029 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276030 : term418 = term419.
Proof. exact (@lem2276029 term400 term400). Qed.
Lemma lem2276031 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276032 : term421 = term400.
Proof. exact (EQ_MP (@lem2276031) (@lem940073)). Qed.
Lemma lem2276033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276034 : term419 = term398.
Proof. exact (MK_COMB (@lem2276033) (@lem2276032)). Qed.
Lemma lem2276035 : term418 = term398.
Proof. exact (TRANS (@lem2276030) (@lem2276034)). Qed.
Lemma lem2276037 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2276038 : term424 = term425.
Proof. exact (@lem2276037 term400 term400). Qed.
Lemma lem2276039 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276040 : term421 = term400.
Proof. exact (EQ_MP (@lem2276039) (@lem940073)). Qed.
Lemma lem2276041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276042 : term419 = term398.
Proof. exact (MK_COMB (@lem2276041) (@lem2276040)). Qed.
Lemma lem2276043 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276044 : term425 = term396.
Proof. exact (MK_COMB (@lem2276043) (@lem2276042)). Qed.
Lemma lem2276045 : term424 = term396.
Proof. exact (TRANS (@lem2276038) (@lem2276044)). Qed.
Lemma lem2276046 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276047 : term426 = term403.
Proof. exact (MK_COMB (@lem2276046) (@lem2276045)). Qed.
Lemma lem2276048 : term427 = term405.
Proof. exact (MK_COMB (@lem2276047) (@lem2276035)). Qed.
Lemma lem2276050 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2276051 : term405 = term408.
Proof. exact (@lem2276050 term400). Qed.
Lemma lem2276052 : term427 = term408.
Proof. exact (TRANS (@lem2276048) (@lem2276051)). Qed.
Lemma lem2276053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276054 : term429 = term430.
Proof. exact (MK_COMB (@lem2276053) (@lem2276052)). Qed.
Lemma lem2276055 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2276056 : term431 = term432.
Proof. exact (MK_COMB (@lem2276054) (@lem2276055)). Qed.
Lemma lem2276058 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276059 : term432 = term408.
Proof. exact (@lem2276058 term400). Qed.
Lemma lem2276060 : term431 = term408.
Proof. exact (TRANS (@lem2276056) (@lem2276059)). Qed.
Lemma lem2276062 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276063 : term418 = term419.
Proof. exact (@lem2276062 term400 term400). Qed.
Lemma lem2276064 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276065 : term421 = term400.
Proof. exact (EQ_MP (@lem2276064) (@lem940073)). Qed.
Lemma lem2276066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276067 : term419 = term398.
Proof. exact (MK_COMB (@lem2276066) (@lem2276065)). Qed.
Lemma lem2276068 : term418 = term398.
Proof. exact (TRANS (@lem2276063) (@lem2276067)). Qed.
Lemma lem2276069 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2276070 : term434 = term432.
Proof. exact (MK_COMB (@lem2276069) (@lem2276068)). Qed.
Lemma lem2276072 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276073 : term432 = term408.
Proof. exact (@lem2276072 term400). Qed.
Lemma lem2276074 : term434 = term408.
Proof. exact (TRANS (@lem2276070) (@lem2276073)). Qed.
Lemma lem2276075 : term408 = term434.
Proof. exact (SYM (@lem2276074)). Qed.
Lemma lem2276076 : term431 = term434.
Proof. exact (TRANS (@lem2276060) (@lem2276075)). Qed.
Lemma lem2276077 : term406 = term435.
Proof. exact (@lem2276027 (@lem2276076)). Qed.
Lemma lem2276078 : term405 = term435.
Proof. exact (TRANS (@lem2275993) (@lem2276077)). Qed.
Lemma lem2276080 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2276081 : term435 = term408.
Proof. exact (@lem2276080 term408). Qed.
Lemma lem2276082 : term405 = term408.
Proof. exact (TRANS (@lem2276078) (@lem2276081)). Qed.
Lemma lem2276083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276084 : term437 = term430.
Proof. exact (MK_COMB (@lem2276083) (@lem2276082)). Qed.
Lemma lem2276085 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2276086 (d : nat) : (term395 d) = (term433 d).
Proof. exact (MK_COMB (@lem2276084) (@lem2276085 d)). Qed.
Lemma lem2276087 (d : nat) : (term518 d) = (term433 d).
Proof. exact (TRANS (@lem2275984 d) (@lem2276086 d)). Qed.
Lemma lem2276088 (d : nat) : (term433 d) = term408.
Proof. exact (@lem1982719 (real_of_num d)). Qed.
Lemma lem2276089 (d : nat) : (term518 d) = term408.
Proof. exact (TRANS (@lem2276087 d) (@lem2276088 d)). Qed.
Lemma lem2276090 (d : nat) : (term507 d) = term408.
Proof. exact (TRANS (@lem2275983 d) (@lem2276089 d)). Qed.
Lemma lem2276091 (d : nat) : (term506 d) = term408.
Proof. exact (TRANS (@lem2275938 d) (@lem2276090 d)). Qed.
Lemma lem2276092 (m : nat) (d : nat) : (term505 m d) = term408.
Proof. exact (TRANS (@lem2275937 m d) (@lem2276091 d)). Qed.
Lemma lem2276093 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276094 (m : nat) (d : nat) : (term519 m d) = term520.
Proof. exact (MK_COMB (@lem2276093) (@lem2276092 m d)). Qed.
Lemma lem2276095 : term520 = term521.
Proof. exact (@lem1982785 term408). Qed.
Lemma lem2276097 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276098 : term408 = term435.
Proof. exact (@lem2276097 (NUMERAL 0)). Qed.
Lemma lem2276100 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276101 : term396 = term402.
Proof. exact (@lem2276100 term400). Qed.
Lemma lem2276102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276103 : term476 = term477.
Proof. exact (MK_COMB (@lem2276102) (@lem2276101)). Qed.
Lemma lem2276104 : term521 = term522.
Proof. exact (MK_COMB (@lem2276103) (@lem2276098)). Qed.
Lemma lem2276105 : term522 = term523.
Proof. exact (@lem1981613 term396 term408 term398 term398). Qed.
Lemma lem2276107 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276108 : term418 = term419.
Proof. exact (@lem2276107 term400 term400). Qed.
Lemma lem2276109 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276110 : term421 = term400.
Proof. exact (EQ_MP (@lem2276109) (@lem940073)). Qed.
Lemma lem2276111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276112 : term419 = term398.
Proof. exact (MK_COMB (@lem2276111) (@lem2276110)). Qed.
Lemma lem2276113 : term418 = term398.
Proof. exact (TRANS (@lem2276108) (@lem2276112)). Qed.
Lemma lem2276115 (x : nat) : (term524 x) = term408.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2276116 : term521 = term408.
Proof. exact (@lem2276115 term400). Qed.
Lemma lem2276117 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2276118 : term525 = term526.
Proof. exact (MK_COMB (@lem2276117) (@lem2276116)). Qed.
Lemma lem2276119 : term523 = term435.
Proof. exact (MK_COMB (@lem2276118) (@lem2276113)). Qed.
Lemma lem2276120 : term522 = term435.
Proof. exact (TRANS (@lem2276105) (@lem2276119)). Qed.
Lemma lem2276121 : term521 = term435.
Proof. exact (TRANS (@lem2276104) (@lem2276120)). Qed.
Lemma lem2276123 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2276124 : term435 = term408.
Proof. exact (@lem2276123 term408). Qed.
Lemma lem2276125 : term521 = term408.
Proof. exact (TRANS (@lem2276121) (@lem2276124)). Qed.
Lemma lem2276126 : term520 = term408.
Proof. exact (TRANS (@lem2276095) (@lem2276125)). Qed.
Lemma lem2276127 (m : nat) (d : nat) : (term527 m d) = (term527 m d).
Proof. exact (eq_refl (term527 m d)). Qed.
Lemma lem2276128 (m : nat) (d : nat) : ((term519 m d) = term520) = ((term519 m d) = term408).
Proof. exact (MK_COMB (@lem2276127 m d) (@lem2276126)). Qed.
Lemma lem2276129 (m : nat) (d : nat) : (term519 m d) = term408.
Proof. exact (EQ_MP (@lem2276128 m d) (@lem2276094 m d)). Qed.
Lemma lem2276130 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2276131 (m : nat) (d : nat) : (term528 m d) = term529.
Proof. exact (MK_COMB (@lem2276130) (@lem2276129 m d)). Qed.
Lemma lem2276132 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2276133 (m : nat) (d : nat) : (term530 m d) = term531.
Proof. exact (MK_COMB (@lem2276131 m d) (@lem2276132)). Qed.
Lemma lem2276134 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2276135 (m : nat) (d : nat) : (term532 m d) = term529.
Proof. exact (MK_COMB (@lem2276134) (@lem2276092 m d)). Qed.
Lemma lem2276136 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2276137 (m : nat) (d : nat) : (term533 m d) = term531.
Proof. exact (MK_COMB (@lem2276135 m d) (@lem2276136)). Qed.
Lemma lem2276138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2276139 (m : nat) (d : nat) : (term534 m d) = term535.
Proof. exact (MK_COMB (@lem2276138) (@lem2276137 m d)). Qed.
Lemma lem2276140 (m : nat) (d : nat) : (term504 m d) = term536.
Proof. exact (MK_COMB (@lem2276139 m d) (@lem2276133 m d)). Qed.
Lemma lem2276141 (m : nat) (d : nat) : (term503 m d) = term536.
Proof. exact (TRANS (@lem2275791 m d) (@lem2276140 m d)). Qed.
Lemma lem2276142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2276143 (m : nat) (d : nat) : (term537 m d) = (term538 d).
Proof. exact (MK_COMB (@lem2276142) (@lem2275790 m d)). Qed.
Lemma lem2276144 (m : nat) (d : nat) : (term386 m d) = (term539 d).
Proof. exact (MK_COMB (@lem2276143 m d) (@lem2276141 m d)). Qed.
Lemma lem2276151 (m : nat) (d : nat) : (term385 m d) = (term539 d).
Proof. exact (TRANS (@lem2275453 m d) (@lem2276144 m d)). Qed.
Lemma lem2276165 (d : nat) : (term539 d) = (term540 d).
Proof. exact (@lem19158 term531 (term502 d) term531). Qed.
Lemma lem2276172 (d : nat) : (term541 d) = (term542 d).
Proof. exact (@lem19367 (term499 d) (term495 d) term531). Qed.
Lemma lem2276179 (d : nat) : (term541 d) = (term542 d).
Proof. exact (@lem19367 (term499 d) (term495 d) term531). Qed.
Lemma lem2276180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2276181 (d : nat) : (term543 d) = (term544 d).
Proof. exact (MK_COMB (@lem2276180) (@lem2276179 d)). Qed.
Lemma lem2276182 (d : nat) : (term540 d) = (term545 d).
Proof. exact (MK_COMB (@lem2276181 d) (@lem2276172 d)). Qed.
Lemma lem2276184 (d : nat) : (term539 d) = (term545 d).
Proof. exact (TRANS (@lem2276165 d) (@lem2276182 d)). Qed.
Lemma lem2276185 (m : nat) (d : nat) : (term385 m d) = (term545 d).
Proof. exact (TRANS (@lem2276151 m d) (@lem2276184 d)). Qed.
Lemma lem2276207 (d : nat) (h1 : term545 d) : term545 d.
Proof. exact (h1). Qed.
Lemma lem2276208 (d : nat) (h1 : term542 d) : term542 d.
Proof. exact (h1). Qed.
Lemma lem2276209 (d : nat) (h1 : term546 d) : term546 d.
Proof. exact (h1). Qed.
Lemma lem2276210 (d : nat) (h1 : term546 d) : term531.
Proof. exact (proj2 (@lem2276209 d h1)). Qed.
Lemma lem2276214 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2276215 : term531 = term547.
Proof. exact (@lem2276214 term408 term408). Qed.
Lemma lem2276217 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276218 : term408 = term435.
Proof. exact (@lem2276217 (NUMERAL 0)). Qed.
Lemma lem2276220 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276221 : term408 = term435.
Proof. exact (@lem2276220 (NUMERAL 0)). Qed.
Lemma lem2276222 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276223 : term548 = term549.
Proof. exact (MK_COMB (@lem2276222) (@lem2276221)). Qed.
Lemma lem2276224 : term547 = term550.
Proof. exact (MK_COMB (@lem2276223) (@lem2276218)). Qed.
Lemma lem2276225 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2276227 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276228 : term410 = term411.
Proof. exact (@lem2276227 (NUMERAL 0) term400). Qed.
Lemma lem2276229 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276230 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276231 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276230 h1) (fun h1 : term411 = True => @lem2276229)). Qed.
Lemma lem2276232 : term411 = True.
Proof. exact (EQ_MP (@lem2276231) (@lem2276229)). Qed.
Lemma lem2276233 : term410 = True.
Proof. exact (TRANS (@lem2276228) (@lem2276232)). Qed.
Lemma lem2276234 : True = term410.
Proof. exact (SYM (@lem2276233)). Qed.
Lemma lem2276235 : term410.
Proof. exact (EQ_MP (@lem2276234) (@lem0)). Qed.
Lemma lem2276236 : term552.
Proof. exact (@lem2276225 (@lem2276235)). Qed.
Lemma lem2276238 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276239 : term410 = term411.
Proof. exact (@lem2276238 (NUMERAL 0) term400). Qed.
Lemma lem2276240 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276241 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276242 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276241 h1) (fun h1 : term411 = True => @lem2276240)). Qed.
Lemma lem2276243 : term411 = True.
Proof. exact (EQ_MP (@lem2276242) (@lem2276240)). Qed.
Lemma lem2276244 : term410 = True.
Proof. exact (TRANS (@lem2276239) (@lem2276243)). Qed.
Lemma lem2276245 : True = term410.
Proof. exact (SYM (@lem2276244)). Qed.
Lemma lem2276246 : term410.
Proof. exact (EQ_MP (@lem2276245) (@lem0)). Qed.
Lemma lem2276247 : term550 = term553.
Proof. exact (@lem2276236 (@lem2276246)). Qed.
Lemma lem2276249 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276250 : term432 = term408.
Proof. exact (@lem2276249 term400). Qed.
Lemma lem2276252 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276253 : term432 = term408.
Proof. exact (@lem2276252 term400). Qed.
Lemma lem2276254 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276255 : term554 = term548.
Proof. exact (MK_COMB (@lem2276254) (@lem2276253)). Qed.
Lemma lem2276256 : term553 = term547.
Proof. exact (MK_COMB (@lem2276255) (@lem2276250)). Qed.
Lemma lem2276258 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276259 : term547 = term555.
Proof. exact (@lem2276258 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2276260 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2276261 : term547 = False.
Proof. exact (TRANS (@lem2276259) (@lem2276260)). Qed.
Lemma lem2276262 : term553 = False.
Proof. exact (TRANS (@lem2276256) (@lem2276261)). Qed.
Lemma lem2276263 : term550 = False.
Proof. exact (TRANS (@lem2276247) (@lem2276262)). Qed.
Lemma lem2276264 : term547 = False.
Proof. exact (TRANS (@lem2276224) (@lem2276263)). Qed.
Lemma lem2276265 : term531 = False.
Proof. exact (TRANS (@lem2276215) (@lem2276264)). Qed.
Lemma lem2276266 (d : nat) (h1 : term546 d) : False.
Proof. exact (EQ_MP (@lem2276265) (@lem2276210 d h1)). Qed.
Lemma lem2276267 (d : nat) (h1 : term556 d) : term556 d.
Proof. exact (h1). Qed.
Lemma lem2276268 (d : nat) (h1 : term556 d) : term531.
Proof. exact (proj2 (@lem2276267 d h1)). Qed.
Lemma lem2276272 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2276273 : term531 = term547.
Proof. exact (@lem2276272 term408 term408). Qed.
Lemma lem2276275 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276276 : term408 = term435.
Proof. exact (@lem2276275 (NUMERAL 0)). Qed.
Lemma lem2276278 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276279 : term408 = term435.
Proof. exact (@lem2276278 (NUMERAL 0)). Qed.
Lemma lem2276280 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276281 : term548 = term549.
Proof. exact (MK_COMB (@lem2276280) (@lem2276279)). Qed.
Lemma lem2276282 : term547 = term550.
Proof. exact (MK_COMB (@lem2276281) (@lem2276276)). Qed.
Lemma lem2276283 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2276285 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276286 : term410 = term411.
Proof. exact (@lem2276285 (NUMERAL 0) term400). Qed.
Lemma lem2276287 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276288 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276289 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276288 h1) (fun h1 : term411 = True => @lem2276287)). Qed.
Lemma lem2276290 : term411 = True.
Proof. exact (EQ_MP (@lem2276289) (@lem2276287)). Qed.
Lemma lem2276291 : term410 = True.
Proof. exact (TRANS (@lem2276286) (@lem2276290)). Qed.
Lemma lem2276292 : True = term410.
Proof. exact (SYM (@lem2276291)). Qed.
Lemma lem2276293 : term410.
Proof. exact (EQ_MP (@lem2276292) (@lem0)). Qed.
Lemma lem2276294 : term552.
Proof. exact (@lem2276283 (@lem2276293)). Qed.
Lemma lem2276296 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276297 : term410 = term411.
Proof. exact (@lem2276296 (NUMERAL 0) term400). Qed.
Lemma lem2276298 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276299 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276300 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276299 h1) (fun h1 : term411 = True => @lem2276298)). Qed.
Lemma lem2276301 : term411 = True.
Proof. exact (EQ_MP (@lem2276300) (@lem2276298)). Qed.
Lemma lem2276302 : term410 = True.
Proof. exact (TRANS (@lem2276297) (@lem2276301)). Qed.
Lemma lem2276303 : True = term410.
Proof. exact (SYM (@lem2276302)). Qed.
Lemma lem2276304 : term410.
Proof. exact (EQ_MP (@lem2276303) (@lem0)). Qed.
Lemma lem2276305 : term550 = term553.
Proof. exact (@lem2276294 (@lem2276304)). Qed.
Lemma lem2276307 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276308 : term432 = term408.
Proof. exact (@lem2276307 term400). Qed.
Lemma lem2276310 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276311 : term432 = term408.
Proof. exact (@lem2276310 term400). Qed.
Lemma lem2276312 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276313 : term554 = term548.
Proof. exact (MK_COMB (@lem2276312) (@lem2276311)). Qed.
Lemma lem2276314 : term553 = term547.
Proof. exact (MK_COMB (@lem2276313) (@lem2276308)). Qed.
Lemma lem2276316 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276317 : term547 = term555.
Proof. exact (@lem2276316 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2276318 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2276319 : term547 = False.
Proof. exact (TRANS (@lem2276317) (@lem2276318)). Qed.
Lemma lem2276320 : term553 = False.
Proof. exact (TRANS (@lem2276314) (@lem2276319)). Qed.
Lemma lem2276321 : term550 = False.
Proof. exact (TRANS (@lem2276305) (@lem2276320)). Qed.
Lemma lem2276322 : term547 = False.
Proof. exact (TRANS (@lem2276282) (@lem2276321)). Qed.
Lemma lem2276323 : term531 = False.
Proof. exact (TRANS (@lem2276273) (@lem2276322)). Qed.
Lemma lem2276324 (d : nat) (h1 : term556 d) : False.
Proof. exact (EQ_MP (@lem2276323) (@lem2276268 d h1)). Qed.
Lemma lem2276325 (d : nat) (h1 : term542 d) : False.
Proof. exact (or_elim (@lem2276208 d h1) (fun h0 : term546 d => @lem2276266 d h0) (fun h0 : term556 d => @lem2276324 d h0)). Qed.
Lemma lem2276326 (d : nat) (h1 : term542 d) : term542 d.
Proof. exact (h1). Qed.
Lemma lem2276327 (d : nat) (h1 : term546 d) : term546 d.
Proof. exact (h1). Qed.
Lemma lem2276328 (d : nat) (h1 : term546 d) : term531.
Proof. exact (proj2 (@lem2276327 d h1)). Qed.
Lemma lem2276332 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2276333 : term531 = term547.
Proof. exact (@lem2276332 term408 term408). Qed.
Lemma lem2276335 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276336 : term408 = term435.
Proof. exact (@lem2276335 (NUMERAL 0)). Qed.
Lemma lem2276338 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276339 : term408 = term435.
Proof. exact (@lem2276338 (NUMERAL 0)). Qed.
Lemma lem2276340 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276341 : term548 = term549.
Proof. exact (MK_COMB (@lem2276340) (@lem2276339)). Qed.
Lemma lem2276342 : term547 = term550.
Proof. exact (MK_COMB (@lem2276341) (@lem2276336)). Qed.
Lemma lem2276343 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2276345 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276346 : term410 = term411.
Proof. exact (@lem2276345 (NUMERAL 0) term400). Qed.
Lemma lem2276347 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276348 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276349 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276348 h1) (fun h1 : term411 = True => @lem2276347)). Qed.
Lemma lem2276350 : term411 = True.
Proof. exact (EQ_MP (@lem2276349) (@lem2276347)). Qed.
Lemma lem2276351 : term410 = True.
Proof. exact (TRANS (@lem2276346) (@lem2276350)). Qed.
Lemma lem2276352 : True = term410.
Proof. exact (SYM (@lem2276351)). Qed.
Lemma lem2276353 : term410.
Proof. exact (EQ_MP (@lem2276352) (@lem0)). Qed.
Lemma lem2276354 : term552.
Proof. exact (@lem2276343 (@lem2276353)). Qed.
Lemma lem2276356 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276357 : term410 = term411.
Proof. exact (@lem2276356 (NUMERAL 0) term400). Qed.
Lemma lem2276358 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276359 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276360 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276359 h1) (fun h1 : term411 = True => @lem2276358)). Qed.
Lemma lem2276361 : term411 = True.
Proof. exact (EQ_MP (@lem2276360) (@lem2276358)). Qed.
Lemma lem2276362 : term410 = True.
Proof. exact (TRANS (@lem2276357) (@lem2276361)). Qed.
Lemma lem2276363 : True = term410.
Proof. exact (SYM (@lem2276362)). Qed.
Lemma lem2276364 : term410.
Proof. exact (EQ_MP (@lem2276363) (@lem0)). Qed.
Lemma lem2276365 : term550 = term553.
Proof. exact (@lem2276354 (@lem2276364)). Qed.
Lemma lem2276367 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276368 : term432 = term408.
Proof. exact (@lem2276367 term400). Qed.
Lemma lem2276370 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276371 : term432 = term408.
Proof. exact (@lem2276370 term400). Qed.
Lemma lem2276372 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276373 : term554 = term548.
Proof. exact (MK_COMB (@lem2276372) (@lem2276371)). Qed.
Lemma lem2276374 : term553 = term547.
Proof. exact (MK_COMB (@lem2276373) (@lem2276368)). Qed.
Lemma lem2276376 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276377 : term547 = term555.
Proof. exact (@lem2276376 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2276378 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2276379 : term547 = False.
Proof. exact (TRANS (@lem2276377) (@lem2276378)). Qed.
Lemma lem2276380 : term553 = False.
Proof. exact (TRANS (@lem2276374) (@lem2276379)). Qed.
Lemma lem2276381 : term550 = False.
Proof. exact (TRANS (@lem2276365) (@lem2276380)). Qed.
Lemma lem2276382 : term547 = False.
Proof. exact (TRANS (@lem2276342) (@lem2276381)). Qed.
Lemma lem2276383 : term531 = False.
Proof. exact (TRANS (@lem2276333) (@lem2276382)). Qed.
Lemma lem2276384 (d : nat) (h1 : term546 d) : False.
Proof. exact (EQ_MP (@lem2276383) (@lem2276328 d h1)). Qed.
Lemma lem2276385 (d : nat) (h1 : term556 d) : term556 d.
Proof. exact (h1). Qed.
Lemma lem2276386 (d : nat) (h1 : term556 d) : term531.
Proof. exact (proj2 (@lem2276385 d h1)). Qed.
Lemma lem2276390 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2276391 : term531 = term547.
Proof. exact (@lem2276390 term408 term408). Qed.
Lemma lem2276393 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276394 : term408 = term435.
Proof. exact (@lem2276393 (NUMERAL 0)). Qed.
Lemma lem2276396 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276397 : term408 = term435.
Proof. exact (@lem2276396 (NUMERAL 0)). Qed.
Lemma lem2276398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276399 : term548 = term549.
Proof. exact (MK_COMB (@lem2276398) (@lem2276397)). Qed.
Lemma lem2276400 : term547 = term550.
Proof. exact (MK_COMB (@lem2276399) (@lem2276394)). Qed.
Lemma lem2276401 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2276403 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276404 : term410 = term411.
Proof. exact (@lem2276403 (NUMERAL 0) term400). Qed.
Lemma lem2276405 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276406 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276407 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276406 h1) (fun h1 : term411 = True => @lem2276405)). Qed.
Lemma lem2276408 : term411 = True.
Proof. exact (EQ_MP (@lem2276407) (@lem2276405)). Qed.
Lemma lem2276409 : term410 = True.
Proof. exact (TRANS (@lem2276404) (@lem2276408)). Qed.
Lemma lem2276410 : True = term410.
Proof. exact (SYM (@lem2276409)). Qed.
Lemma lem2276411 : term410.
Proof. exact (EQ_MP (@lem2276410) (@lem0)). Qed.
Lemma lem2276412 : term552.
Proof. exact (@lem2276401 (@lem2276411)). Qed.
Lemma lem2276414 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276415 : term410 = term411.
Proof. exact (@lem2276414 (NUMERAL 0) term400). Qed.
Lemma lem2276416 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276417 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276418 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276417 h1) (fun h1 : term411 = True => @lem2276416)). Qed.
Lemma lem2276419 : term411 = True.
Proof. exact (EQ_MP (@lem2276418) (@lem2276416)). Qed.
Lemma lem2276420 : term410 = True.
Proof. exact (TRANS (@lem2276415) (@lem2276419)). Qed.
Lemma lem2276421 : True = term410.
Proof. exact (SYM (@lem2276420)). Qed.
Lemma lem2276422 : term410.
Proof. exact (EQ_MP (@lem2276421) (@lem0)). Qed.
Lemma lem2276423 : term550 = term553.
Proof. exact (@lem2276412 (@lem2276422)). Qed.
Lemma lem2276425 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276426 : term432 = term408.
Proof. exact (@lem2276425 term400). Qed.
Lemma lem2276428 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276429 : term432 = term408.
Proof. exact (@lem2276428 term400). Qed.
Lemma lem2276430 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2276431 : term554 = term548.
Proof. exact (MK_COMB (@lem2276430) (@lem2276429)). Qed.
Lemma lem2276432 : term553 = term547.
Proof. exact (MK_COMB (@lem2276431) (@lem2276426)). Qed.
Lemma lem2276434 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276435 : term547 = term555.
Proof. exact (@lem2276434 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2276436 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2276437 : term547 = False.
Proof. exact (TRANS (@lem2276435) (@lem2276436)). Qed.
Lemma lem2276438 : term553 = False.
Proof. exact (TRANS (@lem2276432) (@lem2276437)). Qed.
Lemma lem2276439 : term550 = False.
Proof. exact (TRANS (@lem2276423) (@lem2276438)). Qed.
Lemma lem2276440 : term547 = False.
Proof. exact (TRANS (@lem2276400) (@lem2276439)). Qed.
Lemma lem2276441 : term531 = False.
Proof. exact (TRANS (@lem2276391) (@lem2276440)). Qed.
Lemma lem2276442 (d : nat) (h1 : term556 d) : False.
Proof. exact (EQ_MP (@lem2276441) (@lem2276386 d h1)). Qed.
Lemma lem2276443 (d : nat) (h1 : term542 d) : False.
Proof. exact (or_elim (@lem2276326 d h1) (fun h0 : term546 d => @lem2276384 d h0) (fun h0 : term556 d => @lem2276442 d h0)). Qed.
Lemma lem2276444 (d : nat) (h1 : term545 d) : False.
Proof. exact (or_elim (@lem2276207 d h1) (fun h0 : term542 d => @lem2276325 d h0) (fun h0 : term542 d => @lem2276443 d h0)). Qed.
Lemma lem2276446 (d : nat) (h1 : term545 d) : term545 d.
Proof. exact (h1). Qed.
Lemma lem2276447 (d : nat) (h1 : term545 d) : (term545 d) = False.
Proof. exact (prop_ext (fun h2 : term545 d => @lem2276444 d h1) (fun h2 : False => @lem2276446 d h1)). Qed.
Lemma lem2276448 (d : nat) (h1 : term545 d) : False.
Proof. exact (EQ_MP (@lem2276447 d h1) (@lem2276446 d h1)). Qed.
Lemma lem2276449 (m : nat) (d : nat) (h1 : term385 m d) : term385 m d.
Proof. exact (h1). Qed.
Lemma lem2276450 (m : nat) (d : nat) (h1 : term385 m d) : term545 d.
Proof. exact (EQ_MP (@lem2276185 m d) (@lem2276449 m d h1)). Qed.
Lemma lem2276451 (m : nat) (d : nat) (h1 : term385 m d) : (term545 d) = False.
Proof. exact (prop_ext (fun h2 : term545 d => @lem2276448 d h2) (fun h2 : False => @lem2276450 m d h1)). Qed.
Lemma lem2276452 (m : nat) (d : nat) (h1 : term385 m d) : False.
Proof. exact (EQ_MP (@lem2276451 m d h1) (@lem2276450 m d h1)). Qed.
Lemma lem2276453 (m : nat) (d : nat) : term557 m d.
Proof. exact (fun h0 : term385 m d => @lem2276452 m d h0). Qed.
Lemma lem2276454 (m : nat) (d : nat) : term558 m d.
Proof. exact (@lem1386578 (term559 m d)). Qed.
Lemma lem2276457 (m : nat) (d : nat) : term559 m d.
Proof. exact (@lem2276454 m d (@lem2276453 m d)). Qed.
Lemma lem2276458 (m : nat) (d : nat) : term225 m d.
Proof. exact (ex_intro (term224 m d) d (@lem2276457 m d)). Qed.
Lemma lem2276482 (n : nat) (d : nat) : (term560 n d) = (term561 n d).
Proof. exact (@lem17160 ((term252 d n) = (real_of_num d)) ((term252 d n) = (term93 d))). Qed.
Lemma lem2276483 (n : nat) (d : nat) : (term562 n d) = (term563 n d).
Proof. exact (@lem1988318 (term252 d n) (real_of_num d)). Qed.
Lemma lem2276484 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2276491 (n : nat) : (term93 n) = (term389 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2276498 (d : nat) (n : nat) : (term25 n d) = (term25 d n).
Proof. exact (@lem1982761 (real_of_num d) (real_of_num n)). Qed.
Lemma lem2276499 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276500 (d : nat) (n : nat) : (term251 n d) = (term251 d n).
Proof. exact (MK_COMB (@lem2276499) (@lem2276498 d n)). Qed.
Lemma lem2276501 (d : nat) (n : nat) : (term252 d n) = (term564 d n).
Proof. exact (MK_COMB (@lem2276500 d n) (@lem2276491 n)). Qed.
Lemma lem2276502 (d : nat) (n : nat) : (term564 d n) = (term565 d n).
Proof. exact (@lem1982755 (real_of_num d) (real_of_num n) (term389 n)). Qed.
Lemma lem2276503 (n : nat) : (term394 n) = (term395 n).
Proof. exact (@lem1982715 term396 (real_of_num n)). Qed.
Lemma lem2276505 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276506 : term398 = term399.
Proof. exact (@lem2276505 term400). Qed.
Lemma lem2276508 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276509 : term396 = term402.
Proof. exact (@lem2276508 term400). Qed.
Lemma lem2276510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276511 : term403 = term404.
Proof. exact (MK_COMB (@lem2276510) (@lem2276509)). Qed.
Lemma lem2276512 : term405 = term406.
Proof. exact (MK_COMB (@lem2276511) (@lem2276506)). Qed.
Lemma lem2276513 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2276515 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276516 : term410 = term411.
Proof. exact (@lem2276515 (NUMERAL 0) term400). Qed.
Lemma lem2276517 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276518 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276519 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276518 h1) (fun h1 : term411 = True => @lem2276517)). Qed.
Lemma lem2276520 : term411 = True.
Proof. exact (EQ_MP (@lem2276519) (@lem2276517)). Qed.
Lemma lem2276521 : term410 = True.
Proof. exact (TRANS (@lem2276516) (@lem2276520)). Qed.
Lemma lem2276522 : True = term410.
Proof. exact (SYM (@lem2276521)). Qed.
Lemma lem2276523 : term410.
Proof. exact (EQ_MP (@lem2276522) (@lem0)). Qed.
Lemma lem2276524 : term413.
Proof. exact (@lem2276513 (@lem2276523)). Qed.
Lemma lem2276526 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276527 : term410 = term411.
Proof. exact (@lem2276526 (NUMERAL 0) term400). Qed.
Lemma lem2276528 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276529 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276530 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276529 h1) (fun h1 : term411 = True => @lem2276528)). Qed.
Lemma lem2276531 : term411 = True.
Proof. exact (EQ_MP (@lem2276530) (@lem2276528)). Qed.
Lemma lem2276532 : term410 = True.
Proof. exact (TRANS (@lem2276527) (@lem2276531)). Qed.
Lemma lem2276533 : True = term410.
Proof. exact (SYM (@lem2276532)). Qed.
Lemma lem2276534 : term410.
Proof. exact (EQ_MP (@lem2276533) (@lem0)). Qed.
Lemma lem2276535 : term414.
Proof. exact (@lem2276524 (@lem2276534)). Qed.
Lemma lem2276537 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276538 : term410 = term411.
Proof. exact (@lem2276537 (NUMERAL 0) term400). Qed.
Lemma lem2276539 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276540 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276541 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276540 h1) (fun h1 : term411 = True => @lem2276539)). Qed.
Lemma lem2276542 : term411 = True.
Proof. exact (EQ_MP (@lem2276541) (@lem2276539)). Qed.
Lemma lem2276543 : term410 = True.
Proof. exact (TRANS (@lem2276538) (@lem2276542)). Qed.
Lemma lem2276544 : True = term410.
Proof. exact (SYM (@lem2276543)). Qed.
Lemma lem2276545 : term410.
Proof. exact (EQ_MP (@lem2276544) (@lem0)). Qed.
Lemma lem2276546 : term415.
Proof. exact (@lem2276535 (@lem2276545)). Qed.
Lemma lem2276548 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276549 : term418 = term419.
Proof. exact (@lem2276548 term400 term400). Qed.
Lemma lem2276550 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276551 : term421 = term400.
Proof. exact (EQ_MP (@lem2276550) (@lem940073)). Qed.
Lemma lem2276552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276553 : term419 = term398.
Proof. exact (MK_COMB (@lem2276552) (@lem2276551)). Qed.
Lemma lem2276554 : term418 = term398.
Proof. exact (TRANS (@lem2276549) (@lem2276553)). Qed.
Lemma lem2276556 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2276557 : term424 = term425.
Proof. exact (@lem2276556 term400 term400). Qed.
Lemma lem2276558 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276559 : term421 = term400.
Proof. exact (EQ_MP (@lem2276558) (@lem940073)). Qed.
Lemma lem2276560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276561 : term419 = term398.
Proof. exact (MK_COMB (@lem2276560) (@lem2276559)). Qed.
Lemma lem2276562 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276563 : term425 = term396.
Proof. exact (MK_COMB (@lem2276562) (@lem2276561)). Qed.
Lemma lem2276564 : term424 = term396.
Proof. exact (TRANS (@lem2276557) (@lem2276563)). Qed.
Lemma lem2276565 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276566 : term426 = term403.
Proof. exact (MK_COMB (@lem2276565) (@lem2276564)). Qed.
Lemma lem2276567 : term427 = term405.
Proof. exact (MK_COMB (@lem2276566) (@lem2276554)). Qed.
Lemma lem2276569 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2276570 : term405 = term408.
Proof. exact (@lem2276569 term400). Qed.
Lemma lem2276571 : term427 = term408.
Proof. exact (TRANS (@lem2276567) (@lem2276570)). Qed.
Lemma lem2276572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276573 : term429 = term430.
Proof. exact (MK_COMB (@lem2276572) (@lem2276571)). Qed.
Lemma lem2276574 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2276575 : term431 = term432.
Proof. exact (MK_COMB (@lem2276573) (@lem2276574)). Qed.
Lemma lem2276577 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276578 : term432 = term408.
Proof. exact (@lem2276577 term400). Qed.
Lemma lem2276579 : term431 = term408.
Proof. exact (TRANS (@lem2276575) (@lem2276578)). Qed.
Lemma lem2276581 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276582 : term418 = term419.
Proof. exact (@lem2276581 term400 term400). Qed.
Lemma lem2276583 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276584 : term421 = term400.
Proof. exact (EQ_MP (@lem2276583) (@lem940073)). Qed.
Lemma lem2276585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276586 : term419 = term398.
Proof. exact (MK_COMB (@lem2276585) (@lem2276584)). Qed.
Lemma lem2276587 : term418 = term398.
Proof. exact (TRANS (@lem2276582) (@lem2276586)). Qed.
Lemma lem2276588 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2276589 : term434 = term432.
Proof. exact (MK_COMB (@lem2276588) (@lem2276587)). Qed.
Lemma lem2276591 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276592 : term432 = term408.
Proof. exact (@lem2276591 term400). Qed.
Lemma lem2276593 : term434 = term408.
Proof. exact (TRANS (@lem2276589) (@lem2276592)). Qed.
Lemma lem2276594 : term408 = term434.
Proof. exact (SYM (@lem2276593)). Qed.
Lemma lem2276595 : term431 = term434.
Proof. exact (TRANS (@lem2276579) (@lem2276594)). Qed.
Lemma lem2276596 : term406 = term435.
Proof. exact (@lem2276546 (@lem2276595)). Qed.
Lemma lem2276597 : term405 = term435.
Proof. exact (TRANS (@lem2276512) (@lem2276596)). Qed.
Lemma lem2276599 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2276600 : term435 = term408.
Proof. exact (@lem2276599 term408). Qed.
Lemma lem2276601 : term405 = term408.
Proof. exact (TRANS (@lem2276597) (@lem2276600)). Qed.
Lemma lem2276602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276603 : term437 = term430.
Proof. exact (MK_COMB (@lem2276602) (@lem2276601)). Qed.
Lemma lem2276604 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2276605 (n : nat) : (term395 n) = (term433 n).
Proof. exact (MK_COMB (@lem2276603) (@lem2276604 n)). Qed.
Lemma lem2276606 (n : nat) : (term394 n) = (term433 n).
Proof. exact (TRANS (@lem2276503 n) (@lem2276605 n)). Qed.
Lemma lem2276607 (n : nat) : (term433 n) = term408.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2276608 (n : nat) : (term394 n) = term408.
Proof. exact (TRANS (@lem2276606 n) (@lem2276607 n)). Qed.
Lemma lem2276609 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2276610 (n : nat) (d : nat) : (term565 d n) = (term566 d).
Proof. exact (MK_COMB (@lem2276609 d) (@lem2276608 n)). Qed.
Lemma lem2276611 (n : nat) (d : nat) : (term564 d n) = (term566 d).
Proof. exact (TRANS (@lem2276502 d n) (@lem2276610 n d)). Qed.
Lemma lem2276612 (d : nat) : (term566 d) = (real_of_num d).
Proof. exact (@lem1982723 (real_of_num d)). Qed.
Lemma lem2276613 (n : nat) (d : nat) : (term564 d n) = (real_of_num d).
Proof. exact (TRANS (@lem2276611 n d) (@lem2276612 d)). Qed.
Lemma lem2276614 (n : nat) (d : nat) : (term252 d n) = (real_of_num d).
Proof. exact (TRANS (@lem2276501 d n) (@lem2276613 n d)). Qed.
Lemma lem2276615 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2276616 (n : nat) (d : nat) : (term567 d n) = (term568 d).
Proof. exact (MK_COMB (@lem2276615) (@lem2276614 n d)). Qed.
Lemma lem2276617 (n : nat) (d : nat) : (term569 n d) = (term570 d).
Proof. exact (MK_COMB (@lem2276616 n d) (@lem2276484 d)). Qed.
Lemma lem2276618 (d : nat) : (term570 d) = (term394 d).
Proof. exact (@lem1982792 (real_of_num d) (real_of_num d)). Qed.
Lemma lem2276622 (d : nat) : (term394 d) = (term395 d).
Proof. exact (@lem1982715 term396 (real_of_num d)). Qed.
Lemma lem2276624 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276625 : term398 = term399.
Proof. exact (@lem2276624 term400). Qed.
Lemma lem2276627 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276628 : term396 = term402.
Proof. exact (@lem2276627 term400). Qed.
Lemma lem2276629 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276630 : term403 = term404.
Proof. exact (MK_COMB (@lem2276629) (@lem2276628)). Qed.
Lemma lem2276631 : term405 = term406.
Proof. exact (MK_COMB (@lem2276630) (@lem2276625)). Qed.
Lemma lem2276632 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2276634 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276635 : term410 = term411.
Proof. exact (@lem2276634 (NUMERAL 0) term400). Qed.
Lemma lem2276636 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276637 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276638 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276637 h1) (fun h1 : term411 = True => @lem2276636)). Qed.
Lemma lem2276639 : term411 = True.
Proof. exact (EQ_MP (@lem2276638) (@lem2276636)). Qed.
Lemma lem2276640 : term410 = True.
Proof. exact (TRANS (@lem2276635) (@lem2276639)). Qed.
Lemma lem2276641 : True = term410.
Proof. exact (SYM (@lem2276640)). Qed.
Lemma lem2276642 : term410.
Proof. exact (EQ_MP (@lem2276641) (@lem0)). Qed.
Lemma lem2276643 : term413.
Proof. exact (@lem2276632 (@lem2276642)). Qed.
Lemma lem2276645 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276646 : term410 = term411.
Proof. exact (@lem2276645 (NUMERAL 0) term400). Qed.
Lemma lem2276647 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276648 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276649 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276648 h1) (fun h1 : term411 = True => @lem2276647)). Qed.
Lemma lem2276650 : term411 = True.
Proof. exact (EQ_MP (@lem2276649) (@lem2276647)). Qed.
Lemma lem2276651 : term410 = True.
Proof. exact (TRANS (@lem2276646) (@lem2276650)). Qed.
Lemma lem2276652 : True = term410.
Proof. exact (SYM (@lem2276651)). Qed.
Lemma lem2276653 : term410.
Proof. exact (EQ_MP (@lem2276652) (@lem0)). Qed.
Lemma lem2276654 : term414.
Proof. exact (@lem2276643 (@lem2276653)). Qed.
Lemma lem2276656 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276657 : term410 = term411.
Proof. exact (@lem2276656 (NUMERAL 0) term400). Qed.
Lemma lem2276658 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276659 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276660 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276659 h1) (fun h1 : term411 = True => @lem2276658)). Qed.
Lemma lem2276661 : term411 = True.
Proof. exact (EQ_MP (@lem2276660) (@lem2276658)). Qed.
Lemma lem2276662 : term410 = True.
Proof. exact (TRANS (@lem2276657) (@lem2276661)). Qed.
Lemma lem2276663 : True = term410.
Proof. exact (SYM (@lem2276662)). Qed.
Lemma lem2276664 : term410.
Proof. exact (EQ_MP (@lem2276663) (@lem0)). Qed.
Lemma lem2276665 : term415.
Proof. exact (@lem2276654 (@lem2276664)). Qed.
Lemma lem2276667 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276668 : term418 = term419.
Proof. exact (@lem2276667 term400 term400). Qed.
Lemma lem2276669 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276670 : term421 = term400.
Proof. exact (EQ_MP (@lem2276669) (@lem940073)). Qed.
Lemma lem2276671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276672 : term419 = term398.
Proof. exact (MK_COMB (@lem2276671) (@lem2276670)). Qed.
Lemma lem2276673 : term418 = term398.
Proof. exact (TRANS (@lem2276668) (@lem2276672)). Qed.
Lemma lem2276675 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2276676 : term424 = term425.
Proof. exact (@lem2276675 term400 term400). Qed.
Lemma lem2276677 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276678 : term421 = term400.
Proof. exact (EQ_MP (@lem2276677) (@lem940073)). Qed.
Lemma lem2276679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276680 : term419 = term398.
Proof. exact (MK_COMB (@lem2276679) (@lem2276678)). Qed.
Lemma lem2276681 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276682 : term425 = term396.
Proof. exact (MK_COMB (@lem2276681) (@lem2276680)). Qed.
Lemma lem2276683 : term424 = term396.
Proof. exact (TRANS (@lem2276676) (@lem2276682)). Qed.
Lemma lem2276684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276685 : term426 = term403.
Proof. exact (MK_COMB (@lem2276684) (@lem2276683)). Qed.
Lemma lem2276686 : term427 = term405.
Proof. exact (MK_COMB (@lem2276685) (@lem2276673)). Qed.
Lemma lem2276688 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2276689 : term405 = term408.
Proof. exact (@lem2276688 term400). Qed.
Lemma lem2276690 : term427 = term408.
Proof. exact (TRANS (@lem2276686) (@lem2276689)). Qed.
Lemma lem2276691 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276692 : term429 = term430.
Proof. exact (MK_COMB (@lem2276691) (@lem2276690)). Qed.
Lemma lem2276693 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2276694 : term431 = term432.
Proof. exact (MK_COMB (@lem2276692) (@lem2276693)). Qed.
Lemma lem2276696 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276697 : term432 = term408.
Proof. exact (@lem2276696 term400). Qed.
Lemma lem2276698 : term431 = term408.
Proof. exact (TRANS (@lem2276694) (@lem2276697)). Qed.
Lemma lem2276700 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276701 : term418 = term419.
Proof. exact (@lem2276700 term400 term400). Qed.
Lemma lem2276702 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276703 : term421 = term400.
Proof. exact (EQ_MP (@lem2276702) (@lem940073)). Qed.
Lemma lem2276704 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276705 : term419 = term398.
Proof. exact (MK_COMB (@lem2276704) (@lem2276703)). Qed.
Lemma lem2276706 : term418 = term398.
Proof. exact (TRANS (@lem2276701) (@lem2276705)). Qed.
Lemma lem2276707 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2276708 : term434 = term432.
Proof. exact (MK_COMB (@lem2276707) (@lem2276706)). Qed.
Lemma lem2276710 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276711 : term432 = term408.
Proof. exact (@lem2276710 term400). Qed.
Lemma lem2276712 : term434 = term408.
Proof. exact (TRANS (@lem2276708) (@lem2276711)). Qed.
Lemma lem2276713 : term408 = term434.
Proof. exact (SYM (@lem2276712)). Qed.
Lemma lem2276714 : term431 = term434.
Proof. exact (TRANS (@lem2276698) (@lem2276713)). Qed.
Lemma lem2276715 : term406 = term435.
Proof. exact (@lem2276665 (@lem2276714)). Qed.
Lemma lem2276716 : term405 = term435.
Proof. exact (TRANS (@lem2276631) (@lem2276715)). Qed.
Lemma lem2276718 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2276719 : term435 = term408.
Proof. exact (@lem2276718 term408). Qed.
Lemma lem2276720 : term405 = term408.
Proof. exact (TRANS (@lem2276716) (@lem2276719)). Qed.
Lemma lem2276721 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276722 : term437 = term430.
Proof. exact (MK_COMB (@lem2276721) (@lem2276720)). Qed.
Lemma lem2276723 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2276724 (d : nat) : (term395 d) = (term433 d).
Proof. exact (MK_COMB (@lem2276722) (@lem2276723 d)). Qed.
Lemma lem2276725 (d : nat) : (term394 d) = (term433 d).
Proof. exact (TRANS (@lem2276622 d) (@lem2276724 d)). Qed.
Lemma lem2276726 (d : nat) : (term433 d) = term408.
Proof. exact (@lem1982719 (real_of_num d)). Qed.
Lemma lem2276728 (d : nat) : (term394 d) = term408.
Proof. exact (TRANS (@lem2276725 d) (@lem2276726 d)). Qed.
Lemma lem2276729 (d : nat) : (term570 d) = term408.
Proof. exact (TRANS (@lem2276618 d) (@lem2276728 d)). Qed.
Lemma lem2276730 (n : nat) (d : nat) : (term569 n d) = term408.
Proof. exact (TRANS (@lem2276617 n d) (@lem2276729 d)). Qed.
Lemma lem2276731 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276732 (n : nat) (d : nat) : (term571 n d) = term520.
Proof. exact (MK_COMB (@lem2276731) (@lem2276730 n d)). Qed.
Lemma lem2276733 : term520 = term521.
Proof. exact (@lem1982785 term408). Qed.
Lemma lem2276735 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276736 : term408 = term435.
Proof. exact (@lem2276735 (NUMERAL 0)). Qed.
Lemma lem2276738 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276739 : term396 = term402.
Proof. exact (@lem2276738 term400). Qed.
Lemma lem2276740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276741 : term476 = term477.
Proof. exact (MK_COMB (@lem2276740) (@lem2276739)). Qed.
Lemma lem2276742 : term521 = term522.
Proof. exact (MK_COMB (@lem2276741) (@lem2276736)). Qed.
Lemma lem2276743 : term522 = term523.
Proof. exact (@lem1981613 term396 term408 term398 term398). Qed.
Lemma lem2276745 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276746 : term418 = term419.
Proof. exact (@lem2276745 term400 term400). Qed.
Lemma lem2276747 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276748 : term421 = term400.
Proof. exact (EQ_MP (@lem2276747) (@lem940073)). Qed.
Lemma lem2276749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276750 : term419 = term398.
Proof. exact (MK_COMB (@lem2276749) (@lem2276748)). Qed.
Lemma lem2276751 : term418 = term398.
Proof. exact (TRANS (@lem2276746) (@lem2276750)). Qed.
Lemma lem2276753 (x : nat) : (term524 x) = term408.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2276754 : term521 = term408.
Proof. exact (@lem2276753 term400). Qed.
Lemma lem2276755 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2276756 : term525 = term526.
Proof. exact (MK_COMB (@lem2276755) (@lem2276754)). Qed.
Lemma lem2276757 : term523 = term435.
Proof. exact (MK_COMB (@lem2276756) (@lem2276751)). Qed.
Lemma lem2276758 : term522 = term435.
Proof. exact (TRANS (@lem2276743) (@lem2276757)). Qed.
Lemma lem2276759 : term521 = term435.
Proof. exact (TRANS (@lem2276742) (@lem2276758)). Qed.
Lemma lem2276761 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2276762 : term435 = term408.
Proof. exact (@lem2276761 term408). Qed.
Lemma lem2276763 : term521 = term408.
Proof. exact (TRANS (@lem2276759) (@lem2276762)). Qed.
Lemma lem2276764 : term520 = term408.
Proof. exact (TRANS (@lem2276733) (@lem2276763)). Qed.
Lemma lem2276765 (n : nat) (d : nat) : (term572 n d) = (term572 n d).
Proof. exact (eq_refl (term572 n d)). Qed.
Lemma lem2276766 (n : nat) (d : nat) : ((term571 n d) = term520) = ((term571 n d) = term408).
Proof. exact (MK_COMB (@lem2276765 n d) (@lem2276764)). Qed.
Lemma lem2276767 (n : nat) (d : nat) : (term571 n d) = term408.
Proof. exact (EQ_MP (@lem2276766 n d) (@lem2276732 n d)). Qed.
Lemma lem2276768 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2276769 (n : nat) (d : nat) : (term573 n d) = term529.
Proof. exact (MK_COMB (@lem2276768) (@lem2276767 n d)). Qed.
Lemma lem2276770 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2276771 (n : nat) (d : nat) : (term574 n d) = term531.
Proof. exact (MK_COMB (@lem2276769 n d) (@lem2276770)). Qed.
Lemma lem2276772 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2276773 (n : nat) (d : nat) : (term575 n d) = term529.
Proof. exact (MK_COMB (@lem2276772) (@lem2276730 n d)). Qed.
Lemma lem2276774 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2276775 (n : nat) (d : nat) : (term576 n d) = term531.
Proof. exact (MK_COMB (@lem2276773 n d) (@lem2276774)). Qed.
Lemma lem2276776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2276777 (n : nat) (d : nat) : (term577 n d) = term535.
Proof. exact (MK_COMB (@lem2276776) (@lem2276775 n d)). Qed.
Lemma lem2276778 (n : nat) (d : nat) : (term563 n d) = term536.
Proof. exact (MK_COMB (@lem2276777 n d) (@lem2276771 n d)). Qed.
Lemma lem2276779 (n : nat) (d : nat) : (term562 n d) = term536.
Proof. exact (TRANS (@lem2276483 n d) (@lem2276778 n d)). Qed.
Lemma lem2276780 (n : nat) (d : nat) : (term578 n d) = (term579 n d).
Proof. exact (@lem1988318 (term252 d n) (term93 d)). Qed.
Lemma lem2276787 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2276794 (n : nat) : (term93 n) = (term389 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2276801 (d : nat) (n : nat) : (term25 n d) = (term25 d n).
Proof. exact (@lem1982761 (real_of_num d) (real_of_num n)). Qed.
Lemma lem2276802 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276803 (d : nat) (n : nat) : (term251 n d) = (term251 d n).
Proof. exact (MK_COMB (@lem2276802) (@lem2276801 d n)). Qed.
Lemma lem2276804 (d : nat) (n : nat) : (term252 d n) = (term564 d n).
Proof. exact (MK_COMB (@lem2276803 d n) (@lem2276794 n)). Qed.
Lemma lem2276805 (d : nat) (n : nat) : (term564 d n) = (term565 d n).
Proof. exact (@lem1982755 (real_of_num d) (real_of_num n) (term389 n)). Qed.
Lemma lem2276806 (n : nat) : (term394 n) = (term395 n).
Proof. exact (@lem1982715 term396 (real_of_num n)). Qed.
Lemma lem2276808 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276809 : term398 = term399.
Proof. exact (@lem2276808 term400). Qed.
Lemma lem2276811 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276812 : term396 = term402.
Proof. exact (@lem2276811 term400). Qed.
Lemma lem2276813 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276814 : term403 = term404.
Proof. exact (MK_COMB (@lem2276813) (@lem2276812)). Qed.
Lemma lem2276815 : term405 = term406.
Proof. exact (MK_COMB (@lem2276814) (@lem2276809)). Qed.
Lemma lem2276816 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2276818 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276819 : term410 = term411.
Proof. exact (@lem2276818 (NUMERAL 0) term400). Qed.
Lemma lem2276820 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276821 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276822 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276821 h1) (fun h1 : term411 = True => @lem2276820)). Qed.
Lemma lem2276823 : term411 = True.
Proof. exact (EQ_MP (@lem2276822) (@lem2276820)). Qed.
Lemma lem2276824 : term410 = True.
Proof. exact (TRANS (@lem2276819) (@lem2276823)). Qed.
Lemma lem2276825 : True = term410.
Proof. exact (SYM (@lem2276824)). Qed.
Lemma lem2276826 : term410.
Proof. exact (EQ_MP (@lem2276825) (@lem0)). Qed.
Lemma lem2276827 : term413.
Proof. exact (@lem2276816 (@lem2276826)). Qed.
Lemma lem2276829 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276830 : term410 = term411.
Proof. exact (@lem2276829 (NUMERAL 0) term400). Qed.
Lemma lem2276831 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276832 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276833 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276832 h1) (fun h1 : term411 = True => @lem2276831)). Qed.
Lemma lem2276834 : term411 = True.
Proof. exact (EQ_MP (@lem2276833) (@lem2276831)). Qed.
Lemma lem2276835 : term410 = True.
Proof. exact (TRANS (@lem2276830) (@lem2276834)). Qed.
Lemma lem2276836 : True = term410.
Proof. exact (SYM (@lem2276835)). Qed.
Lemma lem2276837 : term410.
Proof. exact (EQ_MP (@lem2276836) (@lem0)). Qed.
Lemma lem2276838 : term414.
Proof. exact (@lem2276827 (@lem2276837)). Qed.
Lemma lem2276840 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276841 : term410 = term411.
Proof. exact (@lem2276840 (NUMERAL 0) term400). Qed.
Lemma lem2276842 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276843 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276844 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276843 h1) (fun h1 : term411 = True => @lem2276842)). Qed.
Lemma lem2276845 : term411 = True.
Proof. exact (EQ_MP (@lem2276844) (@lem2276842)). Qed.
Lemma lem2276846 : term410 = True.
Proof. exact (TRANS (@lem2276841) (@lem2276845)). Qed.
Lemma lem2276847 : True = term410.
Proof. exact (SYM (@lem2276846)). Qed.
Lemma lem2276848 : term410.
Proof. exact (EQ_MP (@lem2276847) (@lem0)). Qed.
Lemma lem2276849 : term415.
Proof. exact (@lem2276838 (@lem2276848)). Qed.
Lemma lem2276851 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276852 : term418 = term419.
Proof. exact (@lem2276851 term400 term400). Qed.
Lemma lem2276853 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276854 : term421 = term400.
Proof. exact (EQ_MP (@lem2276853) (@lem940073)). Qed.
Lemma lem2276855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276856 : term419 = term398.
Proof. exact (MK_COMB (@lem2276855) (@lem2276854)). Qed.
Lemma lem2276857 : term418 = term398.
Proof. exact (TRANS (@lem2276852) (@lem2276856)). Qed.
Lemma lem2276859 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2276860 : term424 = term425.
Proof. exact (@lem2276859 term400 term400). Qed.
Lemma lem2276861 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276862 : term421 = term400.
Proof. exact (EQ_MP (@lem2276861) (@lem940073)). Qed.
Lemma lem2276863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276864 : term419 = term398.
Proof. exact (MK_COMB (@lem2276863) (@lem2276862)). Qed.
Lemma lem2276865 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2276866 : term425 = term396.
Proof. exact (MK_COMB (@lem2276865) (@lem2276864)). Qed.
Lemma lem2276867 : term424 = term396.
Proof. exact (TRANS (@lem2276860) (@lem2276866)). Qed.
Lemma lem2276868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276869 : term426 = term403.
Proof. exact (MK_COMB (@lem2276868) (@lem2276867)). Qed.
Lemma lem2276870 : term427 = term405.
Proof. exact (MK_COMB (@lem2276869) (@lem2276857)). Qed.
Lemma lem2276872 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2276873 : term405 = term408.
Proof. exact (@lem2276872 term400). Qed.
Lemma lem2276874 : term427 = term408.
Proof. exact (TRANS (@lem2276870) (@lem2276873)). Qed.
Lemma lem2276875 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276876 : term429 = term430.
Proof. exact (MK_COMB (@lem2276875) (@lem2276874)). Qed.
Lemma lem2276877 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2276878 : term431 = term432.
Proof. exact (MK_COMB (@lem2276876) (@lem2276877)). Qed.
Lemma lem2276880 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276881 : term432 = term408.
Proof. exact (@lem2276880 term400). Qed.
Lemma lem2276882 : term431 = term408.
Proof. exact (TRANS (@lem2276878) (@lem2276881)). Qed.
Lemma lem2276884 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276885 : term418 = term419.
Proof. exact (@lem2276884 term400 term400). Qed.
Lemma lem2276886 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276887 : term421 = term400.
Proof. exact (EQ_MP (@lem2276886) (@lem940073)). Qed.
Lemma lem2276888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276889 : term419 = term398.
Proof. exact (MK_COMB (@lem2276888) (@lem2276887)). Qed.
Lemma lem2276890 : term418 = term398.
Proof. exact (TRANS (@lem2276885) (@lem2276889)). Qed.
Lemma lem2276891 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2276892 : term434 = term432.
Proof. exact (MK_COMB (@lem2276891) (@lem2276890)). Qed.
Lemma lem2276894 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2276895 : term432 = term408.
Proof. exact (@lem2276894 term400). Qed.
Lemma lem2276896 : term434 = term408.
Proof. exact (TRANS (@lem2276892) (@lem2276895)). Qed.
Lemma lem2276897 : term408 = term434.
Proof. exact (SYM (@lem2276896)). Qed.
Lemma lem2276898 : term431 = term434.
Proof. exact (TRANS (@lem2276882) (@lem2276897)). Qed.
Lemma lem2276899 : term406 = term435.
Proof. exact (@lem2276849 (@lem2276898)). Qed.
Lemma lem2276900 : term405 = term435.
Proof. exact (TRANS (@lem2276815) (@lem2276899)). Qed.
Lemma lem2276902 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2276903 : term435 = term408.
Proof. exact (@lem2276902 term408). Qed.
Lemma lem2276904 : term405 = term408.
Proof. exact (TRANS (@lem2276900) (@lem2276903)). Qed.
Lemma lem2276905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276906 : term437 = term430.
Proof. exact (MK_COMB (@lem2276905) (@lem2276904)). Qed.
Lemma lem2276907 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2276908 (n : nat) : (term395 n) = (term433 n).
Proof. exact (MK_COMB (@lem2276906) (@lem2276907 n)). Qed.
Lemma lem2276909 (n : nat) : (term394 n) = (term433 n).
Proof. exact (TRANS (@lem2276806 n) (@lem2276908 n)). Qed.
Lemma lem2276910 (n : nat) : (term433 n) = term408.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2276911 (n : nat) : (term394 n) = term408.
Proof. exact (TRANS (@lem2276909 n) (@lem2276910 n)). Qed.
Lemma lem2276912 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2276913 (n : nat) (d : nat) : (term565 d n) = (term566 d).
Proof. exact (MK_COMB (@lem2276912 d) (@lem2276911 n)). Qed.
Lemma lem2276914 (n : nat) (d : nat) : (term564 d n) = (term566 d).
Proof. exact (TRANS (@lem2276805 d n) (@lem2276913 n d)). Qed.
Lemma lem2276915 (d : nat) : (term566 d) = (real_of_num d).
Proof. exact (@lem1982723 (real_of_num d)). Qed.
Lemma lem2276916 (n : nat) (d : nat) : (term564 d n) = (real_of_num d).
Proof. exact (TRANS (@lem2276914 n d) (@lem2276915 d)). Qed.
Lemma lem2276917 (n : nat) (d : nat) : (term252 d n) = (real_of_num d).
Proof. exact (TRANS (@lem2276804 d n) (@lem2276916 n d)). Qed.
Lemma lem2276918 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2276919 (n : nat) (d : nat) : (term567 d n) = (term568 d).
Proof. exact (MK_COMB (@lem2276918) (@lem2276917 n d)). Qed.
Lemma lem2276920 (n : nat) (d : nat) : (term580 n d) = (term581 d).
Proof. exact (MK_COMB (@lem2276919 n d) (@lem2276787 d)). Qed.
Lemma lem2276921 (d : nat) : (term581 d) = (term582 d).
Proof. exact (@lem1982792 (real_of_num d) (term389 d)). Qed.
Lemma lem2276922 (d : nat) : (term508 d) = (term509 d).
Proof. exact (@lem1982749 term396 term396 (real_of_num d)). Qed.
Lemma lem2276924 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276925 : term396 = term402.
Proof. exact (@lem2276924 term400). Qed.
Lemma lem2276927 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2276928 : term396 = term402.
Proof. exact (@lem2276927 term400). Qed.
Lemma lem2276929 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276930 : term476 = term477.
Proof. exact (MK_COMB (@lem2276929) (@lem2276928)). Qed.
Lemma lem2276931 : term510 = term511.
Proof. exact (MK_COMB (@lem2276930) (@lem2276925)). Qed.
Lemma lem2276932 : term511 = term512.
Proof. exact (@lem1981613 term396 term396 term398 term398). Qed.
Lemma lem2276934 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2276935 : term418 = term419.
Proof. exact (@lem2276934 term400 term400). Qed.
Lemma lem2276936 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276937 : term421 = term400.
Proof. exact (EQ_MP (@lem2276936) (@lem940073)). Qed.
Lemma lem2276938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276939 : term419 = term398.
Proof. exact (MK_COMB (@lem2276938) (@lem2276937)). Qed.
Lemma lem2276940 : term418 = term398.
Proof. exact (TRANS (@lem2276935) (@lem2276939)). Qed.
Lemma lem2276942 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2276943 : term510 = term419.
Proof. exact (@lem2276942 term400 term400). Qed.
Lemma lem2276944 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2276945 : term421 = term400.
Proof. exact (EQ_MP (@lem2276944) (@lem940073)). Qed.
Lemma lem2276946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2276947 : term419 = term398.
Proof. exact (MK_COMB (@lem2276946) (@lem2276945)). Qed.
Lemma lem2276948 : term510 = term398.
Proof. exact (TRANS (@lem2276943) (@lem2276947)). Qed.
Lemma lem2276949 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2276950 : term513 = term514.
Proof. exact (MK_COMB (@lem2276949) (@lem2276948)). Qed.
Lemma lem2276951 : term512 = term399.
Proof. exact (MK_COMB (@lem2276950) (@lem2276940)). Qed.
Lemma lem2276952 : term511 = term399.
Proof. exact (TRANS (@lem2276932) (@lem2276951)). Qed.
Lemma lem2276953 : term510 = term399.
Proof. exact (TRANS (@lem2276931) (@lem2276952)). Qed.
Lemma lem2276955 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2276956 : term399 = term398.
Proof. exact (@lem2276955 term398). Qed.
Lemma lem2276957 : term510 = term398.
Proof. exact (TRANS (@lem2276953) (@lem2276956)). Qed.
Lemma lem2276958 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2276959 : term515 = term516.
Proof. exact (MK_COMB (@lem2276958) (@lem2276957)). Qed.
Lemma lem2276960 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2276961 (d : nat) : (term509 d) = (term517 d).
Proof. exact (MK_COMB (@lem2276959) (@lem2276960 d)). Qed.
Lemma lem2276962 (d : nat) : (term508 d) = (term517 d).
Proof. exact (TRANS (@lem2276922 d) (@lem2276961 d)). Qed.
Lemma lem2276963 (d : nat) : (term517 d) = (real_of_num d).
Proof. exact (@lem1982709 (real_of_num d)). Qed.
Lemma lem2276964 (d : nat) : (term508 d) = (real_of_num d).
Proof. exact (TRANS (@lem2276962 d) (@lem2276963 d)). Qed.
Lemma lem2276965 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2276966 (d : nat) : (term582 d) = (term583 d).
Proof. exact (MK_COMB (@lem2276965 d) (@lem2276964 d)). Qed.
Lemma lem2276967 (d : nat) : (term583 d) = (term584 d).
Proof. exact (@lem1982717 (real_of_num d)). Qed.
Lemma lem2276969 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276970 : term398 = term399.
Proof. exact (@lem2276969 term400). Qed.
Lemma lem2276972 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2276973 : term398 = term399.
Proof. exact (@lem2276972 term400). Qed.
Lemma lem2276974 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2276975 : term585 = term586.
Proof. exact (MK_COMB (@lem2276974) (@lem2276973)). Qed.
Lemma lem2276976 : term587 = term588.
Proof. exact (MK_COMB (@lem2276975) (@lem2276970)). Qed.
Lemma lem2276977 : term589.
Proof. exact (@lem1981473 term398 term398 term398 term398 term459 term398). Qed.
Lemma lem2276979 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276980 : term410 = term411.
Proof. exact (@lem2276979 (NUMERAL 0) term400). Qed.
Lemma lem2276981 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276982 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276983 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276982 h1) (fun h1 : term411 = True => @lem2276981)). Qed.
Lemma lem2276984 : term411 = True.
Proof. exact (EQ_MP (@lem2276983) (@lem2276981)). Qed.
Lemma lem2276985 : term410 = True.
Proof. exact (TRANS (@lem2276980) (@lem2276984)). Qed.
Lemma lem2276986 : True = term410.
Proof. exact (SYM (@lem2276985)). Qed.
Lemma lem2276987 : term410.
Proof. exact (EQ_MP (@lem2276986) (@lem0)). Qed.
Lemma lem2276988 : term590.
Proof. exact (@lem2276977 (@lem2276987)). Qed.
Lemma lem2276990 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2276991 : term410 = term411.
Proof. exact (@lem2276990 (NUMERAL 0) term400). Qed.
Lemma lem2276992 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2276993 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2276994 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2276993 h1) (fun h1 : term411 = True => @lem2276992)). Qed.
Lemma lem2276995 : term411 = True.
Proof. exact (EQ_MP (@lem2276994) (@lem2276992)). Qed.
Lemma lem2276996 : term410 = True.
Proof. exact (TRANS (@lem2276991) (@lem2276995)). Qed.
Lemma lem2276997 : True = term410.
Proof. exact (SYM (@lem2276996)). Qed.
Lemma lem2276998 : term410.
Proof. exact (EQ_MP (@lem2276997) (@lem0)). Qed.
Lemma lem2276999 : term591.
Proof. exact (@lem2276988 (@lem2276998)). Qed.
Lemma lem2277001 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277002 : term410 = term411.
Proof. exact (@lem2277001 (NUMERAL 0) term400). Qed.
Lemma lem2277003 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277004 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277005 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277004 h1) (fun h1 : term411 = True => @lem2277003)). Qed.
Lemma lem2277006 : term411 = True.
Proof. exact (EQ_MP (@lem2277005) (@lem2277003)). Qed.
Lemma lem2277007 : term410 = True.
Proof. exact (TRANS (@lem2277002) (@lem2277006)). Qed.
Lemma lem2277008 : True = term410.
Proof. exact (SYM (@lem2277007)). Qed.
Lemma lem2277009 : term410.
Proof. exact (EQ_MP (@lem2277008) (@lem0)). Qed.
Lemma lem2277010 : term592.
Proof. exact (@lem2276999 (@lem2277009)). Qed.
Lemma lem2277012 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277013 : term418 = term419.
Proof. exact (@lem2277012 term400 term400). Qed.
Lemma lem2277014 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277015 : term421 = term400.
Proof. exact (EQ_MP (@lem2277014) (@lem940073)). Qed.
Lemma lem2277016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277017 : term419 = term398.
Proof. exact (MK_COMB (@lem2277016) (@lem2277015)). Qed.
Lemma lem2277018 : term418 = term398.
Proof. exact (TRANS (@lem2277013) (@lem2277017)). Qed.
Lemma lem2277020 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277021 : term418 = term419.
Proof. exact (@lem2277020 term400 term400). Qed.
Lemma lem2277022 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277023 : term421 = term400.
Proof. exact (EQ_MP (@lem2277022) (@lem940073)). Qed.
Lemma lem2277024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277025 : term419 = term398.
Proof. exact (MK_COMB (@lem2277024) (@lem2277023)). Qed.
Lemma lem2277026 : term418 = term398.
Proof. exact (TRANS (@lem2277021) (@lem2277025)). Qed.
Lemma lem2277027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277028 : term593 = term585.
Proof. exact (MK_COMB (@lem2277027) (@lem2277026)). Qed.
Lemma lem2277029 : term594 = term587.
Proof. exact (MK_COMB (@lem2277028) (@lem2277018)). Qed.
Lemma lem2277030 : term587 = term458.
Proof. exact (@lem1367770 term400 term400). Qed.
Lemma lem2277031 : term454 = term455.
Proof. exact (@lem706885). Qed.
Lemma lem2277032 : (term454 = term455) = (term456 = term457).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term455). Qed.
Lemma lem2277033 : term456 = term457.
Proof. exact (EQ_MP (@lem2277032) (@lem2277031)). Qed.
Lemma lem2277034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277035 : term458 = term459.
Proof. exact (MK_COMB (@lem2277034) (@lem2277033)). Qed.
Lemma lem2277036 : term587 = term459.
Proof. exact (TRANS (@lem2277030) (@lem2277035)). Qed.
Lemma lem2277037 : term594 = term459.
Proof. exact (TRANS (@lem2277029) (@lem2277036)). Qed.
Lemma lem2277038 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277039 : term595 = term489.
Proof. exact (MK_COMB (@lem2277038) (@lem2277037)). Qed.
Lemma lem2277040 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2277041 : term596 = term597.
Proof. exact (MK_COMB (@lem2277039) (@lem2277040)). Qed.
Lemma lem2277043 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277044 : term597 = term467.
Proof. exact (@lem2277043 term457 term400). Qed.
Lemma lem2277045 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2277046 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2277047 : term466 = term457.
Proof. exact (EQ_MP (@lem2277046) (@lem2277045)). Qed.
Lemma lem2277048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277049 : term467 = term459.
Proof. exact (MK_COMB (@lem2277048) (@lem2277047)). Qed.
Lemma lem2277050 : term597 = term459.
Proof. exact (TRANS (@lem2277044) (@lem2277049)). Qed.
Lemma lem2277051 : term596 = term459.
Proof. exact (TRANS (@lem2277041) (@lem2277050)). Qed.
Lemma lem2277053 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277054 : term418 = term419.
Proof. exact (@lem2277053 term400 term400). Qed.
Lemma lem2277055 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277056 : term421 = term400.
Proof. exact (EQ_MP (@lem2277055) (@lem940073)). Qed.
Lemma lem2277057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277058 : term419 = term398.
Proof. exact (MK_COMB (@lem2277057) (@lem2277056)). Qed.
Lemma lem2277059 : term418 = term398.
Proof. exact (TRANS (@lem2277054) (@lem2277058)). Qed.
Lemma lem2277060 : term489 = term489.
Proof. exact (eq_refl term489). Qed.
Lemma lem2277061 : term598 = term597.
Proof. exact (MK_COMB (@lem2277060) (@lem2277059)). Qed.
Lemma lem2277063 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277064 : term597 = term467.
Proof. exact (@lem2277063 term457 term400). Qed.
Lemma lem2277065 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2277066 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2277067 : term466 = term457.
Proof. exact (EQ_MP (@lem2277066) (@lem2277065)). Qed.
Lemma lem2277068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277069 : term467 = term459.
Proof. exact (MK_COMB (@lem2277068) (@lem2277067)). Qed.
Lemma lem2277070 : term597 = term459.
Proof. exact (TRANS (@lem2277064) (@lem2277069)). Qed.
Lemma lem2277071 : term598 = term459.
Proof. exact (TRANS (@lem2277061) (@lem2277070)). Qed.
Lemma lem2277072 : term459 = term598.
Proof. exact (SYM (@lem2277071)). Qed.
Lemma lem2277073 : term596 = term598.
Proof. exact (TRANS (@lem2277051) (@lem2277072)). Qed.
Lemma lem2277074 : term588 = term487.
Proof. exact (@lem2277010 (@lem2277073)). Qed.
Lemma lem2277075 : term587 = term487.
Proof. exact (TRANS (@lem2276976) (@lem2277074)). Qed.
Lemma lem2277077 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2277078 : term487 = term459.
Proof. exact (@lem2277077 term459). Qed.
Lemma lem2277079 : term587 = term459.
Proof. exact (TRANS (@lem2277075) (@lem2277078)). Qed.
Lemma lem2277080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277081 : term599 = term489.
Proof. exact (MK_COMB (@lem2277080) (@lem2277079)). Qed.
Lemma lem2277082 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2277083 (d : nat) : (term584 d) = (term490 d).
Proof. exact (MK_COMB (@lem2277081) (@lem2277082 d)). Qed.
Lemma lem2277084 (d : nat) : (term583 d) = (term490 d).
Proof. exact (TRANS (@lem2276967 d) (@lem2277083 d)). Qed.
Lemma lem2277085 (d : nat) : (term582 d) = (term490 d).
Proof. exact (TRANS (@lem2276966 d) (@lem2277084 d)). Qed.
Lemma lem2277086 (d : nat) : (term581 d) = (term490 d).
Proof. exact (TRANS (@lem2276921 d) (@lem2277085 d)). Qed.
Lemma lem2277087 (n : nat) (d : nat) : (term580 n d) = (term490 d).
Proof. exact (TRANS (@lem2276920 n d) (@lem2277086 d)). Qed.
Lemma lem2277088 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277089 (n : nat) (d : nat) : (term600 n d) = (term601 d).
Proof. exact (MK_COMB (@lem2277088) (@lem2277087 n d)). Qed.
Lemma lem2277090 (d : nat) : (term601 d) = (term602 d).
Proof. exact (@lem1982785 (term490 d)). Qed.
Lemma lem2277091 (d : nat) : (term602 d) = (term603 d).
Proof. exact (@lem1982749 term396 term459 (real_of_num d)). Qed.
Lemma lem2277093 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277094 : term459 = term487.
Proof. exact (@lem2277093 term457). Qed.
Lemma lem2277096 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277097 : term396 = term402.
Proof. exact (@lem2277096 term400). Qed.
Lemma lem2277098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277099 : term476 = term477.
Proof. exact (MK_COMB (@lem2277098) (@lem2277097)). Qed.
Lemma lem2277100 : term604 = term605.
Proof. exact (MK_COMB (@lem2277099) (@lem2277094)). Qed.
Lemma lem2277101 : term605 = term606.
Proof. exact (@lem1981613 term396 term459 term398 term398). Qed.
Lemma lem2277103 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277104 : term418 = term419.
Proof. exact (@lem2277103 term400 term400). Qed.
Lemma lem2277105 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277106 : term421 = term400.
Proof. exact (EQ_MP (@lem2277105) (@lem940073)). Qed.
Lemma lem2277107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277108 : term419 = term398.
Proof. exact (MK_COMB (@lem2277107) (@lem2277106)). Qed.
Lemma lem2277109 : term418 = term398.
Proof. exact (TRANS (@lem2277104) (@lem2277108)). Qed.
Lemma lem2277111 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2277112 : term604 = term607.
Proof. exact (@lem2277111 term400 term457). Qed.
Lemma lem2277113 : term483 = term455.
Proof. exact (@lem996238 term455). Qed.
Lemma lem2277114 : (term483 = term455) = (term484 = term457).
Proof. exact (@lem1007663 (BIT1 0) term455 term455). Qed.
Lemma lem2277115 : term484 = term457.
Proof. exact (EQ_MP (@lem2277114) (@lem2277113)). Qed.
Lemma lem2277116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277117 : term482 = term459.
Proof. exact (MK_COMB (@lem2277116) (@lem2277115)). Qed.
Lemma lem2277118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277119 : term607 = term448.
Proof. exact (MK_COMB (@lem2277118) (@lem2277117)). Qed.
Lemma lem2277120 : term604 = term448.
Proof. exact (TRANS (@lem2277112) (@lem2277119)). Qed.
Lemma lem2277121 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2277122 : term608 = term609.
Proof. exact (MK_COMB (@lem2277121) (@lem2277120)). Qed.
Lemma lem2277123 : term606 = term469.
Proof. exact (MK_COMB (@lem2277122) (@lem2277109)). Qed.
Lemma lem2277124 : term605 = term469.
Proof. exact (TRANS (@lem2277101) (@lem2277123)). Qed.
Lemma lem2277125 : term604 = term469.
Proof. exact (TRANS (@lem2277100) (@lem2277124)). Qed.
Lemma lem2277127 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2277128 : term469 = term448.
Proof. exact (@lem2277127 term448). Qed.
Lemma lem2277129 : term604 = term448.
Proof. exact (TRANS (@lem2277125) (@lem2277128)). Qed.
Lemma lem2277130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277131 : term610 = term461.
Proof. exact (MK_COMB (@lem2277130) (@lem2277129)). Qed.
Lemma lem2277132 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2277133 (d : nat) : (term603 d) = (term471 d).
Proof. exact (MK_COMB (@lem2277131) (@lem2277132 d)). Qed.
Lemma lem2277134 (d : nat) : (term602 d) = (term471 d).
Proof. exact (TRANS (@lem2277091 d) (@lem2277133 d)). Qed.
Lemma lem2277135 (d : nat) : (term601 d) = (term471 d).
Proof. exact (TRANS (@lem2277090 d) (@lem2277134 d)). Qed.
Lemma lem2277136 (n : nat) (d : nat) : (term611 n d) = (term611 n d).
Proof. exact (eq_refl (term611 n d)). Qed.
Lemma lem2277137 (n : nat) (d : nat) : ((term600 n d) = (term601 d)) = ((term600 n d) = (term471 d)).
Proof. exact (MK_COMB (@lem2277136 n d) (@lem2277135 d)). Qed.
Lemma lem2277138 (n : nat) (d : nat) : (term600 n d) = (term471 d).
Proof. exact (EQ_MP (@lem2277137 n d) (@lem2277089 n d)). Qed.
Lemma lem2277139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2277140 (n : nat) (d : nat) : (term612 n d) = (term497 d).
Proof. exact (MK_COMB (@lem2277139) (@lem2277138 n d)). Qed.
Lemma lem2277141 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2277142 (n : nat) (d : nat) : (term613 n d) = (term499 d).
Proof. exact (MK_COMB (@lem2277140 n d) (@lem2277141)). Qed.
Lemma lem2277143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2277144 (n : nat) (d : nat) : (term614 n d) = (term493 d).
Proof. exact (MK_COMB (@lem2277143) (@lem2277087 n d)). Qed.
Lemma lem2277145 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2277146 (n : nat) (d : nat) : (term615 n d) = (term495 d).
Proof. exact (MK_COMB (@lem2277144 n d) (@lem2277145)). Qed.
Lemma lem2277147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2277148 (n : nat) (d : nat) : (term616 n d) = (term617 d).
Proof. exact (MK_COMB (@lem2277147) (@lem2277146 n d)). Qed.
Lemma lem2277149 (n : nat) (d : nat) : (term579 n d) = (term618 d).
Proof. exact (MK_COMB (@lem2277148 n d) (@lem2277142 n d)). Qed.
Lemma lem2277150 (n : nat) (d : nat) : (term578 n d) = (term618 d).
Proof. exact (TRANS (@lem2276780 n d) (@lem2277149 n d)). Qed.
Lemma lem2277151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2277152 (n : nat) (d : nat) : (term619 n d) = term620.
Proof. exact (MK_COMB (@lem2277151) (@lem2276779 n d)). Qed.
Lemma lem2277153 (n : nat) (d : nat) : (term561 n d) = (term621 d).
Proof. exact (MK_COMB (@lem2277152 n d) (@lem2277150 n d)). Qed.
Lemma lem2277160 (n : nat) (d : nat) : (term560 n d) = (term621 d).
Proof. exact (TRANS (@lem2276482 n d) (@lem2277153 n d)). Qed.
Lemma lem2277174 (d : nat) : (term621 d) = (term622 d).
Proof. exact (@lem19158 (term495 d) term536 (term499 d)). Qed.
Lemma lem2277181 (d : nat) : (term623 d) = (term624 d).
Proof. exact (@lem19367 term531 term531 (term499 d)). Qed.
Lemma lem2277188 (d : nat) : (term625 d) = (term626 d).
Proof. exact (@lem19367 term531 term531 (term495 d)). Qed.
Lemma lem2277189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2277190 (d : nat) : (term627 d) = (term628 d).
Proof. exact (MK_COMB (@lem2277189) (@lem2277188 d)). Qed.
Lemma lem2277191 (d : nat) : (term622 d) = (term629 d).
Proof. exact (MK_COMB (@lem2277190 d) (@lem2277181 d)). Qed.
Lemma lem2277193 (d : nat) : (term621 d) = (term629 d).
Proof. exact (TRANS (@lem2277174 d) (@lem2277191 d)). Qed.
Lemma lem2277194 (n : nat) (d : nat) : (term560 n d) = (term629 d).
Proof. exact (TRANS (@lem2277160 n d) (@lem2277193 d)). Qed.
Lemma lem2277216 (d : nat) (h1 : term629 d) : term629 d.
Proof. exact (h1). Qed.
Lemma lem2277217 (d : nat) (h1 : term626 d) : term626 d.
Proof. exact (h1). Qed.
Lemma lem2277218 (d : nat) (h1 : term630 d) : term630 d.
Proof. exact (h1). Qed.
Lemma lem2277220 (d : nat) (h1 : term630 d) : term531.
Proof. exact (proj1 (@lem2277218 d h1)). Qed.
Lemma lem2277223 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2277224 : term531 = term547.
Proof. exact (@lem2277223 term408 term408). Qed.
Lemma lem2277226 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277227 : term408 = term435.
Proof. exact (@lem2277226 (NUMERAL 0)). Qed.
Lemma lem2277229 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277230 : term408 = term435.
Proof. exact (@lem2277229 (NUMERAL 0)). Qed.
Lemma lem2277231 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277232 : term548 = term549.
Proof. exact (MK_COMB (@lem2277231) (@lem2277230)). Qed.
Lemma lem2277233 : term547 = term550.
Proof. exact (MK_COMB (@lem2277232) (@lem2277227)). Qed.
Lemma lem2277234 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2277236 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277237 : term410 = term411.
Proof. exact (@lem2277236 (NUMERAL 0) term400). Qed.
Lemma lem2277238 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277239 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277240 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277239 h1) (fun h1 : term411 = True => @lem2277238)). Qed.
Lemma lem2277241 : term411 = True.
Proof. exact (EQ_MP (@lem2277240) (@lem2277238)). Qed.
Lemma lem2277242 : term410 = True.
Proof. exact (TRANS (@lem2277237) (@lem2277241)). Qed.
Lemma lem2277243 : True = term410.
Proof. exact (SYM (@lem2277242)). Qed.
Lemma lem2277244 : term410.
Proof. exact (EQ_MP (@lem2277243) (@lem0)). Qed.
Lemma lem2277245 : term552.
Proof. exact (@lem2277234 (@lem2277244)). Qed.
Lemma lem2277247 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277248 : term410 = term411.
Proof. exact (@lem2277247 (NUMERAL 0) term400). Qed.
Lemma lem2277249 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277250 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277251 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277250 h1) (fun h1 : term411 = True => @lem2277249)). Qed.
Lemma lem2277252 : term411 = True.
Proof. exact (EQ_MP (@lem2277251) (@lem2277249)). Qed.
Lemma lem2277253 : term410 = True.
Proof. exact (TRANS (@lem2277248) (@lem2277252)). Qed.
Lemma lem2277254 : True = term410.
Proof. exact (SYM (@lem2277253)). Qed.
Lemma lem2277255 : term410.
Proof. exact (EQ_MP (@lem2277254) (@lem0)). Qed.
Lemma lem2277256 : term550 = term553.
Proof. exact (@lem2277245 (@lem2277255)). Qed.
Lemma lem2277258 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277259 : term432 = term408.
Proof. exact (@lem2277258 term400). Qed.
Lemma lem2277261 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277262 : term432 = term408.
Proof. exact (@lem2277261 term400). Qed.
Lemma lem2277263 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277264 : term554 = term548.
Proof. exact (MK_COMB (@lem2277263) (@lem2277262)). Qed.
Lemma lem2277265 : term553 = term547.
Proof. exact (MK_COMB (@lem2277264) (@lem2277259)). Qed.
Lemma lem2277267 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277268 : term547 = term555.
Proof. exact (@lem2277267 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2277269 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2277270 : term547 = False.
Proof. exact (TRANS (@lem2277268) (@lem2277269)). Qed.
Lemma lem2277271 : term553 = False.
Proof. exact (TRANS (@lem2277265) (@lem2277270)). Qed.
Lemma lem2277272 : term550 = False.
Proof. exact (TRANS (@lem2277256) (@lem2277271)). Qed.
Lemma lem2277273 : term547 = False.
Proof. exact (TRANS (@lem2277233) (@lem2277272)). Qed.
Lemma lem2277274 : term531 = False.
Proof. exact (TRANS (@lem2277224) (@lem2277273)). Qed.
Lemma lem2277275 (d : nat) (h1 : term630 d) : False.
Proof. exact (EQ_MP (@lem2277274) (@lem2277220 d h1)). Qed.
Lemma lem2277276 (d : nat) (h1 : term630 d) : term630 d.
Proof. exact (h1). Qed.
Lemma lem2277278 (d : nat) (h1 : term630 d) : term531.
Proof. exact (proj1 (@lem2277276 d h1)). Qed.
Lemma lem2277281 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2277282 : term531 = term547.
Proof. exact (@lem2277281 term408 term408). Qed.
Lemma lem2277284 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277285 : term408 = term435.
Proof. exact (@lem2277284 (NUMERAL 0)). Qed.
Lemma lem2277287 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277288 : term408 = term435.
Proof. exact (@lem2277287 (NUMERAL 0)). Qed.
Lemma lem2277289 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277290 : term548 = term549.
Proof. exact (MK_COMB (@lem2277289) (@lem2277288)). Qed.
Lemma lem2277291 : term547 = term550.
Proof. exact (MK_COMB (@lem2277290) (@lem2277285)). Qed.
Lemma lem2277292 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2277294 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277295 : term410 = term411.
Proof. exact (@lem2277294 (NUMERAL 0) term400). Qed.
Lemma lem2277296 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277297 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277298 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277297 h1) (fun h1 : term411 = True => @lem2277296)). Qed.
Lemma lem2277299 : term411 = True.
Proof. exact (EQ_MP (@lem2277298) (@lem2277296)). Qed.
Lemma lem2277300 : term410 = True.
Proof. exact (TRANS (@lem2277295) (@lem2277299)). Qed.
Lemma lem2277301 : True = term410.
Proof. exact (SYM (@lem2277300)). Qed.
Lemma lem2277302 : term410.
Proof. exact (EQ_MP (@lem2277301) (@lem0)). Qed.
Lemma lem2277303 : term552.
Proof. exact (@lem2277292 (@lem2277302)). Qed.
Lemma lem2277305 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277306 : term410 = term411.
Proof. exact (@lem2277305 (NUMERAL 0) term400). Qed.
Lemma lem2277307 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277308 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277309 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277308 h1) (fun h1 : term411 = True => @lem2277307)). Qed.
Lemma lem2277310 : term411 = True.
Proof. exact (EQ_MP (@lem2277309) (@lem2277307)). Qed.
Lemma lem2277311 : term410 = True.
Proof. exact (TRANS (@lem2277306) (@lem2277310)). Qed.
Lemma lem2277312 : True = term410.
Proof. exact (SYM (@lem2277311)). Qed.
Lemma lem2277313 : term410.
Proof. exact (EQ_MP (@lem2277312) (@lem0)). Qed.
Lemma lem2277314 : term550 = term553.
Proof. exact (@lem2277303 (@lem2277313)). Qed.
Lemma lem2277316 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277317 : term432 = term408.
Proof. exact (@lem2277316 term400). Qed.
Lemma lem2277319 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277320 : term432 = term408.
Proof. exact (@lem2277319 term400). Qed.
Lemma lem2277321 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277322 : term554 = term548.
Proof. exact (MK_COMB (@lem2277321) (@lem2277320)). Qed.
Lemma lem2277323 : term553 = term547.
Proof. exact (MK_COMB (@lem2277322) (@lem2277317)). Qed.
Lemma lem2277325 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277326 : term547 = term555.
Proof. exact (@lem2277325 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2277327 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2277328 : term547 = False.
Proof. exact (TRANS (@lem2277326) (@lem2277327)). Qed.
Lemma lem2277329 : term553 = False.
Proof. exact (TRANS (@lem2277323) (@lem2277328)). Qed.
Lemma lem2277330 : term550 = False.
Proof. exact (TRANS (@lem2277314) (@lem2277329)). Qed.
Lemma lem2277331 : term547 = False.
Proof. exact (TRANS (@lem2277291) (@lem2277330)). Qed.
Lemma lem2277332 : term531 = False.
Proof. exact (TRANS (@lem2277282) (@lem2277331)). Qed.
Lemma lem2277333 (d : nat) (h1 : term630 d) : False.
Proof. exact (EQ_MP (@lem2277332) (@lem2277278 d h1)). Qed.
Lemma lem2277334 (d : nat) (h1 : term626 d) : False.
Proof. exact (or_elim (@lem2277217 d h1) (fun h0 : term630 d => @lem2277275 d h0) (fun h0 : term630 d => @lem2277333 d h0)). Qed.
Lemma lem2277335 (d : nat) (h1 : term624 d) : term624 d.
Proof. exact (h1). Qed.
Lemma lem2277336 (d : nat) (h1 : term631 d) : term631 d.
Proof. exact (h1). Qed.
Lemma lem2277338 (d : nat) (h1 : term631 d) : term531.
Proof. exact (proj1 (@lem2277336 d h1)). Qed.
Lemma lem2277341 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2277342 : term531 = term547.
Proof. exact (@lem2277341 term408 term408). Qed.
Lemma lem2277344 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277345 : term408 = term435.
Proof. exact (@lem2277344 (NUMERAL 0)). Qed.
Lemma lem2277347 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277348 : term408 = term435.
Proof. exact (@lem2277347 (NUMERAL 0)). Qed.
Lemma lem2277349 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277350 : term548 = term549.
Proof. exact (MK_COMB (@lem2277349) (@lem2277348)). Qed.
Lemma lem2277351 : term547 = term550.
Proof. exact (MK_COMB (@lem2277350) (@lem2277345)). Qed.
Lemma lem2277352 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2277354 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277355 : term410 = term411.
Proof. exact (@lem2277354 (NUMERAL 0) term400). Qed.
Lemma lem2277356 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277357 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277358 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277357 h1) (fun h1 : term411 = True => @lem2277356)). Qed.
Lemma lem2277359 : term411 = True.
Proof. exact (EQ_MP (@lem2277358) (@lem2277356)). Qed.
Lemma lem2277360 : term410 = True.
Proof. exact (TRANS (@lem2277355) (@lem2277359)). Qed.
Lemma lem2277361 : True = term410.
Proof. exact (SYM (@lem2277360)). Qed.
Lemma lem2277362 : term410.
Proof. exact (EQ_MP (@lem2277361) (@lem0)). Qed.
Lemma lem2277363 : term552.
Proof. exact (@lem2277352 (@lem2277362)). Qed.
Lemma lem2277365 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277366 : term410 = term411.
Proof. exact (@lem2277365 (NUMERAL 0) term400). Qed.
Lemma lem2277367 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277368 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277369 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277368 h1) (fun h1 : term411 = True => @lem2277367)). Qed.
Lemma lem2277370 : term411 = True.
Proof. exact (EQ_MP (@lem2277369) (@lem2277367)). Qed.
Lemma lem2277371 : term410 = True.
Proof. exact (TRANS (@lem2277366) (@lem2277370)). Qed.
Lemma lem2277372 : True = term410.
Proof. exact (SYM (@lem2277371)). Qed.
Lemma lem2277373 : term410.
Proof. exact (EQ_MP (@lem2277372) (@lem0)). Qed.
Lemma lem2277374 : term550 = term553.
Proof. exact (@lem2277363 (@lem2277373)). Qed.
Lemma lem2277376 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277377 : term432 = term408.
Proof. exact (@lem2277376 term400). Qed.
Lemma lem2277379 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277380 : term432 = term408.
Proof. exact (@lem2277379 term400). Qed.
Lemma lem2277381 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277382 : term554 = term548.
Proof. exact (MK_COMB (@lem2277381) (@lem2277380)). Qed.
Lemma lem2277383 : term553 = term547.
Proof. exact (MK_COMB (@lem2277382) (@lem2277377)). Qed.
Lemma lem2277385 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277386 : term547 = term555.
Proof. exact (@lem2277385 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2277387 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2277388 : term547 = False.
Proof. exact (TRANS (@lem2277386) (@lem2277387)). Qed.
Lemma lem2277389 : term553 = False.
Proof. exact (TRANS (@lem2277383) (@lem2277388)). Qed.
Lemma lem2277390 : term550 = False.
Proof. exact (TRANS (@lem2277374) (@lem2277389)). Qed.
Lemma lem2277391 : term547 = False.
Proof. exact (TRANS (@lem2277351) (@lem2277390)). Qed.
Lemma lem2277392 : term531 = False.
Proof. exact (TRANS (@lem2277342) (@lem2277391)). Qed.
Lemma lem2277393 (d : nat) (h1 : term631 d) : False.
Proof. exact (EQ_MP (@lem2277392) (@lem2277338 d h1)). Qed.
Lemma lem2277394 (d : nat) (h1 : term631 d) : term631 d.
Proof. exact (h1). Qed.
Lemma lem2277396 (d : nat) (h1 : term631 d) : term531.
Proof. exact (proj1 (@lem2277394 d h1)). Qed.
Lemma lem2277399 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2277400 : term531 = term547.
Proof. exact (@lem2277399 term408 term408). Qed.
Lemma lem2277402 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277403 : term408 = term435.
Proof. exact (@lem2277402 (NUMERAL 0)). Qed.
Lemma lem2277405 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277406 : term408 = term435.
Proof. exact (@lem2277405 (NUMERAL 0)). Qed.
Lemma lem2277407 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277408 : term548 = term549.
Proof. exact (MK_COMB (@lem2277407) (@lem2277406)). Qed.
Lemma lem2277409 : term547 = term550.
Proof. exact (MK_COMB (@lem2277408) (@lem2277403)). Qed.
Lemma lem2277410 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2277412 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277413 : term410 = term411.
Proof. exact (@lem2277412 (NUMERAL 0) term400). Qed.
Lemma lem2277414 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277415 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277416 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277415 h1) (fun h1 : term411 = True => @lem2277414)). Qed.
Lemma lem2277417 : term411 = True.
Proof. exact (EQ_MP (@lem2277416) (@lem2277414)). Qed.
Lemma lem2277418 : term410 = True.
Proof. exact (TRANS (@lem2277413) (@lem2277417)). Qed.
Lemma lem2277419 : True = term410.
Proof. exact (SYM (@lem2277418)). Qed.
Lemma lem2277420 : term410.
Proof. exact (EQ_MP (@lem2277419) (@lem0)). Qed.
Lemma lem2277421 : term552.
Proof. exact (@lem2277410 (@lem2277420)). Qed.
Lemma lem2277423 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277424 : term410 = term411.
Proof. exact (@lem2277423 (NUMERAL 0) term400). Qed.
Lemma lem2277425 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277426 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277427 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277426 h1) (fun h1 : term411 = True => @lem2277425)). Qed.
Lemma lem2277428 : term411 = True.
Proof. exact (EQ_MP (@lem2277427) (@lem2277425)). Qed.
Lemma lem2277429 : term410 = True.
Proof. exact (TRANS (@lem2277424) (@lem2277428)). Qed.
Lemma lem2277430 : True = term410.
Proof. exact (SYM (@lem2277429)). Qed.
Lemma lem2277431 : term410.
Proof. exact (EQ_MP (@lem2277430) (@lem0)). Qed.
Lemma lem2277432 : term550 = term553.
Proof. exact (@lem2277421 (@lem2277431)). Qed.
Lemma lem2277434 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277435 : term432 = term408.
Proof. exact (@lem2277434 term400). Qed.
Lemma lem2277437 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277438 : term432 = term408.
Proof. exact (@lem2277437 term400). Qed.
Lemma lem2277439 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2277440 : term554 = term548.
Proof. exact (MK_COMB (@lem2277439) (@lem2277438)). Qed.
Lemma lem2277441 : term553 = term547.
Proof. exact (MK_COMB (@lem2277440) (@lem2277435)). Qed.
Lemma lem2277443 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277444 : term547 = term555.
Proof. exact (@lem2277443 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2277445 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2277446 : term547 = False.
Proof. exact (TRANS (@lem2277444) (@lem2277445)). Qed.
Lemma lem2277447 : term553 = False.
Proof. exact (TRANS (@lem2277441) (@lem2277446)). Qed.
Lemma lem2277448 : term550 = False.
Proof. exact (TRANS (@lem2277432) (@lem2277447)). Qed.
Lemma lem2277449 : term547 = False.
Proof. exact (TRANS (@lem2277409) (@lem2277448)). Qed.
Lemma lem2277450 : term531 = False.
Proof. exact (TRANS (@lem2277400) (@lem2277449)). Qed.
Lemma lem2277451 (d : nat) (h1 : term631 d) : False.
Proof. exact (EQ_MP (@lem2277450) (@lem2277396 d h1)). Qed.
Lemma lem2277452 (d : nat) (h1 : term624 d) : False.
Proof. exact (or_elim (@lem2277335 d h1) (fun h0 : term631 d => @lem2277393 d h0) (fun h0 : term631 d => @lem2277451 d h0)). Qed.
Lemma lem2277453 (d : nat) (h1 : term629 d) : False.
Proof. exact (or_elim (@lem2277216 d h1) (fun h0 : term626 d => @lem2277334 d h0) (fun h0 : term624 d => @lem2277452 d h0)). Qed.
Lemma lem2277455 (d : nat) (h1 : term629 d) : term629 d.
Proof. exact (h1). Qed.
Lemma lem2277456 (d : nat) (h1 : term629 d) : (term629 d) = False.
Proof. exact (prop_ext (fun h2 : term629 d => @lem2277453 d h1) (fun h2 : False => @lem2277455 d h1)). Qed.
Lemma lem2277457 (d : nat) (h1 : term629 d) : False.
Proof. exact (EQ_MP (@lem2277456 d h1) (@lem2277455 d h1)). Qed.
Lemma lem2277458 (n : nat) (d : nat) (h1 : term560 n d) : term560 n d.
Proof. exact (h1). Qed.
Lemma lem2277459 (n : nat) (d : nat) (h1 : term560 n d) : term629 d.
Proof. exact (EQ_MP (@lem2277194 n d) (@lem2277458 n d h1)). Qed.
Lemma lem2277460 (n : nat) (d : nat) (h1 : term560 n d) : (term629 d) = False.
Proof. exact (prop_ext (fun h2 : term629 d => @lem2277457 d h2) (fun h2 : False => @lem2277459 n d h1)). Qed.
Lemma lem2277461 (n : nat) (d : nat) (h1 : term560 n d) : False.
Proof. exact (EQ_MP (@lem2277460 n d h1) (@lem2277459 n d h1)). Qed.
Lemma lem2277462 (n : nat) (d : nat) : term632 n d.
Proof. exact (fun h0 : term560 n d => @lem2277461 n d h0). Qed.
Lemma lem2277463 (n : nat) (d : nat) : term633 n d.
Proof. exact (@lem1386578 (term634 n d)). Qed.
Lemma lem2277466 (n : nat) (d : nat) : term634 n d.
Proof. exact (@lem2277463 n d (@lem2277462 n d)). Qed.
Lemma lem2277467 (d : nat) (n : nat) : term258 d n.
Proof. exact (ex_intro (term257 d n) d (@lem2277466 n d)). Qed.
Lemma lem2277491 (m : nat) (d : nat) : (term635 m d) = (term636 m d).
Proof. exact (@lem17160 ((term283 m d) = (real_of_num d)) ((term283 m d) = (term93 d))). Qed.
Lemma lem2277492 (m : nat) (d : nat) : (term637 m d) = (term638 m d).
Proof. exact (@lem1988318 (term283 m d) (real_of_num d)). Qed.
Lemma lem2277493 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2277500 (d : nat) (m : nat) : (term25 m d) = (term25 d m).
Proof. exact (@lem1982761 (real_of_num d) (real_of_num m)). Qed.
Lemma lem2277507 (m : nat) : (term93 m) = (term389 m).
Proof. exact (@lem1982785 (real_of_num m)). Qed.
Lemma lem2277508 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277509 (m : nat) : (term127 m) = (term390 m).
Proof. exact (MK_COMB (@lem2277508) (@lem2277507 m)). Qed.
Lemma lem2277510 (d : nat) (m : nat) : (term283 m d) = (term639 d m).
Proof. exact (MK_COMB (@lem2277509 m) (@lem2277500 d m)). Qed.
Lemma lem2277511 (d : nat) (m : nat) : (term639 d m) = (term640 d m).
Proof. exact (@lem1982757 (real_of_num d) (term389 m) (real_of_num m)). Qed.
Lemma lem2277512 (m : nat) : (term518 m) = (term395 m).
Proof. exact (@lem1982713 term396 (real_of_num m)). Qed.
Lemma lem2277514 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277515 : term398 = term399.
Proof. exact (@lem2277514 term400). Qed.
Lemma lem2277517 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277518 : term396 = term402.
Proof. exact (@lem2277517 term400). Qed.
Lemma lem2277519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277520 : term403 = term404.
Proof. exact (MK_COMB (@lem2277519) (@lem2277518)). Qed.
Lemma lem2277521 : term405 = term406.
Proof. exact (MK_COMB (@lem2277520) (@lem2277515)). Qed.
Lemma lem2277522 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2277524 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277525 : term410 = term411.
Proof. exact (@lem2277524 (NUMERAL 0) term400). Qed.
Lemma lem2277526 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277527 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277528 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277527 h1) (fun h1 : term411 = True => @lem2277526)). Qed.
Lemma lem2277529 : term411 = True.
Proof. exact (EQ_MP (@lem2277528) (@lem2277526)). Qed.
Lemma lem2277530 : term410 = True.
Proof. exact (TRANS (@lem2277525) (@lem2277529)). Qed.
Lemma lem2277531 : True = term410.
Proof. exact (SYM (@lem2277530)). Qed.
Lemma lem2277532 : term410.
Proof. exact (EQ_MP (@lem2277531) (@lem0)). Qed.
Lemma lem2277533 : term413.
Proof. exact (@lem2277522 (@lem2277532)). Qed.
Lemma lem2277535 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277536 : term410 = term411.
Proof. exact (@lem2277535 (NUMERAL 0) term400). Qed.
Lemma lem2277537 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277538 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277539 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277538 h1) (fun h1 : term411 = True => @lem2277537)). Qed.
Lemma lem2277540 : term411 = True.
Proof. exact (EQ_MP (@lem2277539) (@lem2277537)). Qed.
Lemma lem2277541 : term410 = True.
Proof. exact (TRANS (@lem2277536) (@lem2277540)). Qed.
Lemma lem2277542 : True = term410.
Proof. exact (SYM (@lem2277541)). Qed.
Lemma lem2277543 : term410.
Proof. exact (EQ_MP (@lem2277542) (@lem0)). Qed.
Lemma lem2277544 : term414.
Proof. exact (@lem2277533 (@lem2277543)). Qed.
Lemma lem2277546 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277547 : term410 = term411.
Proof. exact (@lem2277546 (NUMERAL 0) term400). Qed.
Lemma lem2277548 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277549 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277550 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277549 h1) (fun h1 : term411 = True => @lem2277548)). Qed.
Lemma lem2277551 : term411 = True.
Proof. exact (EQ_MP (@lem2277550) (@lem2277548)). Qed.
Lemma lem2277552 : term410 = True.
Proof. exact (TRANS (@lem2277547) (@lem2277551)). Qed.
Lemma lem2277553 : True = term410.
Proof. exact (SYM (@lem2277552)). Qed.
Lemma lem2277554 : term410.
Proof. exact (EQ_MP (@lem2277553) (@lem0)). Qed.
Lemma lem2277555 : term415.
Proof. exact (@lem2277544 (@lem2277554)). Qed.
Lemma lem2277557 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277558 : term418 = term419.
Proof. exact (@lem2277557 term400 term400). Qed.
Lemma lem2277559 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277560 : term421 = term400.
Proof. exact (EQ_MP (@lem2277559) (@lem940073)). Qed.
Lemma lem2277561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277562 : term419 = term398.
Proof. exact (MK_COMB (@lem2277561) (@lem2277560)). Qed.
Lemma lem2277563 : term418 = term398.
Proof. exact (TRANS (@lem2277558) (@lem2277562)). Qed.
Lemma lem2277565 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2277566 : term424 = term425.
Proof. exact (@lem2277565 term400 term400). Qed.
Lemma lem2277567 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277568 : term421 = term400.
Proof. exact (EQ_MP (@lem2277567) (@lem940073)). Qed.
Lemma lem2277569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277570 : term419 = term398.
Proof. exact (MK_COMB (@lem2277569) (@lem2277568)). Qed.
Lemma lem2277571 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277572 : term425 = term396.
Proof. exact (MK_COMB (@lem2277571) (@lem2277570)). Qed.
Lemma lem2277573 : term424 = term396.
Proof. exact (TRANS (@lem2277566) (@lem2277572)). Qed.
Lemma lem2277574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277575 : term426 = term403.
Proof. exact (MK_COMB (@lem2277574) (@lem2277573)). Qed.
Lemma lem2277576 : term427 = term405.
Proof. exact (MK_COMB (@lem2277575) (@lem2277563)). Qed.
Lemma lem2277578 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2277579 : term405 = term408.
Proof. exact (@lem2277578 term400). Qed.
Lemma lem2277580 : term427 = term408.
Proof. exact (TRANS (@lem2277576) (@lem2277579)). Qed.
Lemma lem2277581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277582 : term429 = term430.
Proof. exact (MK_COMB (@lem2277581) (@lem2277580)). Qed.
Lemma lem2277583 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2277584 : term431 = term432.
Proof. exact (MK_COMB (@lem2277582) (@lem2277583)). Qed.
Lemma lem2277586 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277587 : term432 = term408.
Proof. exact (@lem2277586 term400). Qed.
Lemma lem2277588 : term431 = term408.
Proof. exact (TRANS (@lem2277584) (@lem2277587)). Qed.
Lemma lem2277590 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277591 : term418 = term419.
Proof. exact (@lem2277590 term400 term400). Qed.
Lemma lem2277592 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277593 : term421 = term400.
Proof. exact (EQ_MP (@lem2277592) (@lem940073)). Qed.
Lemma lem2277594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277595 : term419 = term398.
Proof. exact (MK_COMB (@lem2277594) (@lem2277593)). Qed.
Lemma lem2277596 : term418 = term398.
Proof. exact (TRANS (@lem2277591) (@lem2277595)). Qed.
Lemma lem2277597 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2277598 : term434 = term432.
Proof. exact (MK_COMB (@lem2277597) (@lem2277596)). Qed.
Lemma lem2277600 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277601 : term432 = term408.
Proof. exact (@lem2277600 term400). Qed.
Lemma lem2277602 : term434 = term408.
Proof. exact (TRANS (@lem2277598) (@lem2277601)). Qed.
Lemma lem2277603 : term408 = term434.
Proof. exact (SYM (@lem2277602)). Qed.
Lemma lem2277604 : term431 = term434.
Proof. exact (TRANS (@lem2277588) (@lem2277603)). Qed.
Lemma lem2277605 : term406 = term435.
Proof. exact (@lem2277555 (@lem2277604)). Qed.
Lemma lem2277606 : term405 = term435.
Proof. exact (TRANS (@lem2277521) (@lem2277605)). Qed.
Lemma lem2277608 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2277609 : term435 = term408.
Proof. exact (@lem2277608 term408). Qed.
Lemma lem2277610 : term405 = term408.
Proof. exact (TRANS (@lem2277606) (@lem2277609)). Qed.
Lemma lem2277611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277612 : term437 = term430.
Proof. exact (MK_COMB (@lem2277611) (@lem2277610)). Qed.
Lemma lem2277613 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem2277614 (m : nat) : (term395 m) = (term433 m).
Proof. exact (MK_COMB (@lem2277612) (@lem2277613 m)). Qed.
Lemma lem2277615 (m : nat) : (term518 m) = (term433 m).
Proof. exact (TRANS (@lem2277512 m) (@lem2277614 m)). Qed.
Lemma lem2277616 (m : nat) : (term433 m) = term408.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem2277617 (m : nat) : (term518 m) = term408.
Proof. exact (TRANS (@lem2277615 m) (@lem2277616 m)). Qed.
Lemma lem2277618 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2277619 (m : nat) (d : nat) : (term640 d m) = (term566 d).
Proof. exact (MK_COMB (@lem2277618 d) (@lem2277617 m)). Qed.
Lemma lem2277620 (m : nat) (d : nat) : (term639 d m) = (term566 d).
Proof. exact (TRANS (@lem2277511 d m) (@lem2277619 m d)). Qed.
Lemma lem2277621 (d : nat) : (term566 d) = (real_of_num d).
Proof. exact (@lem1982723 (real_of_num d)). Qed.
Lemma lem2277622 (m : nat) (d : nat) : (term639 d m) = (real_of_num d).
Proof. exact (TRANS (@lem2277620 m d) (@lem2277621 d)). Qed.
Lemma lem2277623 (m : nat) (d : nat) : (term283 m d) = (real_of_num d).
Proof. exact (TRANS (@lem2277510 d m) (@lem2277622 m d)). Qed.
Lemma lem2277624 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2277625 (m : nat) (d : nat) : (term641 m d) = (term568 d).
Proof. exact (MK_COMB (@lem2277624) (@lem2277623 m d)). Qed.
Lemma lem2277626 (m : nat) (d : nat) : (term642 m d) = (term570 d).
Proof. exact (MK_COMB (@lem2277625 m d) (@lem2277493 d)). Qed.
Lemma lem2277627 (d : nat) : (term570 d) = (term394 d).
Proof. exact (@lem1982792 (real_of_num d) (real_of_num d)). Qed.
Lemma lem2277631 (d : nat) : (term394 d) = (term395 d).
Proof. exact (@lem1982715 term396 (real_of_num d)). Qed.
Lemma lem2277633 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277634 : term398 = term399.
Proof. exact (@lem2277633 term400). Qed.
Lemma lem2277636 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277637 : term396 = term402.
Proof. exact (@lem2277636 term400). Qed.
Lemma lem2277638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277639 : term403 = term404.
Proof. exact (MK_COMB (@lem2277638) (@lem2277637)). Qed.
Lemma lem2277640 : term405 = term406.
Proof. exact (MK_COMB (@lem2277639) (@lem2277634)). Qed.
Lemma lem2277641 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2277643 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277644 : term410 = term411.
Proof. exact (@lem2277643 (NUMERAL 0) term400). Qed.
Lemma lem2277645 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277646 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277647 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277646 h1) (fun h1 : term411 = True => @lem2277645)). Qed.
Lemma lem2277648 : term411 = True.
Proof. exact (EQ_MP (@lem2277647) (@lem2277645)). Qed.
Lemma lem2277649 : term410 = True.
Proof. exact (TRANS (@lem2277644) (@lem2277648)). Qed.
Lemma lem2277650 : True = term410.
Proof. exact (SYM (@lem2277649)). Qed.
Lemma lem2277651 : term410.
Proof. exact (EQ_MP (@lem2277650) (@lem0)). Qed.
Lemma lem2277652 : term413.
Proof. exact (@lem2277641 (@lem2277651)). Qed.
Lemma lem2277654 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277655 : term410 = term411.
Proof. exact (@lem2277654 (NUMERAL 0) term400). Qed.
Lemma lem2277656 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277657 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277658 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277657 h1) (fun h1 : term411 = True => @lem2277656)). Qed.
Lemma lem2277659 : term411 = True.
Proof. exact (EQ_MP (@lem2277658) (@lem2277656)). Qed.
Lemma lem2277660 : term410 = True.
Proof. exact (TRANS (@lem2277655) (@lem2277659)). Qed.
Lemma lem2277661 : True = term410.
Proof. exact (SYM (@lem2277660)). Qed.
Lemma lem2277662 : term410.
Proof. exact (EQ_MP (@lem2277661) (@lem0)). Qed.
Lemma lem2277663 : term414.
Proof. exact (@lem2277652 (@lem2277662)). Qed.
Lemma lem2277665 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277666 : term410 = term411.
Proof. exact (@lem2277665 (NUMERAL 0) term400). Qed.
Lemma lem2277667 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277668 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277669 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277668 h1) (fun h1 : term411 = True => @lem2277667)). Qed.
Lemma lem2277670 : term411 = True.
Proof. exact (EQ_MP (@lem2277669) (@lem2277667)). Qed.
Lemma lem2277671 : term410 = True.
Proof. exact (TRANS (@lem2277666) (@lem2277670)). Qed.
Lemma lem2277672 : True = term410.
Proof. exact (SYM (@lem2277671)). Qed.
Lemma lem2277673 : term410.
Proof. exact (EQ_MP (@lem2277672) (@lem0)). Qed.
Lemma lem2277674 : term415.
Proof. exact (@lem2277663 (@lem2277673)). Qed.
Lemma lem2277676 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277677 : term418 = term419.
Proof. exact (@lem2277676 term400 term400). Qed.
Lemma lem2277678 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277679 : term421 = term400.
Proof. exact (EQ_MP (@lem2277678) (@lem940073)). Qed.
Lemma lem2277680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277681 : term419 = term398.
Proof. exact (MK_COMB (@lem2277680) (@lem2277679)). Qed.
Lemma lem2277682 : term418 = term398.
Proof. exact (TRANS (@lem2277677) (@lem2277681)). Qed.
Lemma lem2277684 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2277685 : term424 = term425.
Proof. exact (@lem2277684 term400 term400). Qed.
Lemma lem2277686 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277687 : term421 = term400.
Proof. exact (EQ_MP (@lem2277686) (@lem940073)). Qed.
Lemma lem2277688 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277689 : term419 = term398.
Proof. exact (MK_COMB (@lem2277688) (@lem2277687)). Qed.
Lemma lem2277690 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277691 : term425 = term396.
Proof. exact (MK_COMB (@lem2277690) (@lem2277689)). Qed.
Lemma lem2277692 : term424 = term396.
Proof. exact (TRANS (@lem2277685) (@lem2277691)). Qed.
Lemma lem2277693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277694 : term426 = term403.
Proof. exact (MK_COMB (@lem2277693) (@lem2277692)). Qed.
Lemma lem2277695 : term427 = term405.
Proof. exact (MK_COMB (@lem2277694) (@lem2277682)). Qed.
Lemma lem2277697 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2277698 : term405 = term408.
Proof. exact (@lem2277697 term400). Qed.
Lemma lem2277699 : term427 = term408.
Proof. exact (TRANS (@lem2277695) (@lem2277698)). Qed.
Lemma lem2277700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277701 : term429 = term430.
Proof. exact (MK_COMB (@lem2277700) (@lem2277699)). Qed.
Lemma lem2277702 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2277703 : term431 = term432.
Proof. exact (MK_COMB (@lem2277701) (@lem2277702)). Qed.
Lemma lem2277705 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277706 : term432 = term408.
Proof. exact (@lem2277705 term400). Qed.
Lemma lem2277707 : term431 = term408.
Proof. exact (TRANS (@lem2277703) (@lem2277706)). Qed.
Lemma lem2277709 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277710 : term418 = term419.
Proof. exact (@lem2277709 term400 term400). Qed.
Lemma lem2277711 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277712 : term421 = term400.
Proof. exact (EQ_MP (@lem2277711) (@lem940073)). Qed.
Lemma lem2277713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277714 : term419 = term398.
Proof. exact (MK_COMB (@lem2277713) (@lem2277712)). Qed.
Lemma lem2277715 : term418 = term398.
Proof. exact (TRANS (@lem2277710) (@lem2277714)). Qed.
Lemma lem2277716 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2277717 : term434 = term432.
Proof. exact (MK_COMB (@lem2277716) (@lem2277715)). Qed.
Lemma lem2277719 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277720 : term432 = term408.
Proof. exact (@lem2277719 term400). Qed.
Lemma lem2277721 : term434 = term408.
Proof. exact (TRANS (@lem2277717) (@lem2277720)). Qed.
Lemma lem2277722 : term408 = term434.
Proof. exact (SYM (@lem2277721)). Qed.
Lemma lem2277723 : term431 = term434.
Proof. exact (TRANS (@lem2277707) (@lem2277722)). Qed.
Lemma lem2277724 : term406 = term435.
Proof. exact (@lem2277674 (@lem2277723)). Qed.
Lemma lem2277725 : term405 = term435.
Proof. exact (TRANS (@lem2277640) (@lem2277724)). Qed.
Lemma lem2277727 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2277728 : term435 = term408.
Proof. exact (@lem2277727 term408). Qed.
Lemma lem2277729 : term405 = term408.
Proof. exact (TRANS (@lem2277725) (@lem2277728)). Qed.
Lemma lem2277730 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277731 : term437 = term430.
Proof. exact (MK_COMB (@lem2277730) (@lem2277729)). Qed.
Lemma lem2277732 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2277733 (d : nat) : (term395 d) = (term433 d).
Proof. exact (MK_COMB (@lem2277731) (@lem2277732 d)). Qed.
Lemma lem2277734 (d : nat) : (term394 d) = (term433 d).
Proof. exact (TRANS (@lem2277631 d) (@lem2277733 d)). Qed.
Lemma lem2277735 (d : nat) : (term433 d) = term408.
Proof. exact (@lem1982719 (real_of_num d)). Qed.
Lemma lem2277737 (d : nat) : (term394 d) = term408.
Proof. exact (TRANS (@lem2277734 d) (@lem2277735 d)). Qed.
Lemma lem2277738 (d : nat) : (term570 d) = term408.
Proof. exact (TRANS (@lem2277627 d) (@lem2277737 d)). Qed.
Lemma lem2277739 (m : nat) (d : nat) : (term642 m d) = term408.
Proof. exact (TRANS (@lem2277626 m d) (@lem2277738 d)). Qed.
Lemma lem2277740 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277741 (m : nat) (d : nat) : (term643 m d) = term520.
Proof. exact (MK_COMB (@lem2277740) (@lem2277739 m d)). Qed.
Lemma lem2277742 : term520 = term521.
Proof. exact (@lem1982785 term408). Qed.
Lemma lem2277744 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277745 : term408 = term435.
Proof. exact (@lem2277744 (NUMERAL 0)). Qed.
Lemma lem2277747 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277748 : term396 = term402.
Proof. exact (@lem2277747 term400). Qed.
Lemma lem2277749 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277750 : term476 = term477.
Proof. exact (MK_COMB (@lem2277749) (@lem2277748)). Qed.
Lemma lem2277751 : term521 = term522.
Proof. exact (MK_COMB (@lem2277750) (@lem2277745)). Qed.
Lemma lem2277752 : term522 = term523.
Proof. exact (@lem1981613 term396 term408 term398 term398). Qed.
Lemma lem2277754 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277755 : term418 = term419.
Proof. exact (@lem2277754 term400 term400). Qed.
Lemma lem2277756 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277757 : term421 = term400.
Proof. exact (EQ_MP (@lem2277756) (@lem940073)). Qed.
Lemma lem2277758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277759 : term419 = term398.
Proof. exact (MK_COMB (@lem2277758) (@lem2277757)). Qed.
Lemma lem2277760 : term418 = term398.
Proof. exact (TRANS (@lem2277755) (@lem2277759)). Qed.
Lemma lem2277762 (x : nat) : (term524 x) = term408.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2277763 : term521 = term408.
Proof. exact (@lem2277762 term400). Qed.
Lemma lem2277764 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2277765 : term525 = term526.
Proof. exact (MK_COMB (@lem2277764) (@lem2277763)). Qed.
Lemma lem2277766 : term523 = term435.
Proof. exact (MK_COMB (@lem2277765) (@lem2277760)). Qed.
Lemma lem2277767 : term522 = term435.
Proof. exact (TRANS (@lem2277752) (@lem2277766)). Qed.
Lemma lem2277768 : term521 = term435.
Proof. exact (TRANS (@lem2277751) (@lem2277767)). Qed.
Lemma lem2277770 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2277771 : term435 = term408.
Proof. exact (@lem2277770 term408). Qed.
Lemma lem2277772 : term521 = term408.
Proof. exact (TRANS (@lem2277768) (@lem2277771)). Qed.
Lemma lem2277773 : term520 = term408.
Proof. exact (TRANS (@lem2277742) (@lem2277772)). Qed.
Lemma lem2277774 (m : nat) (d : nat) : (term644 m d) = (term644 m d).
Proof. exact (eq_refl (term644 m d)). Qed.
Lemma lem2277775 (m : nat) (d : nat) : ((term643 m d) = term520) = ((term643 m d) = term408).
Proof. exact (MK_COMB (@lem2277774 m d) (@lem2277773)). Qed.
Lemma lem2277776 (m : nat) (d : nat) : (term643 m d) = term408.
Proof. exact (EQ_MP (@lem2277775 m d) (@lem2277741 m d)). Qed.
Lemma lem2277777 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2277778 (m : nat) (d : nat) : (term645 m d) = term529.
Proof. exact (MK_COMB (@lem2277777) (@lem2277776 m d)). Qed.
Lemma lem2277779 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2277780 (m : nat) (d : nat) : (term646 m d) = term531.
Proof. exact (MK_COMB (@lem2277778 m d) (@lem2277779)). Qed.
Lemma lem2277781 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2277782 (m : nat) (d : nat) : (term647 m d) = term529.
Proof. exact (MK_COMB (@lem2277781) (@lem2277739 m d)). Qed.
Lemma lem2277783 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2277784 (m : nat) (d : nat) : (term648 m d) = term531.
Proof. exact (MK_COMB (@lem2277782 m d) (@lem2277783)). Qed.
Lemma lem2277785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2277786 (m : nat) (d : nat) : (term649 m d) = term535.
Proof. exact (MK_COMB (@lem2277785) (@lem2277784 m d)). Qed.
Lemma lem2277787 (m : nat) (d : nat) : (term638 m d) = term536.
Proof. exact (MK_COMB (@lem2277786 m d) (@lem2277780 m d)). Qed.
Lemma lem2277788 (m : nat) (d : nat) : (term637 m d) = term536.
Proof. exact (TRANS (@lem2277492 m d) (@lem2277787 m d)). Qed.
Lemma lem2277789 (m : nat) (d : nat) : (term650 m d) = (term651 m d).
Proof. exact (@lem1988318 (term283 m d) (term93 d)). Qed.
Lemma lem2277796 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2277803 (d : nat) (m : nat) : (term25 m d) = (term25 d m).
Proof. exact (@lem1982761 (real_of_num d) (real_of_num m)). Qed.
Lemma lem2277810 (m : nat) : (term93 m) = (term389 m).
Proof. exact (@lem1982785 (real_of_num m)). Qed.
Lemma lem2277811 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277812 (m : nat) : (term127 m) = (term390 m).
Proof. exact (MK_COMB (@lem2277811) (@lem2277810 m)). Qed.
Lemma lem2277813 (d : nat) (m : nat) : (term283 m d) = (term639 d m).
Proof. exact (MK_COMB (@lem2277812 m) (@lem2277803 d m)). Qed.
Lemma lem2277814 (d : nat) (m : nat) : (term639 d m) = (term640 d m).
Proof. exact (@lem1982757 (real_of_num d) (term389 m) (real_of_num m)). Qed.
Lemma lem2277815 (m : nat) : (term518 m) = (term395 m).
Proof. exact (@lem1982713 term396 (real_of_num m)). Qed.
Lemma lem2277817 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277818 : term398 = term399.
Proof. exact (@lem2277817 term400). Qed.
Lemma lem2277820 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277821 : term396 = term402.
Proof. exact (@lem2277820 term400). Qed.
Lemma lem2277822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277823 : term403 = term404.
Proof. exact (MK_COMB (@lem2277822) (@lem2277821)). Qed.
Lemma lem2277824 : term405 = term406.
Proof. exact (MK_COMB (@lem2277823) (@lem2277818)). Qed.
Lemma lem2277825 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2277827 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277828 : term410 = term411.
Proof. exact (@lem2277827 (NUMERAL 0) term400). Qed.
Lemma lem2277829 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277830 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277831 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277830 h1) (fun h1 : term411 = True => @lem2277829)). Qed.
Lemma lem2277832 : term411 = True.
Proof. exact (EQ_MP (@lem2277831) (@lem2277829)). Qed.
Lemma lem2277833 : term410 = True.
Proof. exact (TRANS (@lem2277828) (@lem2277832)). Qed.
Lemma lem2277834 : True = term410.
Proof. exact (SYM (@lem2277833)). Qed.
Lemma lem2277835 : term410.
Proof. exact (EQ_MP (@lem2277834) (@lem0)). Qed.
Lemma lem2277836 : term413.
Proof. exact (@lem2277825 (@lem2277835)). Qed.
Lemma lem2277838 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277839 : term410 = term411.
Proof. exact (@lem2277838 (NUMERAL 0) term400). Qed.
Lemma lem2277840 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277841 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277842 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277841 h1) (fun h1 : term411 = True => @lem2277840)). Qed.
Lemma lem2277843 : term411 = True.
Proof. exact (EQ_MP (@lem2277842) (@lem2277840)). Qed.
Lemma lem2277844 : term410 = True.
Proof. exact (TRANS (@lem2277839) (@lem2277843)). Qed.
Lemma lem2277845 : True = term410.
Proof. exact (SYM (@lem2277844)). Qed.
Lemma lem2277846 : term410.
Proof. exact (EQ_MP (@lem2277845) (@lem0)). Qed.
Lemma lem2277847 : term414.
Proof. exact (@lem2277836 (@lem2277846)). Qed.
Lemma lem2277849 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277850 : term410 = term411.
Proof. exact (@lem2277849 (NUMERAL 0) term400). Qed.
Lemma lem2277851 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277852 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277853 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277852 h1) (fun h1 : term411 = True => @lem2277851)). Qed.
Lemma lem2277854 : term411 = True.
Proof. exact (EQ_MP (@lem2277853) (@lem2277851)). Qed.
Lemma lem2277855 : term410 = True.
Proof. exact (TRANS (@lem2277850) (@lem2277854)). Qed.
Lemma lem2277856 : True = term410.
Proof. exact (SYM (@lem2277855)). Qed.
Lemma lem2277857 : term410.
Proof. exact (EQ_MP (@lem2277856) (@lem0)). Qed.
Lemma lem2277858 : term415.
Proof. exact (@lem2277847 (@lem2277857)). Qed.
Lemma lem2277860 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277861 : term418 = term419.
Proof. exact (@lem2277860 term400 term400). Qed.
Lemma lem2277862 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277863 : term421 = term400.
Proof. exact (EQ_MP (@lem2277862) (@lem940073)). Qed.
Lemma lem2277864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277865 : term419 = term398.
Proof. exact (MK_COMB (@lem2277864) (@lem2277863)). Qed.
Lemma lem2277866 : term418 = term398.
Proof. exact (TRANS (@lem2277861) (@lem2277865)). Qed.
Lemma lem2277868 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2277869 : term424 = term425.
Proof. exact (@lem2277868 term400 term400). Qed.
Lemma lem2277870 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277871 : term421 = term400.
Proof. exact (EQ_MP (@lem2277870) (@lem940073)). Qed.
Lemma lem2277872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277873 : term419 = term398.
Proof. exact (MK_COMB (@lem2277872) (@lem2277871)). Qed.
Lemma lem2277874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2277875 : term425 = term396.
Proof. exact (MK_COMB (@lem2277874) (@lem2277873)). Qed.
Lemma lem2277876 : term424 = term396.
Proof. exact (TRANS (@lem2277869) (@lem2277875)). Qed.
Lemma lem2277877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277878 : term426 = term403.
Proof. exact (MK_COMB (@lem2277877) (@lem2277876)). Qed.
Lemma lem2277879 : term427 = term405.
Proof. exact (MK_COMB (@lem2277878) (@lem2277866)). Qed.
Lemma lem2277881 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2277882 : term405 = term408.
Proof. exact (@lem2277881 term400). Qed.
Lemma lem2277883 : term427 = term408.
Proof. exact (TRANS (@lem2277879) (@lem2277882)). Qed.
Lemma lem2277884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277885 : term429 = term430.
Proof. exact (MK_COMB (@lem2277884) (@lem2277883)). Qed.
Lemma lem2277886 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2277887 : term431 = term432.
Proof. exact (MK_COMB (@lem2277885) (@lem2277886)). Qed.
Lemma lem2277889 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277890 : term432 = term408.
Proof. exact (@lem2277889 term400). Qed.
Lemma lem2277891 : term431 = term408.
Proof. exact (TRANS (@lem2277887) (@lem2277890)). Qed.
Lemma lem2277893 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277894 : term418 = term419.
Proof. exact (@lem2277893 term400 term400). Qed.
Lemma lem2277895 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277896 : term421 = term400.
Proof. exact (EQ_MP (@lem2277895) (@lem940073)). Qed.
Lemma lem2277897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277898 : term419 = term398.
Proof. exact (MK_COMB (@lem2277897) (@lem2277896)). Qed.
Lemma lem2277899 : term418 = term398.
Proof. exact (TRANS (@lem2277894) (@lem2277898)). Qed.
Lemma lem2277900 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2277901 : term434 = term432.
Proof. exact (MK_COMB (@lem2277900) (@lem2277899)). Qed.
Lemma lem2277903 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2277904 : term432 = term408.
Proof. exact (@lem2277903 term400). Qed.
Lemma lem2277905 : term434 = term408.
Proof. exact (TRANS (@lem2277901) (@lem2277904)). Qed.
Lemma lem2277906 : term408 = term434.
Proof. exact (SYM (@lem2277905)). Qed.
Lemma lem2277907 : term431 = term434.
Proof. exact (TRANS (@lem2277891) (@lem2277906)). Qed.
Lemma lem2277908 : term406 = term435.
Proof. exact (@lem2277858 (@lem2277907)). Qed.
Lemma lem2277909 : term405 = term435.
Proof. exact (TRANS (@lem2277824) (@lem2277908)). Qed.
Lemma lem2277911 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2277912 : term435 = term408.
Proof. exact (@lem2277911 term408). Qed.
Lemma lem2277913 : term405 = term408.
Proof. exact (TRANS (@lem2277909) (@lem2277912)). Qed.
Lemma lem2277914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277915 : term437 = term430.
Proof. exact (MK_COMB (@lem2277914) (@lem2277913)). Qed.
Lemma lem2277916 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem2277917 (m : nat) : (term395 m) = (term433 m).
Proof. exact (MK_COMB (@lem2277915) (@lem2277916 m)). Qed.
Lemma lem2277918 (m : nat) : (term518 m) = (term433 m).
Proof. exact (TRANS (@lem2277815 m) (@lem2277917 m)). Qed.
Lemma lem2277919 (m : nat) : (term433 m) = term408.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem2277920 (m : nat) : (term518 m) = term408.
Proof. exact (TRANS (@lem2277918 m) (@lem2277919 m)). Qed.
Lemma lem2277921 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2277922 (m : nat) (d : nat) : (term640 d m) = (term566 d).
Proof. exact (MK_COMB (@lem2277921 d) (@lem2277920 m)). Qed.
Lemma lem2277923 (m : nat) (d : nat) : (term639 d m) = (term566 d).
Proof. exact (TRANS (@lem2277814 d m) (@lem2277922 m d)). Qed.
Lemma lem2277924 (d : nat) : (term566 d) = (real_of_num d).
Proof. exact (@lem1982723 (real_of_num d)). Qed.
Lemma lem2277925 (m : nat) (d : nat) : (term639 d m) = (real_of_num d).
Proof. exact (TRANS (@lem2277923 m d) (@lem2277924 d)). Qed.
Lemma lem2277926 (m : nat) (d : nat) : (term283 m d) = (real_of_num d).
Proof. exact (TRANS (@lem2277813 d m) (@lem2277925 m d)). Qed.
Lemma lem2277927 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2277928 (m : nat) (d : nat) : (term641 m d) = (term568 d).
Proof. exact (MK_COMB (@lem2277927) (@lem2277926 m d)). Qed.
Lemma lem2277929 (m : nat) (d : nat) : (term652 m d) = (term581 d).
Proof. exact (MK_COMB (@lem2277928 m d) (@lem2277796 d)). Qed.
Lemma lem2277930 (d : nat) : (term581 d) = (term582 d).
Proof. exact (@lem1982792 (real_of_num d) (term389 d)). Qed.
Lemma lem2277931 (d : nat) : (term508 d) = (term509 d).
Proof. exact (@lem1982749 term396 term396 (real_of_num d)). Qed.
Lemma lem2277933 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277934 : term396 = term402.
Proof. exact (@lem2277933 term400). Qed.
Lemma lem2277936 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2277937 : term396 = term402.
Proof. exact (@lem2277936 term400). Qed.
Lemma lem2277938 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277939 : term476 = term477.
Proof. exact (MK_COMB (@lem2277938) (@lem2277937)). Qed.
Lemma lem2277940 : term510 = term511.
Proof. exact (MK_COMB (@lem2277939) (@lem2277934)). Qed.
Lemma lem2277941 : term511 = term512.
Proof. exact (@lem1981613 term396 term396 term398 term398). Qed.
Lemma lem2277943 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2277944 : term418 = term419.
Proof. exact (@lem2277943 term400 term400). Qed.
Lemma lem2277945 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277946 : term421 = term400.
Proof. exact (EQ_MP (@lem2277945) (@lem940073)). Qed.
Lemma lem2277947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277948 : term419 = term398.
Proof. exact (MK_COMB (@lem2277947) (@lem2277946)). Qed.
Lemma lem2277949 : term418 = term398.
Proof. exact (TRANS (@lem2277944) (@lem2277948)). Qed.
Lemma lem2277951 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2277952 : term510 = term419.
Proof. exact (@lem2277951 term400 term400). Qed.
Lemma lem2277953 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2277954 : term421 = term400.
Proof. exact (EQ_MP (@lem2277953) (@lem940073)). Qed.
Lemma lem2277955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2277956 : term419 = term398.
Proof. exact (MK_COMB (@lem2277955) (@lem2277954)). Qed.
Lemma lem2277957 : term510 = term398.
Proof. exact (TRANS (@lem2277952) (@lem2277956)). Qed.
Lemma lem2277958 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2277959 : term513 = term514.
Proof. exact (MK_COMB (@lem2277958) (@lem2277957)). Qed.
Lemma lem2277960 : term512 = term399.
Proof. exact (MK_COMB (@lem2277959) (@lem2277949)). Qed.
Lemma lem2277961 : term511 = term399.
Proof. exact (TRANS (@lem2277941) (@lem2277960)). Qed.
Lemma lem2277962 : term510 = term399.
Proof. exact (TRANS (@lem2277940) (@lem2277961)). Qed.
Lemma lem2277964 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2277965 : term399 = term398.
Proof. exact (@lem2277964 term398). Qed.
Lemma lem2277966 : term510 = term398.
Proof. exact (TRANS (@lem2277962) (@lem2277965)). Qed.
Lemma lem2277967 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2277968 : term515 = term516.
Proof. exact (MK_COMB (@lem2277967) (@lem2277966)). Qed.
Lemma lem2277969 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2277970 (d : nat) : (term509 d) = (term517 d).
Proof. exact (MK_COMB (@lem2277968) (@lem2277969 d)). Qed.
Lemma lem2277971 (d : nat) : (term508 d) = (term517 d).
Proof. exact (TRANS (@lem2277931 d) (@lem2277970 d)). Qed.
Lemma lem2277972 (d : nat) : (term517 d) = (real_of_num d).
Proof. exact (@lem1982709 (real_of_num d)). Qed.
Lemma lem2277973 (d : nat) : (term508 d) = (real_of_num d).
Proof. exact (TRANS (@lem2277971 d) (@lem2277972 d)). Qed.
Lemma lem2277974 (d : nat) : (term110 d) = (term110 d).
Proof. exact (eq_refl (term110 d)). Qed.
Lemma lem2277975 (d : nat) : (term582 d) = (term583 d).
Proof. exact (MK_COMB (@lem2277974 d) (@lem2277973 d)). Qed.
Lemma lem2277976 (d : nat) : (term583 d) = (term584 d).
Proof. exact (@lem1982717 (real_of_num d)). Qed.
Lemma lem2277978 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277979 : term398 = term399.
Proof. exact (@lem2277978 term400). Qed.
Lemma lem2277981 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2277982 : term398 = term399.
Proof. exact (@lem2277981 term400). Qed.
Lemma lem2277983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2277984 : term585 = term586.
Proof. exact (MK_COMB (@lem2277983) (@lem2277982)). Qed.
Lemma lem2277985 : term587 = term588.
Proof. exact (MK_COMB (@lem2277984) (@lem2277979)). Qed.
Lemma lem2277986 : term589.
Proof. exact (@lem1981473 term398 term398 term398 term398 term459 term398). Qed.
Lemma lem2277988 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2277989 : term410 = term411.
Proof. exact (@lem2277988 (NUMERAL 0) term400). Qed.
Lemma lem2277990 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2277991 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2277992 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2277991 h1) (fun h1 : term411 = True => @lem2277990)). Qed.
Lemma lem2277993 : term411 = True.
Proof. exact (EQ_MP (@lem2277992) (@lem2277990)). Qed.
Lemma lem2277994 : term410 = True.
Proof. exact (TRANS (@lem2277989) (@lem2277993)). Qed.
Lemma lem2277995 : True = term410.
Proof. exact (SYM (@lem2277994)). Qed.
Lemma lem2277996 : term410.
Proof. exact (EQ_MP (@lem2277995) (@lem0)). Qed.
Lemma lem2277997 : term590.
Proof. exact (@lem2277986 (@lem2277996)). Qed.
Lemma lem2277999 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278000 : term410 = term411.
Proof. exact (@lem2277999 (NUMERAL 0) term400). Qed.
Lemma lem2278001 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278002 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278003 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278002 h1) (fun h1 : term411 = True => @lem2278001)). Qed.
Lemma lem2278004 : term411 = True.
Proof. exact (EQ_MP (@lem2278003) (@lem2278001)). Qed.
Lemma lem2278005 : term410 = True.
Proof. exact (TRANS (@lem2278000) (@lem2278004)). Qed.
Lemma lem2278006 : True = term410.
Proof. exact (SYM (@lem2278005)). Qed.
Lemma lem2278007 : term410.
Proof. exact (EQ_MP (@lem2278006) (@lem0)). Qed.
Lemma lem2278008 : term591.
Proof. exact (@lem2277997 (@lem2278007)). Qed.
Lemma lem2278010 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278011 : term410 = term411.
Proof. exact (@lem2278010 (NUMERAL 0) term400). Qed.
Lemma lem2278012 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278013 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278014 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278013 h1) (fun h1 : term411 = True => @lem2278012)). Qed.
Lemma lem2278015 : term411 = True.
Proof. exact (EQ_MP (@lem2278014) (@lem2278012)). Qed.
Lemma lem2278016 : term410 = True.
Proof. exact (TRANS (@lem2278011) (@lem2278015)). Qed.
Lemma lem2278017 : True = term410.
Proof. exact (SYM (@lem2278016)). Qed.
Lemma lem2278018 : term410.
Proof. exact (EQ_MP (@lem2278017) (@lem0)). Qed.
Lemma lem2278019 : term592.
Proof. exact (@lem2278008 (@lem2278018)). Qed.
Lemma lem2278021 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278022 : term418 = term419.
Proof. exact (@lem2278021 term400 term400). Qed.
Lemma lem2278023 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278024 : term421 = term400.
Proof. exact (EQ_MP (@lem2278023) (@lem940073)). Qed.
Lemma lem2278025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278026 : term419 = term398.
Proof. exact (MK_COMB (@lem2278025) (@lem2278024)). Qed.
Lemma lem2278027 : term418 = term398.
Proof. exact (TRANS (@lem2278022) (@lem2278026)). Qed.
Lemma lem2278029 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278030 : term418 = term419.
Proof. exact (@lem2278029 term400 term400). Qed.
Lemma lem2278031 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278032 : term421 = term400.
Proof. exact (EQ_MP (@lem2278031) (@lem940073)). Qed.
Lemma lem2278033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278034 : term419 = term398.
Proof. exact (MK_COMB (@lem2278033) (@lem2278032)). Qed.
Lemma lem2278035 : term418 = term398.
Proof. exact (TRANS (@lem2278030) (@lem2278034)). Qed.
Lemma lem2278036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278037 : term593 = term585.
Proof. exact (MK_COMB (@lem2278036) (@lem2278035)). Qed.
Lemma lem2278038 : term594 = term587.
Proof. exact (MK_COMB (@lem2278037) (@lem2278027)). Qed.
Lemma lem2278039 : term587 = term458.
Proof. exact (@lem1367770 term400 term400). Qed.
Lemma lem2278040 : term454 = term455.
Proof. exact (@lem706885). Qed.
Lemma lem2278041 : (term454 = term455) = (term456 = term457).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term455). Qed.
Lemma lem2278042 : term456 = term457.
Proof. exact (EQ_MP (@lem2278041) (@lem2278040)). Qed.
Lemma lem2278043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278044 : term458 = term459.
Proof. exact (MK_COMB (@lem2278043) (@lem2278042)). Qed.
Lemma lem2278045 : term587 = term459.
Proof. exact (TRANS (@lem2278039) (@lem2278044)). Qed.
Lemma lem2278046 : term594 = term459.
Proof. exact (TRANS (@lem2278038) (@lem2278045)). Qed.
Lemma lem2278047 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278048 : term595 = term489.
Proof. exact (MK_COMB (@lem2278047) (@lem2278046)). Qed.
Lemma lem2278049 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2278050 : term596 = term597.
Proof. exact (MK_COMB (@lem2278048) (@lem2278049)). Qed.
Lemma lem2278052 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278053 : term597 = term467.
Proof. exact (@lem2278052 term457 term400). Qed.
Lemma lem2278054 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2278055 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2278056 : term466 = term457.
Proof. exact (EQ_MP (@lem2278055) (@lem2278054)). Qed.
Lemma lem2278057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278058 : term467 = term459.
Proof. exact (MK_COMB (@lem2278057) (@lem2278056)). Qed.
Lemma lem2278059 : term597 = term459.
Proof. exact (TRANS (@lem2278053) (@lem2278058)). Qed.
Lemma lem2278060 : term596 = term459.
Proof. exact (TRANS (@lem2278050) (@lem2278059)). Qed.
Lemma lem2278062 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278063 : term418 = term419.
Proof. exact (@lem2278062 term400 term400). Qed.
Lemma lem2278064 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278065 : term421 = term400.
Proof. exact (EQ_MP (@lem2278064) (@lem940073)). Qed.
Lemma lem2278066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278067 : term419 = term398.
Proof. exact (MK_COMB (@lem2278066) (@lem2278065)). Qed.
Lemma lem2278068 : term418 = term398.
Proof. exact (TRANS (@lem2278063) (@lem2278067)). Qed.
Lemma lem2278069 : term489 = term489.
Proof. exact (eq_refl term489). Qed.
Lemma lem2278070 : term598 = term597.
Proof. exact (MK_COMB (@lem2278069) (@lem2278068)). Qed.
Lemma lem2278072 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278073 : term597 = term467.
Proof. exact (@lem2278072 term457 term400). Qed.
Lemma lem2278074 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2278075 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2278076 : term466 = term457.
Proof. exact (EQ_MP (@lem2278075) (@lem2278074)). Qed.
Lemma lem2278077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278078 : term467 = term459.
Proof. exact (MK_COMB (@lem2278077) (@lem2278076)). Qed.
Lemma lem2278079 : term597 = term459.
Proof. exact (TRANS (@lem2278073) (@lem2278078)). Qed.
Lemma lem2278080 : term598 = term459.
Proof. exact (TRANS (@lem2278070) (@lem2278079)). Qed.
Lemma lem2278081 : term459 = term598.
Proof. exact (SYM (@lem2278080)). Qed.
Lemma lem2278082 : term596 = term598.
Proof. exact (TRANS (@lem2278060) (@lem2278081)). Qed.
Lemma lem2278083 : term588 = term487.
Proof. exact (@lem2278019 (@lem2278082)). Qed.
Lemma lem2278084 : term587 = term487.
Proof. exact (TRANS (@lem2277985) (@lem2278083)). Qed.
Lemma lem2278086 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2278087 : term487 = term459.
Proof. exact (@lem2278086 term459). Qed.
Lemma lem2278088 : term587 = term459.
Proof. exact (TRANS (@lem2278084) (@lem2278087)). Qed.
Lemma lem2278089 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278090 : term599 = term489.
Proof. exact (MK_COMB (@lem2278089) (@lem2278088)). Qed.
Lemma lem2278091 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2278092 (d : nat) : (term584 d) = (term490 d).
Proof. exact (MK_COMB (@lem2278090) (@lem2278091 d)). Qed.
Lemma lem2278093 (d : nat) : (term583 d) = (term490 d).
Proof. exact (TRANS (@lem2277976 d) (@lem2278092 d)). Qed.
Lemma lem2278094 (d : nat) : (term582 d) = (term490 d).
Proof. exact (TRANS (@lem2277975 d) (@lem2278093 d)). Qed.
Lemma lem2278095 (d : nat) : (term581 d) = (term490 d).
Proof. exact (TRANS (@lem2277930 d) (@lem2278094 d)). Qed.
Lemma lem2278096 (m : nat) (d : nat) : (term652 m d) = (term490 d).
Proof. exact (TRANS (@lem2277929 m d) (@lem2278095 d)). Qed.
Lemma lem2278097 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278098 (m : nat) (d : nat) : (term653 m d) = (term601 d).
Proof. exact (MK_COMB (@lem2278097) (@lem2278096 m d)). Qed.
Lemma lem2278099 (d : nat) : (term601 d) = (term602 d).
Proof. exact (@lem1982785 (term490 d)). Qed.
Lemma lem2278100 (d : nat) : (term602 d) = (term603 d).
Proof. exact (@lem1982749 term396 term459 (real_of_num d)). Qed.
Lemma lem2278102 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278103 : term459 = term487.
Proof. exact (@lem2278102 term457). Qed.
Lemma lem2278105 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278106 : term396 = term402.
Proof. exact (@lem2278105 term400). Qed.
Lemma lem2278107 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278108 : term476 = term477.
Proof. exact (MK_COMB (@lem2278107) (@lem2278106)). Qed.
Lemma lem2278109 : term604 = term605.
Proof. exact (MK_COMB (@lem2278108) (@lem2278103)). Qed.
Lemma lem2278110 : term605 = term606.
Proof. exact (@lem1981613 term396 term459 term398 term398). Qed.
Lemma lem2278112 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278113 : term418 = term419.
Proof. exact (@lem2278112 term400 term400). Qed.
Lemma lem2278114 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278115 : term421 = term400.
Proof. exact (EQ_MP (@lem2278114) (@lem940073)). Qed.
Lemma lem2278116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278117 : term419 = term398.
Proof. exact (MK_COMB (@lem2278116) (@lem2278115)). Qed.
Lemma lem2278118 : term418 = term398.
Proof. exact (TRANS (@lem2278113) (@lem2278117)). Qed.
Lemma lem2278120 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278121 : term604 = term607.
Proof. exact (@lem2278120 term400 term457). Qed.
Lemma lem2278122 : term483 = term455.
Proof. exact (@lem996238 term455). Qed.
Lemma lem2278123 : (term483 = term455) = (term484 = term457).
Proof. exact (@lem1007663 (BIT1 0) term455 term455). Qed.
Lemma lem2278124 : term484 = term457.
Proof. exact (EQ_MP (@lem2278123) (@lem2278122)). Qed.
Lemma lem2278125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278126 : term482 = term459.
Proof. exact (MK_COMB (@lem2278125) (@lem2278124)). Qed.
Lemma lem2278127 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278128 : term607 = term448.
Proof. exact (MK_COMB (@lem2278127) (@lem2278126)). Qed.
Lemma lem2278129 : term604 = term448.
Proof. exact (TRANS (@lem2278121) (@lem2278128)). Qed.
Lemma lem2278130 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2278131 : term608 = term609.
Proof. exact (MK_COMB (@lem2278130) (@lem2278129)). Qed.
Lemma lem2278132 : term606 = term469.
Proof. exact (MK_COMB (@lem2278131) (@lem2278118)). Qed.
Lemma lem2278133 : term605 = term469.
Proof. exact (TRANS (@lem2278110) (@lem2278132)). Qed.
Lemma lem2278134 : term604 = term469.
Proof. exact (TRANS (@lem2278109) (@lem2278133)). Qed.
Lemma lem2278136 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2278137 : term469 = term448.
Proof. exact (@lem2278136 term448). Qed.
Lemma lem2278138 : term604 = term448.
Proof. exact (TRANS (@lem2278134) (@lem2278137)). Qed.
Lemma lem2278139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278140 : term610 = term461.
Proof. exact (MK_COMB (@lem2278139) (@lem2278138)). Qed.
Lemma lem2278141 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2278142 (d : nat) : (term603 d) = (term471 d).
Proof. exact (MK_COMB (@lem2278140) (@lem2278141 d)). Qed.
Lemma lem2278143 (d : nat) : (term602 d) = (term471 d).
Proof. exact (TRANS (@lem2278100 d) (@lem2278142 d)). Qed.
Lemma lem2278144 (d : nat) : (term601 d) = (term471 d).
Proof. exact (TRANS (@lem2278099 d) (@lem2278143 d)). Qed.
Lemma lem2278145 (m : nat) (d : nat) : (term654 m d) = (term654 m d).
Proof. exact (eq_refl (term654 m d)). Qed.
Lemma lem2278146 (m : nat) (d : nat) : ((term653 m d) = (term601 d)) = ((term653 m d) = (term471 d)).
Proof. exact (MK_COMB (@lem2278145 m d) (@lem2278144 d)). Qed.
Lemma lem2278147 (m : nat) (d : nat) : (term653 m d) = (term471 d).
Proof. exact (EQ_MP (@lem2278146 m d) (@lem2278098 m d)). Qed.
Lemma lem2278148 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2278149 (m : nat) (d : nat) : (term655 m d) = (term497 d).
Proof. exact (MK_COMB (@lem2278148) (@lem2278147 m d)). Qed.
Lemma lem2278150 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2278151 (m : nat) (d : nat) : (term656 m d) = (term499 d).
Proof. exact (MK_COMB (@lem2278149 m d) (@lem2278150)). Qed.
Lemma lem2278152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2278153 (m : nat) (d : nat) : (term657 m d) = (term493 d).
Proof. exact (MK_COMB (@lem2278152) (@lem2278096 m d)). Qed.
Lemma lem2278154 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2278155 (m : nat) (d : nat) : (term658 m d) = (term495 d).
Proof. exact (MK_COMB (@lem2278153 m d) (@lem2278154)). Qed.
Lemma lem2278156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2278157 (m : nat) (d : nat) : (term659 m d) = (term617 d).
Proof. exact (MK_COMB (@lem2278156) (@lem2278155 m d)). Qed.
Lemma lem2278158 (m : nat) (d : nat) : (term651 m d) = (term618 d).
Proof. exact (MK_COMB (@lem2278157 m d) (@lem2278151 m d)). Qed.
Lemma lem2278159 (m : nat) (d : nat) : (term650 m d) = (term618 d).
Proof. exact (TRANS (@lem2277789 m d) (@lem2278158 m d)). Qed.
Lemma lem2278160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2278161 (m : nat) (d : nat) : (term660 m d) = term620.
Proof. exact (MK_COMB (@lem2278160) (@lem2277788 m d)). Qed.
Lemma lem2278162 (m : nat) (d : nat) : (term636 m d) = (term621 d).
Proof. exact (MK_COMB (@lem2278161 m d) (@lem2278159 m d)). Qed.
Lemma lem2278169 (m : nat) (d : nat) : (term635 m d) = (term621 d).
Proof. exact (TRANS (@lem2277491 m d) (@lem2278162 m d)). Qed.
Lemma lem2278183 (d : nat) : (term621 d) = (term622 d).
Proof. exact (@lem19158 (term495 d) term536 (term499 d)). Qed.
Lemma lem2278190 (d : nat) : (term623 d) = (term624 d).
Proof. exact (@lem19367 term531 term531 (term499 d)). Qed.
Lemma lem2278197 (d : nat) : (term625 d) = (term626 d).
Proof. exact (@lem19367 term531 term531 (term495 d)). Qed.
Lemma lem2278198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2278199 (d : nat) : (term627 d) = (term628 d).
Proof. exact (MK_COMB (@lem2278198) (@lem2278197 d)). Qed.
Lemma lem2278200 (d : nat) : (term622 d) = (term629 d).
Proof. exact (MK_COMB (@lem2278199 d) (@lem2278190 d)). Qed.
Lemma lem2278202 (d : nat) : (term621 d) = (term629 d).
Proof. exact (TRANS (@lem2278183 d) (@lem2278200 d)). Qed.
Lemma lem2278203 (m : nat) (d : nat) : (term635 m d) = (term629 d).
Proof. exact (TRANS (@lem2278169 m d) (@lem2278202 d)). Qed.
Lemma lem2278225 (d : nat) (h1 : term629 d) : term629 d.
Proof. exact (h1). Qed.
Lemma lem2278226 (d : nat) (h1 : term626 d) : term626 d.
Proof. exact (h1). Qed.
Lemma lem2278227 (d : nat) (h1 : term630 d) : term630 d.
Proof. exact (h1). Qed.
Lemma lem2278229 (d : nat) (h1 : term630 d) : term531.
Proof. exact (proj1 (@lem2278227 d h1)). Qed.
Lemma lem2278232 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2278233 : term531 = term547.
Proof. exact (@lem2278232 term408 term408). Qed.
Lemma lem2278235 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278236 : term408 = term435.
Proof. exact (@lem2278235 (NUMERAL 0)). Qed.
Lemma lem2278238 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278239 : term408 = term435.
Proof. exact (@lem2278238 (NUMERAL 0)). Qed.
Lemma lem2278240 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278241 : term548 = term549.
Proof. exact (MK_COMB (@lem2278240) (@lem2278239)). Qed.
Lemma lem2278242 : term547 = term550.
Proof. exact (MK_COMB (@lem2278241) (@lem2278236)). Qed.
Lemma lem2278243 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2278245 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278246 : term410 = term411.
Proof. exact (@lem2278245 (NUMERAL 0) term400). Qed.
Lemma lem2278247 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278248 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278249 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278248 h1) (fun h1 : term411 = True => @lem2278247)). Qed.
Lemma lem2278250 : term411 = True.
Proof. exact (EQ_MP (@lem2278249) (@lem2278247)). Qed.
Lemma lem2278251 : term410 = True.
Proof. exact (TRANS (@lem2278246) (@lem2278250)). Qed.
Lemma lem2278252 : True = term410.
Proof. exact (SYM (@lem2278251)). Qed.
Lemma lem2278253 : term410.
Proof. exact (EQ_MP (@lem2278252) (@lem0)). Qed.
Lemma lem2278254 : term552.
Proof. exact (@lem2278243 (@lem2278253)). Qed.
Lemma lem2278256 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278257 : term410 = term411.
Proof. exact (@lem2278256 (NUMERAL 0) term400). Qed.
Lemma lem2278258 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278259 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278260 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278259 h1) (fun h1 : term411 = True => @lem2278258)). Qed.
Lemma lem2278261 : term411 = True.
Proof. exact (EQ_MP (@lem2278260) (@lem2278258)). Qed.
Lemma lem2278262 : term410 = True.
Proof. exact (TRANS (@lem2278257) (@lem2278261)). Qed.
Lemma lem2278263 : True = term410.
Proof. exact (SYM (@lem2278262)). Qed.
Lemma lem2278264 : term410.
Proof. exact (EQ_MP (@lem2278263) (@lem0)). Qed.
Lemma lem2278265 : term550 = term553.
Proof. exact (@lem2278254 (@lem2278264)). Qed.
Lemma lem2278267 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278268 : term432 = term408.
Proof. exact (@lem2278267 term400). Qed.
Lemma lem2278270 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278271 : term432 = term408.
Proof. exact (@lem2278270 term400). Qed.
Lemma lem2278272 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278273 : term554 = term548.
Proof. exact (MK_COMB (@lem2278272) (@lem2278271)). Qed.
Lemma lem2278274 : term553 = term547.
Proof. exact (MK_COMB (@lem2278273) (@lem2278268)). Qed.
Lemma lem2278276 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278277 : term547 = term555.
Proof. exact (@lem2278276 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2278278 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2278279 : term547 = False.
Proof. exact (TRANS (@lem2278277) (@lem2278278)). Qed.
Lemma lem2278280 : term553 = False.
Proof. exact (TRANS (@lem2278274) (@lem2278279)). Qed.
Lemma lem2278281 : term550 = False.
Proof. exact (TRANS (@lem2278265) (@lem2278280)). Qed.
Lemma lem2278282 : term547 = False.
Proof. exact (TRANS (@lem2278242) (@lem2278281)). Qed.
Lemma lem2278283 : term531 = False.
Proof. exact (TRANS (@lem2278233) (@lem2278282)). Qed.
Lemma lem2278284 (d : nat) (h1 : term630 d) : False.
Proof. exact (EQ_MP (@lem2278283) (@lem2278229 d h1)). Qed.
Lemma lem2278285 (d : nat) (h1 : term630 d) : term630 d.
Proof. exact (h1). Qed.
Lemma lem2278287 (d : nat) (h1 : term630 d) : term531.
Proof. exact (proj1 (@lem2278285 d h1)). Qed.
Lemma lem2278290 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2278291 : term531 = term547.
Proof. exact (@lem2278290 term408 term408). Qed.
Lemma lem2278293 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278294 : term408 = term435.
Proof. exact (@lem2278293 (NUMERAL 0)). Qed.
Lemma lem2278296 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278297 : term408 = term435.
Proof. exact (@lem2278296 (NUMERAL 0)). Qed.
Lemma lem2278298 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278299 : term548 = term549.
Proof. exact (MK_COMB (@lem2278298) (@lem2278297)). Qed.
Lemma lem2278300 : term547 = term550.
Proof. exact (MK_COMB (@lem2278299) (@lem2278294)). Qed.
Lemma lem2278301 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2278303 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278304 : term410 = term411.
Proof. exact (@lem2278303 (NUMERAL 0) term400). Qed.
Lemma lem2278305 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278306 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278307 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278306 h1) (fun h1 : term411 = True => @lem2278305)). Qed.
Lemma lem2278308 : term411 = True.
Proof. exact (EQ_MP (@lem2278307) (@lem2278305)). Qed.
Lemma lem2278309 : term410 = True.
Proof. exact (TRANS (@lem2278304) (@lem2278308)). Qed.
Lemma lem2278310 : True = term410.
Proof. exact (SYM (@lem2278309)). Qed.
Lemma lem2278311 : term410.
Proof. exact (EQ_MP (@lem2278310) (@lem0)). Qed.
Lemma lem2278312 : term552.
Proof. exact (@lem2278301 (@lem2278311)). Qed.
Lemma lem2278314 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278315 : term410 = term411.
Proof. exact (@lem2278314 (NUMERAL 0) term400). Qed.
Lemma lem2278316 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278317 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278318 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278317 h1) (fun h1 : term411 = True => @lem2278316)). Qed.
Lemma lem2278319 : term411 = True.
Proof. exact (EQ_MP (@lem2278318) (@lem2278316)). Qed.
Lemma lem2278320 : term410 = True.
Proof. exact (TRANS (@lem2278315) (@lem2278319)). Qed.
Lemma lem2278321 : True = term410.
Proof. exact (SYM (@lem2278320)). Qed.
Lemma lem2278322 : term410.
Proof. exact (EQ_MP (@lem2278321) (@lem0)). Qed.
Lemma lem2278323 : term550 = term553.
Proof. exact (@lem2278312 (@lem2278322)). Qed.
Lemma lem2278325 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278326 : term432 = term408.
Proof. exact (@lem2278325 term400). Qed.
Lemma lem2278328 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278329 : term432 = term408.
Proof. exact (@lem2278328 term400). Qed.
Lemma lem2278330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278331 : term554 = term548.
Proof. exact (MK_COMB (@lem2278330) (@lem2278329)). Qed.
Lemma lem2278332 : term553 = term547.
Proof. exact (MK_COMB (@lem2278331) (@lem2278326)). Qed.
Lemma lem2278334 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278335 : term547 = term555.
Proof. exact (@lem2278334 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2278336 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2278337 : term547 = False.
Proof. exact (TRANS (@lem2278335) (@lem2278336)). Qed.
Lemma lem2278338 : term553 = False.
Proof. exact (TRANS (@lem2278332) (@lem2278337)). Qed.
Lemma lem2278339 : term550 = False.
Proof. exact (TRANS (@lem2278323) (@lem2278338)). Qed.
Lemma lem2278340 : term547 = False.
Proof. exact (TRANS (@lem2278300) (@lem2278339)). Qed.
Lemma lem2278341 : term531 = False.
Proof. exact (TRANS (@lem2278291) (@lem2278340)). Qed.
Lemma lem2278342 (d : nat) (h1 : term630 d) : False.
Proof. exact (EQ_MP (@lem2278341) (@lem2278287 d h1)). Qed.
Lemma lem2278343 (d : nat) (h1 : term626 d) : False.
Proof. exact (or_elim (@lem2278226 d h1) (fun h0 : term630 d => @lem2278284 d h0) (fun h0 : term630 d => @lem2278342 d h0)). Qed.
Lemma lem2278344 (d : nat) (h1 : term624 d) : term624 d.
Proof. exact (h1). Qed.
Lemma lem2278345 (d : nat) (h1 : term631 d) : term631 d.
Proof. exact (h1). Qed.
Lemma lem2278347 (d : nat) (h1 : term631 d) : term531.
Proof. exact (proj1 (@lem2278345 d h1)). Qed.
Lemma lem2278350 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2278351 : term531 = term547.
Proof. exact (@lem2278350 term408 term408). Qed.
Lemma lem2278353 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278354 : term408 = term435.
Proof. exact (@lem2278353 (NUMERAL 0)). Qed.
Lemma lem2278356 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278357 : term408 = term435.
Proof. exact (@lem2278356 (NUMERAL 0)). Qed.
Lemma lem2278358 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278359 : term548 = term549.
Proof. exact (MK_COMB (@lem2278358) (@lem2278357)). Qed.
Lemma lem2278360 : term547 = term550.
Proof. exact (MK_COMB (@lem2278359) (@lem2278354)). Qed.
Lemma lem2278361 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2278363 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278364 : term410 = term411.
Proof. exact (@lem2278363 (NUMERAL 0) term400). Qed.
Lemma lem2278365 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278366 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278367 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278366 h1) (fun h1 : term411 = True => @lem2278365)). Qed.
Lemma lem2278368 : term411 = True.
Proof. exact (EQ_MP (@lem2278367) (@lem2278365)). Qed.
Lemma lem2278369 : term410 = True.
Proof. exact (TRANS (@lem2278364) (@lem2278368)). Qed.
Lemma lem2278370 : True = term410.
Proof. exact (SYM (@lem2278369)). Qed.
Lemma lem2278371 : term410.
Proof. exact (EQ_MP (@lem2278370) (@lem0)). Qed.
Lemma lem2278372 : term552.
Proof. exact (@lem2278361 (@lem2278371)). Qed.
Lemma lem2278374 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278375 : term410 = term411.
Proof. exact (@lem2278374 (NUMERAL 0) term400). Qed.
Lemma lem2278376 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278377 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278378 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278377 h1) (fun h1 : term411 = True => @lem2278376)). Qed.
Lemma lem2278379 : term411 = True.
Proof. exact (EQ_MP (@lem2278378) (@lem2278376)). Qed.
Lemma lem2278380 : term410 = True.
Proof. exact (TRANS (@lem2278375) (@lem2278379)). Qed.
Lemma lem2278381 : True = term410.
Proof. exact (SYM (@lem2278380)). Qed.
Lemma lem2278382 : term410.
Proof. exact (EQ_MP (@lem2278381) (@lem0)). Qed.
Lemma lem2278383 : term550 = term553.
Proof. exact (@lem2278372 (@lem2278382)). Qed.
Lemma lem2278385 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278386 : term432 = term408.
Proof. exact (@lem2278385 term400). Qed.
Lemma lem2278388 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278389 : term432 = term408.
Proof. exact (@lem2278388 term400). Qed.
Lemma lem2278390 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278391 : term554 = term548.
Proof. exact (MK_COMB (@lem2278390) (@lem2278389)). Qed.
Lemma lem2278392 : term553 = term547.
Proof. exact (MK_COMB (@lem2278391) (@lem2278386)). Qed.
Lemma lem2278394 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278395 : term547 = term555.
Proof. exact (@lem2278394 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2278396 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2278397 : term547 = False.
Proof. exact (TRANS (@lem2278395) (@lem2278396)). Qed.
Lemma lem2278398 : term553 = False.
Proof. exact (TRANS (@lem2278392) (@lem2278397)). Qed.
Lemma lem2278399 : term550 = False.
Proof. exact (TRANS (@lem2278383) (@lem2278398)). Qed.
Lemma lem2278400 : term547 = False.
Proof. exact (TRANS (@lem2278360) (@lem2278399)). Qed.
Lemma lem2278401 : term531 = False.
Proof. exact (TRANS (@lem2278351) (@lem2278400)). Qed.
Lemma lem2278402 (d : nat) (h1 : term631 d) : False.
Proof. exact (EQ_MP (@lem2278401) (@lem2278347 d h1)). Qed.
Lemma lem2278403 (d : nat) (h1 : term631 d) : term631 d.
Proof. exact (h1). Qed.
Lemma lem2278405 (d : nat) (h1 : term631 d) : term531.
Proof. exact (proj1 (@lem2278403 d h1)). Qed.
Lemma lem2278408 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2278409 : term531 = term547.
Proof. exact (@lem2278408 term408 term408). Qed.
Lemma lem2278411 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278412 : term408 = term435.
Proof. exact (@lem2278411 (NUMERAL 0)). Qed.
Lemma lem2278414 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278415 : term408 = term435.
Proof. exact (@lem2278414 (NUMERAL 0)). Qed.
Lemma lem2278416 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278417 : term548 = term549.
Proof. exact (MK_COMB (@lem2278416) (@lem2278415)). Qed.
Lemma lem2278418 : term547 = term550.
Proof. exact (MK_COMB (@lem2278417) (@lem2278412)). Qed.
Lemma lem2278419 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2278421 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278422 : term410 = term411.
Proof. exact (@lem2278421 (NUMERAL 0) term400). Qed.
Lemma lem2278423 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278424 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278425 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278424 h1) (fun h1 : term411 = True => @lem2278423)). Qed.
Lemma lem2278426 : term411 = True.
Proof. exact (EQ_MP (@lem2278425) (@lem2278423)). Qed.
Lemma lem2278427 : term410 = True.
Proof. exact (TRANS (@lem2278422) (@lem2278426)). Qed.
Lemma lem2278428 : True = term410.
Proof. exact (SYM (@lem2278427)). Qed.
Lemma lem2278429 : term410.
Proof. exact (EQ_MP (@lem2278428) (@lem0)). Qed.
Lemma lem2278430 : term552.
Proof. exact (@lem2278419 (@lem2278429)). Qed.
Lemma lem2278432 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278433 : term410 = term411.
Proof. exact (@lem2278432 (NUMERAL 0) term400). Qed.
Lemma lem2278434 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278435 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278436 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278435 h1) (fun h1 : term411 = True => @lem2278434)). Qed.
Lemma lem2278437 : term411 = True.
Proof. exact (EQ_MP (@lem2278436) (@lem2278434)). Qed.
Lemma lem2278438 : term410 = True.
Proof. exact (TRANS (@lem2278433) (@lem2278437)). Qed.
Lemma lem2278439 : True = term410.
Proof. exact (SYM (@lem2278438)). Qed.
Lemma lem2278440 : term410.
Proof. exact (EQ_MP (@lem2278439) (@lem0)). Qed.
Lemma lem2278441 : term550 = term553.
Proof. exact (@lem2278430 (@lem2278440)). Qed.
Lemma lem2278443 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278444 : term432 = term408.
Proof. exact (@lem2278443 term400). Qed.
Lemma lem2278446 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278447 : term432 = term408.
Proof. exact (@lem2278446 term400). Qed.
Lemma lem2278448 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2278449 : term554 = term548.
Proof. exact (MK_COMB (@lem2278448) (@lem2278447)). Qed.
Lemma lem2278450 : term553 = term547.
Proof. exact (MK_COMB (@lem2278449) (@lem2278444)). Qed.
Lemma lem2278452 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278453 : term547 = term555.
Proof. exact (@lem2278452 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2278454 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2278455 : term547 = False.
Proof. exact (TRANS (@lem2278453) (@lem2278454)). Qed.
Lemma lem2278456 : term553 = False.
Proof. exact (TRANS (@lem2278450) (@lem2278455)). Qed.
Lemma lem2278457 : term550 = False.
Proof. exact (TRANS (@lem2278441) (@lem2278456)). Qed.
Lemma lem2278458 : term547 = False.
Proof. exact (TRANS (@lem2278418) (@lem2278457)). Qed.
Lemma lem2278459 : term531 = False.
Proof. exact (TRANS (@lem2278409) (@lem2278458)). Qed.
Lemma lem2278460 (d : nat) (h1 : term631 d) : False.
Proof. exact (EQ_MP (@lem2278459) (@lem2278405 d h1)). Qed.
Lemma lem2278461 (d : nat) (h1 : term624 d) : False.
Proof. exact (or_elim (@lem2278344 d h1) (fun h0 : term631 d => @lem2278402 d h0) (fun h0 : term631 d => @lem2278460 d h0)). Qed.
Lemma lem2278462 (d : nat) (h1 : term629 d) : False.
Proof. exact (or_elim (@lem2278225 d h1) (fun h0 : term626 d => @lem2278343 d h0) (fun h0 : term624 d => @lem2278461 d h0)). Qed.
Lemma lem2278464 (d : nat) (h1 : term629 d) : term629 d.
Proof. exact (h1). Qed.
Lemma lem2278465 (d : nat) (h1 : term629 d) : (term629 d) = False.
Proof. exact (prop_ext (fun h2 : term629 d => @lem2278462 d h1) (fun h2 : False => @lem2278464 d h1)). Qed.
Lemma lem2278466 (d : nat) (h1 : term629 d) : False.
Proof. exact (EQ_MP (@lem2278465 d h1) (@lem2278464 d h1)). Qed.
Lemma lem2278467 (m : nat) (d : nat) (h1 : term635 m d) : term635 m d.
Proof. exact (h1). Qed.
Lemma lem2278468 (m : nat) (d : nat) (h1 : term635 m d) : term629 d.
Proof. exact (EQ_MP (@lem2278203 m d) (@lem2278467 m d h1)). Qed.
Lemma lem2278469 (m : nat) (d : nat) (h1 : term635 m d) : (term629 d) = False.
Proof. exact (prop_ext (fun h2 : term629 d => @lem2278466 d h2) (fun h2 : False => @lem2278468 m d h1)). Qed.
Lemma lem2278470 (m : nat) (d : nat) (h1 : term635 m d) : False.
Proof. exact (EQ_MP (@lem2278469 m d h1) (@lem2278468 m d h1)). Qed.
Lemma lem2278471 (m : nat) (d : nat) : term661 m d.
Proof. exact (fun h0 : term635 m d => @lem2278470 m d h0). Qed.
Lemma lem2278472 (m : nat) (d : nat) : term662 m d.
Proof. exact (@lem1386578 (term663 m d)). Qed.
Lemma lem2278475 (m : nat) (d : nat) : term663 m d.
Proof. exact (@lem2278472 m d (@lem2278471 m d)). Qed.
Lemma lem2278476 (m : nat) (d : nat) : term289 m d.
Proof. exact (ex_intro (term288 m d) d (@lem2278475 m d)). Qed.
Lemma lem2278500 (n : nat) (d : nat) : (term664 n d) = (term665 n d).
Proof. exact (@lem17160 ((term316 d n) = (real_of_num d)) ((term316 d n) = (term93 d))). Qed.
Lemma lem2278501 (n : nat) (d : nat) : (term666 n d) = (term667 n d).
Proof. exact (@lem1988318 (term316 d n) (real_of_num d)). Qed.
Lemma lem2278502 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2278503 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2278510 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2278517 (n : nat) : (term93 n) = (term389 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2278518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278519 (n : nat) : (term127 n) = (term390 n).
Proof. exact (MK_COMB (@lem2278518) (@lem2278517 n)). Qed.
Lemma lem2278520 (n : nat) (d : nat) : (term136 n d) = (term391 n d).
Proof. exact (MK_COMB (@lem2278519 n) (@lem2278510 d)). Qed.
Lemma lem2278521 (d : nat) (n : nat) : (term391 n d) = (term391 d n).
Proof. exact (@lem1982761 (term389 d) (term389 n)). Qed.
Lemma lem2278522 (d : nat) (n : nat) : (term136 n d) = (term391 d n).
Proof. exact (TRANS (@lem2278520 n d) (@lem2278521 d n)). Qed.
Lemma lem2278523 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278524 (d : nat) (n : nat) : (term315 n d) = (term668 d n).
Proof. exact (MK_COMB (@lem2278523) (@lem2278522 d n)). Qed.
Lemma lem2278525 (d : nat) (n : nat) : (term316 d n) = (term669 d n).
Proof. exact (MK_COMB (@lem2278524 d n) (@lem2278503 n)). Qed.
Lemma lem2278526 (d : nat) (n : nat) : (term669 d n) = (term670 d n).
Proof. exact (@lem1982755 (term389 d) (term389 n) (real_of_num n)). Qed.
Lemma lem2278527 (n : nat) : (term518 n) = (term395 n).
Proof. exact (@lem1982713 term396 (real_of_num n)). Qed.
Lemma lem2278529 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278530 : term398 = term399.
Proof. exact (@lem2278529 term400). Qed.
Lemma lem2278532 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278533 : term396 = term402.
Proof. exact (@lem2278532 term400). Qed.
Lemma lem2278534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278535 : term403 = term404.
Proof. exact (MK_COMB (@lem2278534) (@lem2278533)). Qed.
Lemma lem2278536 : term405 = term406.
Proof. exact (MK_COMB (@lem2278535) (@lem2278530)). Qed.
Lemma lem2278537 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2278539 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278540 : term410 = term411.
Proof. exact (@lem2278539 (NUMERAL 0) term400). Qed.
Lemma lem2278541 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278542 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278543 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278542 h1) (fun h1 : term411 = True => @lem2278541)). Qed.
Lemma lem2278544 : term411 = True.
Proof. exact (EQ_MP (@lem2278543) (@lem2278541)). Qed.
Lemma lem2278545 : term410 = True.
Proof. exact (TRANS (@lem2278540) (@lem2278544)). Qed.
Lemma lem2278546 : True = term410.
Proof. exact (SYM (@lem2278545)). Qed.
Lemma lem2278547 : term410.
Proof. exact (EQ_MP (@lem2278546) (@lem0)). Qed.
Lemma lem2278548 : term413.
Proof. exact (@lem2278537 (@lem2278547)). Qed.
Lemma lem2278550 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278551 : term410 = term411.
Proof. exact (@lem2278550 (NUMERAL 0) term400). Qed.
Lemma lem2278552 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278553 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278554 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278553 h1) (fun h1 : term411 = True => @lem2278552)). Qed.
Lemma lem2278555 : term411 = True.
Proof. exact (EQ_MP (@lem2278554) (@lem2278552)). Qed.
Lemma lem2278556 : term410 = True.
Proof. exact (TRANS (@lem2278551) (@lem2278555)). Qed.
Lemma lem2278557 : True = term410.
Proof. exact (SYM (@lem2278556)). Qed.
Lemma lem2278558 : term410.
Proof. exact (EQ_MP (@lem2278557) (@lem0)). Qed.
Lemma lem2278559 : term414.
Proof. exact (@lem2278548 (@lem2278558)). Qed.
Lemma lem2278561 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278562 : term410 = term411.
Proof. exact (@lem2278561 (NUMERAL 0) term400). Qed.
Lemma lem2278563 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278564 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278565 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278564 h1) (fun h1 : term411 = True => @lem2278563)). Qed.
Lemma lem2278566 : term411 = True.
Proof. exact (EQ_MP (@lem2278565) (@lem2278563)). Qed.
Lemma lem2278567 : term410 = True.
Proof. exact (TRANS (@lem2278562) (@lem2278566)). Qed.
Lemma lem2278568 : True = term410.
Proof. exact (SYM (@lem2278567)). Qed.
Lemma lem2278569 : term410.
Proof. exact (EQ_MP (@lem2278568) (@lem0)). Qed.
Lemma lem2278570 : term415.
Proof. exact (@lem2278559 (@lem2278569)). Qed.
Lemma lem2278572 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278573 : term418 = term419.
Proof. exact (@lem2278572 term400 term400). Qed.
Lemma lem2278574 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278575 : term421 = term400.
Proof. exact (EQ_MP (@lem2278574) (@lem940073)). Qed.
Lemma lem2278576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278577 : term419 = term398.
Proof. exact (MK_COMB (@lem2278576) (@lem2278575)). Qed.
Lemma lem2278578 : term418 = term398.
Proof. exact (TRANS (@lem2278573) (@lem2278577)). Qed.
Lemma lem2278580 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278581 : term424 = term425.
Proof. exact (@lem2278580 term400 term400). Qed.
Lemma lem2278582 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278583 : term421 = term400.
Proof. exact (EQ_MP (@lem2278582) (@lem940073)). Qed.
Lemma lem2278584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278585 : term419 = term398.
Proof. exact (MK_COMB (@lem2278584) (@lem2278583)). Qed.
Lemma lem2278586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278587 : term425 = term396.
Proof. exact (MK_COMB (@lem2278586) (@lem2278585)). Qed.
Lemma lem2278588 : term424 = term396.
Proof. exact (TRANS (@lem2278581) (@lem2278587)). Qed.
Lemma lem2278589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278590 : term426 = term403.
Proof. exact (MK_COMB (@lem2278589) (@lem2278588)). Qed.
Lemma lem2278591 : term427 = term405.
Proof. exact (MK_COMB (@lem2278590) (@lem2278578)). Qed.
Lemma lem2278593 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2278594 : term405 = term408.
Proof. exact (@lem2278593 term400). Qed.
Lemma lem2278595 : term427 = term408.
Proof. exact (TRANS (@lem2278591) (@lem2278594)). Qed.
Lemma lem2278596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278597 : term429 = term430.
Proof. exact (MK_COMB (@lem2278596) (@lem2278595)). Qed.
Lemma lem2278598 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2278599 : term431 = term432.
Proof. exact (MK_COMB (@lem2278597) (@lem2278598)). Qed.
Lemma lem2278601 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278602 : term432 = term408.
Proof. exact (@lem2278601 term400). Qed.
Lemma lem2278603 : term431 = term408.
Proof. exact (TRANS (@lem2278599) (@lem2278602)). Qed.
Lemma lem2278605 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278606 : term418 = term419.
Proof. exact (@lem2278605 term400 term400). Qed.
Lemma lem2278607 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278608 : term421 = term400.
Proof. exact (EQ_MP (@lem2278607) (@lem940073)). Qed.
Lemma lem2278609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278610 : term419 = term398.
Proof. exact (MK_COMB (@lem2278609) (@lem2278608)). Qed.
Lemma lem2278611 : term418 = term398.
Proof. exact (TRANS (@lem2278606) (@lem2278610)). Qed.
Lemma lem2278612 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2278613 : term434 = term432.
Proof. exact (MK_COMB (@lem2278612) (@lem2278611)). Qed.
Lemma lem2278615 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278616 : term432 = term408.
Proof. exact (@lem2278615 term400). Qed.
Lemma lem2278617 : term434 = term408.
Proof. exact (TRANS (@lem2278613) (@lem2278616)). Qed.
Lemma lem2278618 : term408 = term434.
Proof. exact (SYM (@lem2278617)). Qed.
Lemma lem2278619 : term431 = term434.
Proof. exact (TRANS (@lem2278603) (@lem2278618)). Qed.
Lemma lem2278620 : term406 = term435.
Proof. exact (@lem2278570 (@lem2278619)). Qed.
Lemma lem2278621 : term405 = term435.
Proof. exact (TRANS (@lem2278536) (@lem2278620)). Qed.
Lemma lem2278623 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2278624 : term435 = term408.
Proof. exact (@lem2278623 term408). Qed.
Lemma lem2278625 : term405 = term408.
Proof. exact (TRANS (@lem2278621) (@lem2278624)). Qed.
Lemma lem2278626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278627 : term437 = term430.
Proof. exact (MK_COMB (@lem2278626) (@lem2278625)). Qed.
Lemma lem2278628 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2278629 (n : nat) : (term395 n) = (term433 n).
Proof. exact (MK_COMB (@lem2278627) (@lem2278628 n)). Qed.
Lemma lem2278630 (n : nat) : (term518 n) = (term433 n).
Proof. exact (TRANS (@lem2278527 n) (@lem2278629 n)). Qed.
Lemma lem2278631 (n : nat) : (term433 n) = term408.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2278632 (n : nat) : (term518 n) = term408.
Proof. exact (TRANS (@lem2278630 n) (@lem2278631 n)). Qed.
Lemma lem2278633 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2278634 (n : nat) (d : nat) : (term670 d n) = (term438 d).
Proof. exact (MK_COMB (@lem2278633 d) (@lem2278632 n)). Qed.
Lemma lem2278635 (n : nat) (d : nat) : (term669 d n) = (term438 d).
Proof. exact (TRANS (@lem2278526 d n) (@lem2278634 n d)). Qed.
Lemma lem2278636 (d : nat) : (term438 d) = (term389 d).
Proof. exact (@lem1982723 (term389 d)). Qed.
Lemma lem2278637 (n : nat) (d : nat) : (term669 d n) = (term389 d).
Proof. exact (TRANS (@lem2278635 n d) (@lem2278636 d)). Qed.
Lemma lem2278638 (n : nat) (d : nat) : (term316 d n) = (term389 d).
Proof. exact (TRANS (@lem2278525 d n) (@lem2278637 n d)). Qed.
Lemma lem2278639 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2278640 (n : nat) (d : nat) : (term671 d n) = (term440 d).
Proof. exact (MK_COMB (@lem2278639) (@lem2278638 n d)). Qed.
Lemma lem2278641 (n : nat) (d : nat) : (term672 n d) = (term442 d).
Proof. exact (MK_COMB (@lem2278640 n d) (@lem2278502 d)). Qed.
Lemma lem2278642 (d : nat) : (term442 d) = (term443 d).
Proof. exact (@lem1982792 (term389 d) (real_of_num d)). Qed.
Lemma lem2278646 (d : nat) : (term443 d) = (term444 d).
Proof. exact (@lem1982711 term396 term396 (real_of_num d)). Qed.
Lemma lem2278648 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278649 : term396 = term402.
Proof. exact (@lem2278648 term400). Qed.
Lemma lem2278651 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278652 : term396 = term402.
Proof. exact (@lem2278651 term400). Qed.
Lemma lem2278653 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278654 : term403 = term404.
Proof. exact (MK_COMB (@lem2278653) (@lem2278652)). Qed.
Lemma lem2278655 : term445 = term446.
Proof. exact (MK_COMB (@lem2278654) (@lem2278649)). Qed.
Lemma lem2278656 : term447.
Proof. exact (@lem1981473 term396 term398 term396 term398 term448 term398). Qed.
Lemma lem2278658 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278659 : term410 = term411.
Proof. exact (@lem2278658 (NUMERAL 0) term400). Qed.
Lemma lem2278660 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278661 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278662 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278661 h1) (fun h1 : term411 = True => @lem2278660)). Qed.
Lemma lem2278663 : term411 = True.
Proof. exact (EQ_MP (@lem2278662) (@lem2278660)). Qed.
Lemma lem2278664 : term410 = True.
Proof. exact (TRANS (@lem2278659) (@lem2278663)). Qed.
Lemma lem2278665 : True = term410.
Proof. exact (SYM (@lem2278664)). Qed.
Lemma lem2278666 : term410.
Proof. exact (EQ_MP (@lem2278665) (@lem0)). Qed.
Lemma lem2278667 : term449.
Proof. exact (@lem2278656 (@lem2278666)). Qed.
Lemma lem2278669 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278670 : term410 = term411.
Proof. exact (@lem2278669 (NUMERAL 0) term400). Qed.
Lemma lem2278671 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278672 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278673 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278672 h1) (fun h1 : term411 = True => @lem2278671)). Qed.
Lemma lem2278674 : term411 = True.
Proof. exact (EQ_MP (@lem2278673) (@lem2278671)). Qed.
Lemma lem2278675 : term410 = True.
Proof. exact (TRANS (@lem2278670) (@lem2278674)). Qed.
Lemma lem2278676 : True = term410.
Proof. exact (SYM (@lem2278675)). Qed.
Lemma lem2278677 : term410.
Proof. exact (EQ_MP (@lem2278676) (@lem0)). Qed.
Lemma lem2278678 : term450.
Proof. exact (@lem2278667 (@lem2278677)). Qed.
Lemma lem2278680 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278681 : term410 = term411.
Proof. exact (@lem2278680 (NUMERAL 0) term400). Qed.
Lemma lem2278682 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278683 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278684 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278683 h1) (fun h1 : term411 = True => @lem2278682)). Qed.
Lemma lem2278685 : term411 = True.
Proof. exact (EQ_MP (@lem2278684) (@lem2278682)). Qed.
Lemma lem2278686 : term410 = True.
Proof. exact (TRANS (@lem2278681) (@lem2278685)). Qed.
Lemma lem2278687 : True = term410.
Proof. exact (SYM (@lem2278686)). Qed.
Lemma lem2278688 : term410.
Proof. exact (EQ_MP (@lem2278687) (@lem0)). Qed.
Lemma lem2278689 : term451.
Proof. exact (@lem2278678 (@lem2278688)). Qed.
Lemma lem2278691 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278692 : term424 = term425.
Proof. exact (@lem2278691 term400 term400). Qed.
Lemma lem2278693 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278694 : term421 = term400.
Proof. exact (EQ_MP (@lem2278693) (@lem940073)). Qed.
Lemma lem2278695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278696 : term419 = term398.
Proof. exact (MK_COMB (@lem2278695) (@lem2278694)). Qed.
Lemma lem2278697 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278698 : term425 = term396.
Proof. exact (MK_COMB (@lem2278697) (@lem2278696)). Qed.
Lemma lem2278699 : term424 = term396.
Proof. exact (TRANS (@lem2278692) (@lem2278698)). Qed.
Lemma lem2278701 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278702 : term424 = term425.
Proof. exact (@lem2278701 term400 term400). Qed.
Lemma lem2278703 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278704 : term421 = term400.
Proof. exact (EQ_MP (@lem2278703) (@lem940073)). Qed.
Lemma lem2278705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278706 : term419 = term398.
Proof. exact (MK_COMB (@lem2278705) (@lem2278704)). Qed.
Lemma lem2278707 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278708 : term425 = term396.
Proof. exact (MK_COMB (@lem2278707) (@lem2278706)). Qed.
Lemma lem2278709 : term424 = term396.
Proof. exact (TRANS (@lem2278702) (@lem2278708)). Qed.
Lemma lem2278710 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278711 : term426 = term403.
Proof. exact (MK_COMB (@lem2278710) (@lem2278709)). Qed.
Lemma lem2278712 : term452 = term445.
Proof. exact (MK_COMB (@lem2278711) (@lem2278699)). Qed.
Lemma lem2278713 : term445 = term453.
Proof. exact (@lem1367763 term400 term400). Qed.
Lemma lem2278714 : term454 = term455.
Proof. exact (@lem706885). Qed.
Lemma lem2278715 : (term454 = term455) = (term456 = term457).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term455). Qed.
Lemma lem2278716 : term456 = term457.
Proof. exact (EQ_MP (@lem2278715) (@lem2278714)). Qed.
Lemma lem2278717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278718 : term458 = term459.
Proof. exact (MK_COMB (@lem2278717) (@lem2278716)). Qed.
Lemma lem2278719 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278720 : term453 = term448.
Proof. exact (MK_COMB (@lem2278719) (@lem2278718)). Qed.
Lemma lem2278721 : term445 = term448.
Proof. exact (TRANS (@lem2278713) (@lem2278720)). Qed.
Lemma lem2278722 : term452 = term448.
Proof. exact (TRANS (@lem2278712) (@lem2278721)). Qed.
Lemma lem2278723 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278724 : term460 = term461.
Proof. exact (MK_COMB (@lem2278723) (@lem2278722)). Qed.
Lemma lem2278725 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2278726 : term462 = term463.
Proof. exact (MK_COMB (@lem2278724) (@lem2278725)). Qed.
Lemma lem2278728 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278729 : term463 = term464.
Proof. exact (@lem2278728 term457 term400). Qed.
Lemma lem2278730 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2278731 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2278732 : term466 = term457.
Proof. exact (EQ_MP (@lem2278731) (@lem2278730)). Qed.
Lemma lem2278733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278734 : term467 = term459.
Proof. exact (MK_COMB (@lem2278733) (@lem2278732)). Qed.
Lemma lem2278735 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278736 : term464 = term448.
Proof. exact (MK_COMB (@lem2278735) (@lem2278734)). Qed.
Lemma lem2278737 : term463 = term448.
Proof. exact (TRANS (@lem2278729) (@lem2278736)). Qed.
Lemma lem2278738 : term462 = term448.
Proof. exact (TRANS (@lem2278726) (@lem2278737)). Qed.
Lemma lem2278740 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278741 : term418 = term419.
Proof. exact (@lem2278740 term400 term400). Qed.
Lemma lem2278742 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278743 : term421 = term400.
Proof. exact (EQ_MP (@lem2278742) (@lem940073)). Qed.
Lemma lem2278744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278745 : term419 = term398.
Proof. exact (MK_COMB (@lem2278744) (@lem2278743)). Qed.
Lemma lem2278746 : term418 = term398.
Proof. exact (TRANS (@lem2278741) (@lem2278745)). Qed.
Lemma lem2278747 : term461 = term461.
Proof. exact (eq_refl term461). Qed.
Lemma lem2278748 : term468 = term463.
Proof. exact (MK_COMB (@lem2278747) (@lem2278746)). Qed.
Lemma lem2278750 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278751 : term463 = term464.
Proof. exact (@lem2278750 term457 term400). Qed.
Lemma lem2278752 : term465 = term455.
Proof. exact (@lem996237 term455). Qed.
Lemma lem2278753 : (term465 = term455) = (term466 = term457).
Proof. exact (@lem1007663 term455 (BIT1 0) term455). Qed.
Lemma lem2278754 : term466 = term457.
Proof. exact (EQ_MP (@lem2278753) (@lem2278752)). Qed.
Lemma lem2278755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278756 : term467 = term459.
Proof. exact (MK_COMB (@lem2278755) (@lem2278754)). Qed.
Lemma lem2278757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278758 : term464 = term448.
Proof. exact (MK_COMB (@lem2278757) (@lem2278756)). Qed.
Lemma lem2278759 : term463 = term448.
Proof. exact (TRANS (@lem2278751) (@lem2278758)). Qed.
Lemma lem2278760 : term468 = term448.
Proof. exact (TRANS (@lem2278748) (@lem2278759)). Qed.
Lemma lem2278761 : term448 = term468.
Proof. exact (SYM (@lem2278760)). Qed.
Lemma lem2278762 : term462 = term468.
Proof. exact (TRANS (@lem2278738) (@lem2278761)). Qed.
Lemma lem2278763 : term446 = term469.
Proof. exact (@lem2278689 (@lem2278762)). Qed.
Lemma lem2278764 : term445 = term469.
Proof. exact (TRANS (@lem2278655) (@lem2278763)). Qed.
Lemma lem2278766 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2278767 : term469 = term448.
Proof. exact (@lem2278766 term448). Qed.
Lemma lem2278768 : term445 = term448.
Proof. exact (TRANS (@lem2278764) (@lem2278767)). Qed.
Lemma lem2278769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278770 : term470 = term461.
Proof. exact (MK_COMB (@lem2278769) (@lem2278768)). Qed.
Lemma lem2278771 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2278772 (d : nat) : (term444 d) = (term471 d).
Proof. exact (MK_COMB (@lem2278770) (@lem2278771 d)). Qed.
Lemma lem2278774 (d : nat) : (term443 d) = (term471 d).
Proof. exact (TRANS (@lem2278646 d) (@lem2278772 d)). Qed.
Lemma lem2278775 (d : nat) : (term442 d) = (term471 d).
Proof. exact (TRANS (@lem2278642 d) (@lem2278774 d)). Qed.
Lemma lem2278776 (n : nat) (d : nat) : (term672 n d) = (term471 d).
Proof. exact (TRANS (@lem2278641 n d) (@lem2278775 d)). Qed.
Lemma lem2278777 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278778 (n : nat) (d : nat) : (term673 n d) = (term473 d).
Proof. exact (MK_COMB (@lem2278777) (@lem2278776 n d)). Qed.
Lemma lem2278779 (d : nat) : (term473 d) = (term474 d).
Proof. exact (@lem1982785 (term471 d)). Qed.
Lemma lem2278780 (d : nat) : (term474 d) = (term475 d).
Proof. exact (@lem1982749 term396 term448 (real_of_num d)). Qed.
Lemma lem2278782 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278783 : term448 = term469.
Proof. exact (@lem2278782 term457). Qed.
Lemma lem2278785 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278786 : term396 = term402.
Proof. exact (@lem2278785 term400). Qed.
Lemma lem2278787 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278788 : term476 = term477.
Proof. exact (MK_COMB (@lem2278787) (@lem2278786)). Qed.
Lemma lem2278789 : term478 = term479.
Proof. exact (MK_COMB (@lem2278788) (@lem2278783)). Qed.
Lemma lem2278790 : term479 = term480.
Proof. exact (@lem1981613 term396 term448 term398 term398). Qed.
Lemma lem2278792 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278793 : term418 = term419.
Proof. exact (@lem2278792 term400 term400). Qed.
Lemma lem2278794 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278795 : term421 = term400.
Proof. exact (EQ_MP (@lem2278794) (@lem940073)). Qed.
Lemma lem2278796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278797 : term419 = term398.
Proof. exact (MK_COMB (@lem2278796) (@lem2278795)). Qed.
Lemma lem2278798 : term418 = term398.
Proof. exact (TRANS (@lem2278793) (@lem2278797)). Qed.
Lemma lem2278800 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2278801 : term478 = term482.
Proof. exact (@lem2278800 term400 term457). Qed.
Lemma lem2278802 : term483 = term455.
Proof. exact (@lem996238 term455). Qed.
Lemma lem2278803 : (term483 = term455) = (term484 = term457).
Proof. exact (@lem1007663 (BIT1 0) term455 term455). Qed.
Lemma lem2278804 : term484 = term457.
Proof. exact (EQ_MP (@lem2278803) (@lem2278802)). Qed.
Lemma lem2278805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278806 : term482 = term459.
Proof. exact (MK_COMB (@lem2278805) (@lem2278804)). Qed.
Lemma lem2278807 : term478 = term459.
Proof. exact (TRANS (@lem2278801) (@lem2278806)). Qed.
Lemma lem2278808 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2278809 : term485 = term486.
Proof. exact (MK_COMB (@lem2278808) (@lem2278807)). Qed.
Lemma lem2278810 : term480 = term487.
Proof. exact (MK_COMB (@lem2278809) (@lem2278798)). Qed.
Lemma lem2278811 : term479 = term487.
Proof. exact (TRANS (@lem2278790) (@lem2278810)). Qed.
Lemma lem2278812 : term478 = term487.
Proof. exact (TRANS (@lem2278789) (@lem2278811)). Qed.
Lemma lem2278814 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2278815 : term487 = term459.
Proof. exact (@lem2278814 term459). Qed.
Lemma lem2278816 : term478 = term459.
Proof. exact (TRANS (@lem2278812) (@lem2278815)). Qed.
Lemma lem2278817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278818 : term488 = term489.
Proof. exact (MK_COMB (@lem2278817) (@lem2278816)). Qed.
Lemma lem2278819 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2278820 (d : nat) : (term475 d) = (term490 d).
Proof. exact (MK_COMB (@lem2278818) (@lem2278819 d)). Qed.
Lemma lem2278821 (d : nat) : (term474 d) = (term490 d).
Proof. exact (TRANS (@lem2278780 d) (@lem2278820 d)). Qed.
Lemma lem2278822 (d : nat) : (term473 d) = (term490 d).
Proof. exact (TRANS (@lem2278779 d) (@lem2278821 d)). Qed.
Lemma lem2278823 (n : nat) (d : nat) : (term674 n d) = (term674 n d).
Proof. exact (eq_refl (term674 n d)). Qed.
Lemma lem2278824 (n : nat) (d : nat) : ((term673 n d) = (term473 d)) = ((term673 n d) = (term490 d)).
Proof. exact (MK_COMB (@lem2278823 n d) (@lem2278822 d)). Qed.
Lemma lem2278825 (n : nat) (d : nat) : (term673 n d) = (term490 d).
Proof. exact (EQ_MP (@lem2278824 n d) (@lem2278778 n d)). Qed.
Lemma lem2278826 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2278827 (n : nat) (d : nat) : (term675 n d) = (term493 d).
Proof. exact (MK_COMB (@lem2278826) (@lem2278825 n d)). Qed.
Lemma lem2278828 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2278829 (n : nat) (d : nat) : (term676 n d) = (term495 d).
Proof. exact (MK_COMB (@lem2278827 n d) (@lem2278828)). Qed.
Lemma lem2278830 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2278831 (n : nat) (d : nat) : (term677 n d) = (term497 d).
Proof. exact (MK_COMB (@lem2278830) (@lem2278776 n d)). Qed.
Lemma lem2278832 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2278833 (n : nat) (d : nat) : (term678 n d) = (term499 d).
Proof. exact (MK_COMB (@lem2278831 n d) (@lem2278832)). Qed.
Lemma lem2278834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2278835 (n : nat) (d : nat) : (term679 n d) = (term501 d).
Proof. exact (MK_COMB (@lem2278834) (@lem2278833 n d)). Qed.
Lemma lem2278836 (n : nat) (d : nat) : (term667 n d) = (term502 d).
Proof. exact (MK_COMB (@lem2278835 n d) (@lem2278829 n d)). Qed.
Lemma lem2278837 (n : nat) (d : nat) : (term666 n d) = (term502 d).
Proof. exact (TRANS (@lem2278501 n d) (@lem2278836 n d)). Qed.
Lemma lem2278838 (n : nat) (d : nat) : (term680 n d) = (term681 n d).
Proof. exact (@lem1988318 (term316 d n) (term93 d)). Qed.
Lemma lem2278845 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2278846 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2278853 (d : nat) : (term93 d) = (term389 d).
Proof. exact (@lem1982785 (real_of_num d)). Qed.
Lemma lem2278860 (n : nat) : (term93 n) = (term389 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2278861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278862 (n : nat) : (term127 n) = (term390 n).
Proof. exact (MK_COMB (@lem2278861) (@lem2278860 n)). Qed.
Lemma lem2278863 (n : nat) (d : nat) : (term136 n d) = (term391 n d).
Proof. exact (MK_COMB (@lem2278862 n) (@lem2278853 d)). Qed.
Lemma lem2278864 (d : nat) (n : nat) : (term391 n d) = (term391 d n).
Proof. exact (@lem1982761 (term389 d) (term389 n)). Qed.
Lemma lem2278865 (d : nat) (n : nat) : (term136 n d) = (term391 d n).
Proof. exact (TRANS (@lem2278863 n d) (@lem2278864 d n)). Qed.
Lemma lem2278866 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278867 (d : nat) (n : nat) : (term315 n d) = (term668 d n).
Proof. exact (MK_COMB (@lem2278866) (@lem2278865 d n)). Qed.
Lemma lem2278868 (d : nat) (n : nat) : (term316 d n) = (term669 d n).
Proof. exact (MK_COMB (@lem2278867 d n) (@lem2278846 n)). Qed.
Lemma lem2278869 (d : nat) (n : nat) : (term669 d n) = (term670 d n).
Proof. exact (@lem1982755 (term389 d) (term389 n) (real_of_num n)). Qed.
Lemma lem2278870 (n : nat) : (term518 n) = (term395 n).
Proof. exact (@lem1982713 term396 (real_of_num n)). Qed.
Lemma lem2278872 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2278873 : term398 = term399.
Proof. exact (@lem2278872 term400). Qed.
Lemma lem2278875 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278876 : term396 = term402.
Proof. exact (@lem2278875 term400). Qed.
Lemma lem2278877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278878 : term403 = term404.
Proof. exact (MK_COMB (@lem2278877) (@lem2278876)). Qed.
Lemma lem2278879 : term405 = term406.
Proof. exact (MK_COMB (@lem2278878) (@lem2278873)). Qed.
Lemma lem2278880 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2278882 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278883 : term410 = term411.
Proof. exact (@lem2278882 (NUMERAL 0) term400). Qed.
Lemma lem2278884 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278885 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278886 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278885 h1) (fun h1 : term411 = True => @lem2278884)). Qed.
Lemma lem2278887 : term411 = True.
Proof. exact (EQ_MP (@lem2278886) (@lem2278884)). Qed.
Lemma lem2278888 : term410 = True.
Proof. exact (TRANS (@lem2278883) (@lem2278887)). Qed.
Lemma lem2278889 : True = term410.
Proof. exact (SYM (@lem2278888)). Qed.
Lemma lem2278890 : term410.
Proof. exact (EQ_MP (@lem2278889) (@lem0)). Qed.
Lemma lem2278891 : term413.
Proof. exact (@lem2278880 (@lem2278890)). Qed.
Lemma lem2278893 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278894 : term410 = term411.
Proof. exact (@lem2278893 (NUMERAL 0) term400). Qed.
Lemma lem2278895 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278896 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278897 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278896 h1) (fun h1 : term411 = True => @lem2278895)). Qed.
Lemma lem2278898 : term411 = True.
Proof. exact (EQ_MP (@lem2278897) (@lem2278895)). Qed.
Lemma lem2278899 : term410 = True.
Proof. exact (TRANS (@lem2278894) (@lem2278898)). Qed.
Lemma lem2278900 : True = term410.
Proof. exact (SYM (@lem2278899)). Qed.
Lemma lem2278901 : term410.
Proof. exact (EQ_MP (@lem2278900) (@lem0)). Qed.
Lemma lem2278902 : term414.
Proof. exact (@lem2278891 (@lem2278901)). Qed.
Lemma lem2278904 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2278905 : term410 = term411.
Proof. exact (@lem2278904 (NUMERAL 0) term400). Qed.
Lemma lem2278906 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2278907 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2278908 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2278907 h1) (fun h1 : term411 = True => @lem2278906)). Qed.
Lemma lem2278909 : term411 = True.
Proof. exact (EQ_MP (@lem2278908) (@lem2278906)). Qed.
Lemma lem2278910 : term410 = True.
Proof. exact (TRANS (@lem2278905) (@lem2278909)). Qed.
Lemma lem2278911 : True = term410.
Proof. exact (SYM (@lem2278910)). Qed.
Lemma lem2278912 : term410.
Proof. exact (EQ_MP (@lem2278911) (@lem0)). Qed.
Lemma lem2278913 : term415.
Proof. exact (@lem2278902 (@lem2278912)). Qed.
Lemma lem2278915 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278916 : term418 = term419.
Proof. exact (@lem2278915 term400 term400). Qed.
Lemma lem2278917 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278918 : term421 = term400.
Proof. exact (EQ_MP (@lem2278917) (@lem940073)). Qed.
Lemma lem2278919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278920 : term419 = term398.
Proof. exact (MK_COMB (@lem2278919) (@lem2278918)). Qed.
Lemma lem2278921 : term418 = term398.
Proof. exact (TRANS (@lem2278916) (@lem2278920)). Qed.
Lemma lem2278923 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2278924 : term424 = term425.
Proof. exact (@lem2278923 term400 term400). Qed.
Lemma lem2278925 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278926 : term421 = term400.
Proof. exact (EQ_MP (@lem2278925) (@lem940073)). Qed.
Lemma lem2278927 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278928 : term419 = term398.
Proof. exact (MK_COMB (@lem2278927) (@lem2278926)). Qed.
Lemma lem2278929 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2278930 : term425 = term396.
Proof. exact (MK_COMB (@lem2278929) (@lem2278928)). Qed.
Lemma lem2278931 : term424 = term396.
Proof. exact (TRANS (@lem2278924) (@lem2278930)). Qed.
Lemma lem2278932 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2278933 : term426 = term403.
Proof. exact (MK_COMB (@lem2278932) (@lem2278931)). Qed.
Lemma lem2278934 : term427 = term405.
Proof. exact (MK_COMB (@lem2278933) (@lem2278921)). Qed.
Lemma lem2278936 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2278937 : term405 = term408.
Proof. exact (@lem2278936 term400). Qed.
Lemma lem2278938 : term427 = term408.
Proof. exact (TRANS (@lem2278934) (@lem2278937)). Qed.
Lemma lem2278939 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278940 : term429 = term430.
Proof. exact (MK_COMB (@lem2278939) (@lem2278938)). Qed.
Lemma lem2278941 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2278942 : term431 = term432.
Proof. exact (MK_COMB (@lem2278940) (@lem2278941)). Qed.
Lemma lem2278944 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278945 : term432 = term408.
Proof. exact (@lem2278944 term400). Qed.
Lemma lem2278946 : term431 = term408.
Proof. exact (TRANS (@lem2278942) (@lem2278945)). Qed.
Lemma lem2278948 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278949 : term418 = term419.
Proof. exact (@lem2278948 term400 term400). Qed.
Lemma lem2278950 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2278951 : term421 = term400.
Proof. exact (EQ_MP (@lem2278950) (@lem940073)). Qed.
Lemma lem2278952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2278953 : term419 = term398.
Proof. exact (MK_COMB (@lem2278952) (@lem2278951)). Qed.
Lemma lem2278954 : term418 = term398.
Proof. exact (TRANS (@lem2278949) (@lem2278953)). Qed.
Lemma lem2278955 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2278956 : term434 = term432.
Proof. exact (MK_COMB (@lem2278955) (@lem2278954)). Qed.
Lemma lem2278958 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2278959 : term432 = term408.
Proof. exact (@lem2278958 term400). Qed.
Lemma lem2278960 : term434 = term408.
Proof. exact (TRANS (@lem2278956) (@lem2278959)). Qed.
Lemma lem2278961 : term408 = term434.
Proof. exact (SYM (@lem2278960)). Qed.
Lemma lem2278962 : term431 = term434.
Proof. exact (TRANS (@lem2278946) (@lem2278961)). Qed.
Lemma lem2278963 : term406 = term435.
Proof. exact (@lem2278913 (@lem2278962)). Qed.
Lemma lem2278964 : term405 = term435.
Proof. exact (TRANS (@lem2278879) (@lem2278963)). Qed.
Lemma lem2278966 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2278967 : term435 = term408.
Proof. exact (@lem2278966 term408). Qed.
Lemma lem2278968 : term405 = term408.
Proof. exact (TRANS (@lem2278964) (@lem2278967)). Qed.
Lemma lem2278969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278970 : term437 = term430.
Proof. exact (MK_COMB (@lem2278969) (@lem2278968)). Qed.
Lemma lem2278971 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2278972 (n : nat) : (term395 n) = (term433 n).
Proof. exact (MK_COMB (@lem2278970) (@lem2278971 n)). Qed.
Lemma lem2278973 (n : nat) : (term518 n) = (term433 n).
Proof. exact (TRANS (@lem2278870 n) (@lem2278972 n)). Qed.
Lemma lem2278974 (n : nat) : (term433 n) = term408.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2278975 (n : nat) : (term518 n) = term408.
Proof. exact (TRANS (@lem2278973 n) (@lem2278974 n)). Qed.
Lemma lem2278976 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2278977 (n : nat) (d : nat) : (term670 d n) = (term438 d).
Proof. exact (MK_COMB (@lem2278976 d) (@lem2278975 n)). Qed.
Lemma lem2278978 (n : nat) (d : nat) : (term669 d n) = (term438 d).
Proof. exact (TRANS (@lem2278869 d n) (@lem2278977 n d)). Qed.
Lemma lem2278979 (d : nat) : (term438 d) = (term389 d).
Proof. exact (@lem1982723 (term389 d)). Qed.
Lemma lem2278980 (n : nat) (d : nat) : (term669 d n) = (term389 d).
Proof. exact (TRANS (@lem2278978 n d) (@lem2278979 d)). Qed.
Lemma lem2278981 (n : nat) (d : nat) : (term316 d n) = (term389 d).
Proof. exact (TRANS (@lem2278868 d n) (@lem2278980 n d)). Qed.
Lemma lem2278982 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2278983 (n : nat) (d : nat) : (term671 d n) = (term440 d).
Proof. exact (MK_COMB (@lem2278982) (@lem2278981 n d)). Qed.
Lemma lem2278984 (n : nat) (d : nat) : (term682 n d) = (term506 d).
Proof. exact (MK_COMB (@lem2278983 n d) (@lem2278845 d)). Qed.
Lemma lem2278985 (d : nat) : (term506 d) = (term507 d).
Proof. exact (@lem1982792 (term389 d) (term389 d)). Qed.
Lemma lem2278986 (d : nat) : (term508 d) = (term509 d).
Proof. exact (@lem1982749 term396 term396 (real_of_num d)). Qed.
Lemma lem2278988 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278989 : term396 = term402.
Proof. exact (@lem2278988 term400). Qed.
Lemma lem2278991 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2278992 : term396 = term402.
Proof. exact (@lem2278991 term400). Qed.
Lemma lem2278993 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2278994 : term476 = term477.
Proof. exact (MK_COMB (@lem2278993) (@lem2278992)). Qed.
Lemma lem2278995 : term510 = term511.
Proof. exact (MK_COMB (@lem2278994) (@lem2278989)). Qed.
Lemma lem2278996 : term511 = term512.
Proof. exact (@lem1981613 term396 term396 term398 term398). Qed.
Lemma lem2278998 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2278999 : term418 = term419.
Proof. exact (@lem2278998 term400 term400). Qed.
Lemma lem2279000 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279001 : term421 = term400.
Proof. exact (EQ_MP (@lem2279000) (@lem940073)). Qed.
Lemma lem2279002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279003 : term419 = term398.
Proof. exact (MK_COMB (@lem2279002) (@lem2279001)). Qed.
Lemma lem2279004 : term418 = term398.
Proof. exact (TRANS (@lem2278999) (@lem2279003)). Qed.
Lemma lem2279006 (m : nat) (n : nat) : (term481 m n) = (term417 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2279007 : term510 = term419.
Proof. exact (@lem2279006 term400 term400). Qed.
Lemma lem2279008 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279009 : term421 = term400.
Proof. exact (EQ_MP (@lem2279008) (@lem940073)). Qed.
Lemma lem2279010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279011 : term419 = term398.
Proof. exact (MK_COMB (@lem2279010) (@lem2279009)). Qed.
Lemma lem2279012 : term510 = term398.
Proof. exact (TRANS (@lem2279007) (@lem2279011)). Qed.
Lemma lem2279013 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2279014 : term513 = term514.
Proof. exact (MK_COMB (@lem2279013) (@lem2279012)). Qed.
Lemma lem2279015 : term512 = term399.
Proof. exact (MK_COMB (@lem2279014) (@lem2279004)). Qed.
Lemma lem2279016 : term511 = term399.
Proof. exact (TRANS (@lem2278996) (@lem2279015)). Qed.
Lemma lem2279017 : term510 = term399.
Proof. exact (TRANS (@lem2278995) (@lem2279016)). Qed.
Lemma lem2279019 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2279020 : term399 = term398.
Proof. exact (@lem2279019 term398). Qed.
Lemma lem2279021 : term510 = term398.
Proof. exact (TRANS (@lem2279017) (@lem2279020)). Qed.
Lemma lem2279022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2279023 : term515 = term516.
Proof. exact (MK_COMB (@lem2279022) (@lem2279021)). Qed.
Lemma lem2279024 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2279025 (d : nat) : (term509 d) = (term517 d).
Proof. exact (MK_COMB (@lem2279023) (@lem2279024 d)). Qed.
Lemma lem2279026 (d : nat) : (term508 d) = (term517 d).
Proof. exact (TRANS (@lem2278986 d) (@lem2279025 d)). Qed.
Lemma lem2279027 (d : nat) : (term517 d) = (real_of_num d).
Proof. exact (@lem1982709 (real_of_num d)). Qed.
Lemma lem2279028 (d : nat) : (term508 d) = (real_of_num d).
Proof. exact (TRANS (@lem2279026 d) (@lem2279027 d)). Qed.
Lemma lem2279029 (d : nat) : (term390 d) = (term390 d).
Proof. exact (eq_refl (term390 d)). Qed.
Lemma lem2279030 (d : nat) : (term507 d) = (term518 d).
Proof. exact (MK_COMB (@lem2279029 d) (@lem2279028 d)). Qed.
Lemma lem2279031 (d : nat) : (term518 d) = (term395 d).
Proof. exact (@lem1982713 term396 (real_of_num d)). Qed.
Lemma lem2279033 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279034 : term398 = term399.
Proof. exact (@lem2279033 term400). Qed.
Lemma lem2279036 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2279037 : term396 = term402.
Proof. exact (@lem2279036 term400). Qed.
Lemma lem2279038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2279039 : term403 = term404.
Proof. exact (MK_COMB (@lem2279038) (@lem2279037)). Qed.
Lemma lem2279040 : term405 = term406.
Proof. exact (MK_COMB (@lem2279039) (@lem2279034)). Qed.
Lemma lem2279041 : term407.
Proof. exact (@lem1981473 term396 term398 term398 term398 term408 term398). Qed.
Lemma lem2279043 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279044 : term410 = term411.
Proof. exact (@lem2279043 (NUMERAL 0) term400). Qed.
Lemma lem2279045 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279046 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279047 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279046 h1) (fun h1 : term411 = True => @lem2279045)). Qed.
Lemma lem2279048 : term411 = True.
Proof. exact (EQ_MP (@lem2279047) (@lem2279045)). Qed.
Lemma lem2279049 : term410 = True.
Proof. exact (TRANS (@lem2279044) (@lem2279048)). Qed.
Lemma lem2279050 : True = term410.
Proof. exact (SYM (@lem2279049)). Qed.
Lemma lem2279051 : term410.
Proof. exact (EQ_MP (@lem2279050) (@lem0)). Qed.
Lemma lem2279052 : term413.
Proof. exact (@lem2279041 (@lem2279051)). Qed.
Lemma lem2279054 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279055 : term410 = term411.
Proof. exact (@lem2279054 (NUMERAL 0) term400). Qed.
Lemma lem2279056 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279057 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279058 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279057 h1) (fun h1 : term411 = True => @lem2279056)). Qed.
Lemma lem2279059 : term411 = True.
Proof. exact (EQ_MP (@lem2279058) (@lem2279056)). Qed.
Lemma lem2279060 : term410 = True.
Proof. exact (TRANS (@lem2279055) (@lem2279059)). Qed.
Lemma lem2279061 : True = term410.
Proof. exact (SYM (@lem2279060)). Qed.
Lemma lem2279062 : term410.
Proof. exact (EQ_MP (@lem2279061) (@lem0)). Qed.
Lemma lem2279063 : term414.
Proof. exact (@lem2279052 (@lem2279062)). Qed.
Lemma lem2279065 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279066 : term410 = term411.
Proof. exact (@lem2279065 (NUMERAL 0) term400). Qed.
Lemma lem2279067 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279068 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279069 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279068 h1) (fun h1 : term411 = True => @lem2279067)). Qed.
Lemma lem2279070 : term411 = True.
Proof. exact (EQ_MP (@lem2279069) (@lem2279067)). Qed.
Lemma lem2279071 : term410 = True.
Proof. exact (TRANS (@lem2279066) (@lem2279070)). Qed.
Lemma lem2279072 : True = term410.
Proof. exact (SYM (@lem2279071)). Qed.
Lemma lem2279073 : term410.
Proof. exact (EQ_MP (@lem2279072) (@lem0)). Qed.
Lemma lem2279074 : term415.
Proof. exact (@lem2279063 (@lem2279073)). Qed.
Lemma lem2279076 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2279077 : term418 = term419.
Proof. exact (@lem2279076 term400 term400). Qed.
Lemma lem2279078 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279079 : term421 = term400.
Proof. exact (EQ_MP (@lem2279078) (@lem940073)). Qed.
Lemma lem2279080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279081 : term419 = term398.
Proof. exact (MK_COMB (@lem2279080) (@lem2279079)). Qed.
Lemma lem2279082 : term418 = term398.
Proof. exact (TRANS (@lem2279077) (@lem2279081)). Qed.
Lemma lem2279084 (m : nat) (n : nat) : (term422 m n) = (term423 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2279085 : term424 = term425.
Proof. exact (@lem2279084 term400 term400). Qed.
Lemma lem2279086 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279087 : term421 = term400.
Proof. exact (EQ_MP (@lem2279086) (@lem940073)). Qed.
Lemma lem2279088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279089 : term419 = term398.
Proof. exact (MK_COMB (@lem2279088) (@lem2279087)). Qed.
Lemma lem2279090 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2279091 : term425 = term396.
Proof. exact (MK_COMB (@lem2279090) (@lem2279089)). Qed.
Lemma lem2279092 : term424 = term396.
Proof. exact (TRANS (@lem2279085) (@lem2279091)). Qed.
Lemma lem2279093 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2279094 : term426 = term403.
Proof. exact (MK_COMB (@lem2279093) (@lem2279092)). Qed.
Lemma lem2279095 : term427 = term405.
Proof. exact (MK_COMB (@lem2279094) (@lem2279082)). Qed.
Lemma lem2279097 (m : nat) : (term428 m) = term408.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2279098 : term405 = term408.
Proof. exact (@lem2279097 term400). Qed.
Lemma lem2279099 : term427 = term408.
Proof. exact (TRANS (@lem2279095) (@lem2279098)). Qed.
Lemma lem2279100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2279101 : term429 = term430.
Proof. exact (MK_COMB (@lem2279100) (@lem2279099)). Qed.
Lemma lem2279102 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem2279103 : term431 = term432.
Proof. exact (MK_COMB (@lem2279101) (@lem2279102)). Qed.
Lemma lem2279105 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279106 : term432 = term408.
Proof. exact (@lem2279105 term400). Qed.
Lemma lem2279107 : term431 = term408.
Proof. exact (TRANS (@lem2279103) (@lem2279106)). Qed.
Lemma lem2279109 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2279110 : term418 = term419.
Proof. exact (@lem2279109 term400 term400). Qed.
Lemma lem2279111 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279112 : term421 = term400.
Proof. exact (EQ_MP (@lem2279111) (@lem940073)). Qed.
Lemma lem2279113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279114 : term419 = term398.
Proof. exact (MK_COMB (@lem2279113) (@lem2279112)). Qed.
Lemma lem2279115 : term418 = term398.
Proof. exact (TRANS (@lem2279110) (@lem2279114)). Qed.
Lemma lem2279116 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem2279117 : term434 = term432.
Proof. exact (MK_COMB (@lem2279116) (@lem2279115)). Qed.
Lemma lem2279119 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279120 : term432 = term408.
Proof. exact (@lem2279119 term400). Qed.
Lemma lem2279121 : term434 = term408.
Proof. exact (TRANS (@lem2279117) (@lem2279120)). Qed.
Lemma lem2279122 : term408 = term434.
Proof. exact (SYM (@lem2279121)). Qed.
Lemma lem2279123 : term431 = term434.
Proof. exact (TRANS (@lem2279107) (@lem2279122)). Qed.
Lemma lem2279124 : term406 = term435.
Proof. exact (@lem2279074 (@lem2279123)). Qed.
Lemma lem2279125 : term405 = term435.
Proof. exact (TRANS (@lem2279040) (@lem2279124)). Qed.
Lemma lem2279127 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2279128 : term435 = term408.
Proof. exact (@lem2279127 term408). Qed.
Lemma lem2279129 : term405 = term408.
Proof. exact (TRANS (@lem2279125) (@lem2279128)). Qed.
Lemma lem2279130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2279131 : term437 = term430.
Proof. exact (MK_COMB (@lem2279130) (@lem2279129)). Qed.
Lemma lem2279132 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem2279133 (d : nat) : (term395 d) = (term433 d).
Proof. exact (MK_COMB (@lem2279131) (@lem2279132 d)). Qed.
Lemma lem2279134 (d : nat) : (term518 d) = (term433 d).
Proof. exact (TRANS (@lem2279031 d) (@lem2279133 d)). Qed.
Lemma lem2279135 (d : nat) : (term433 d) = term408.
Proof. exact (@lem1982719 (real_of_num d)). Qed.
Lemma lem2279136 (d : nat) : (term518 d) = term408.
Proof. exact (TRANS (@lem2279134 d) (@lem2279135 d)). Qed.
Lemma lem2279137 (d : nat) : (term507 d) = term408.
Proof. exact (TRANS (@lem2279030 d) (@lem2279136 d)). Qed.
Lemma lem2279138 (d : nat) : (term506 d) = term408.
Proof. exact (TRANS (@lem2278985 d) (@lem2279137 d)). Qed.
Lemma lem2279139 (n : nat) (d : nat) : (term682 n d) = term408.
Proof. exact (TRANS (@lem2278984 n d) (@lem2279138 d)). Qed.
Lemma lem2279140 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2279141 (n : nat) (d : nat) : (term683 n d) = term520.
Proof. exact (MK_COMB (@lem2279140) (@lem2279139 n d)). Qed.
Lemma lem2279142 : term520 = term521.
Proof. exact (@lem1982785 term408). Qed.
Lemma lem2279144 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279145 : term408 = term435.
Proof. exact (@lem2279144 (NUMERAL 0)). Qed.
Lemma lem2279147 (x : nat) : (term93 x) = (term401 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2279148 : term396 = term402.
Proof. exact (@lem2279147 term400). Qed.
Lemma lem2279149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2279150 : term476 = term477.
Proof. exact (MK_COMB (@lem2279149) (@lem2279148)). Qed.
Lemma lem2279151 : term521 = term522.
Proof. exact (MK_COMB (@lem2279150) (@lem2279145)). Qed.
Lemma lem2279152 : term522 = term523.
Proof. exact (@lem1981613 term396 term408 term398 term398). Qed.
Lemma lem2279154 (m : nat) (n : nat) : (term416 m n) = (term417 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2279155 : term418 = term419.
Proof. exact (@lem2279154 term400 term400). Qed.
Lemma lem2279156 : (term420 = (BIT1 0)) = (term421 = term400).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2279157 : term421 = term400.
Proof. exact (EQ_MP (@lem2279156) (@lem940073)). Qed.
Lemma lem2279158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2279159 : term419 = term398.
Proof. exact (MK_COMB (@lem2279158) (@lem2279157)). Qed.
Lemma lem2279160 : term418 = term398.
Proof. exact (TRANS (@lem2279155) (@lem2279159)). Qed.
Lemma lem2279162 (x : nat) : (term524 x) = term408.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2279163 : term521 = term408.
Proof. exact (@lem2279162 term400). Qed.
Lemma lem2279164 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2279165 : term525 = term526.
Proof. exact (MK_COMB (@lem2279164) (@lem2279163)). Qed.
Lemma lem2279166 : term523 = term435.
Proof. exact (MK_COMB (@lem2279165) (@lem2279160)). Qed.
Lemma lem2279167 : term522 = term435.
Proof. exact (TRANS (@lem2279152) (@lem2279166)). Qed.
Lemma lem2279168 : term521 = term435.
Proof. exact (TRANS (@lem2279151) (@lem2279167)). Qed.
Lemma lem2279170 (x : real) : (term436 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2279171 : term435 = term408.
Proof. exact (@lem2279170 term408). Qed.
Lemma lem2279172 : term521 = term408.
Proof. exact (TRANS (@lem2279168) (@lem2279171)). Qed.
Lemma lem2279173 : term520 = term408.
Proof. exact (TRANS (@lem2279142) (@lem2279172)). Qed.
Lemma lem2279174 (n : nat) (d : nat) : (term684 n d) = (term684 n d).
Proof. exact (eq_refl (term684 n d)). Qed.
Lemma lem2279175 (n : nat) (d : nat) : ((term683 n d) = term520) = ((term683 n d) = term408).
Proof. exact (MK_COMB (@lem2279174 n d) (@lem2279173)). Qed.
Lemma lem2279176 (n : nat) (d : nat) : (term683 n d) = term408.
Proof. exact (EQ_MP (@lem2279175 n d) (@lem2279141 n d)). Qed.
Lemma lem2279177 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2279178 (n : nat) (d : nat) : (term685 n d) = term529.
Proof. exact (MK_COMB (@lem2279177) (@lem2279176 n d)). Qed.
Lemma lem2279179 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2279180 (n : nat) (d : nat) : (term686 n d) = term531.
Proof. exact (MK_COMB (@lem2279178 n d) (@lem2279179)). Qed.
Lemma lem2279181 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2279182 (n : nat) (d : nat) : (term687 n d) = term529.
Proof. exact (MK_COMB (@lem2279181) (@lem2279139 n d)). Qed.
Lemma lem2279183 : term408 = term408.
Proof. exact (eq_refl term408). Qed.
Lemma lem2279184 (n : nat) (d : nat) : (term688 n d) = term531.
Proof. exact (MK_COMB (@lem2279182 n d) (@lem2279183)). Qed.
Lemma lem2279185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2279186 (n : nat) (d : nat) : (term689 n d) = term535.
Proof. exact (MK_COMB (@lem2279185) (@lem2279184 n d)). Qed.
Lemma lem2279187 (n : nat) (d : nat) : (term681 n d) = term536.
Proof. exact (MK_COMB (@lem2279186 n d) (@lem2279180 n d)). Qed.
Lemma lem2279188 (n : nat) (d : nat) : (term680 n d) = term536.
Proof. exact (TRANS (@lem2278838 n d) (@lem2279187 n d)). Qed.
Lemma lem2279189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2279190 (n : nat) (d : nat) : (term690 n d) = (term538 d).
Proof. exact (MK_COMB (@lem2279189) (@lem2278837 n d)). Qed.
Lemma lem2279191 (n : nat) (d : nat) : (term665 n d) = (term539 d).
Proof. exact (MK_COMB (@lem2279190 n d) (@lem2279188 n d)). Qed.
Lemma lem2279198 (n : nat) (d : nat) : (term664 n d) = (term539 d).
Proof. exact (TRANS (@lem2278500 n d) (@lem2279191 n d)). Qed.
Lemma lem2279212 (d : nat) : (term539 d) = (term540 d).
Proof. exact (@lem19158 term531 (term502 d) term531). Qed.
Lemma lem2279219 (d : nat) : (term541 d) = (term542 d).
Proof. exact (@lem19367 (term499 d) (term495 d) term531). Qed.
Lemma lem2279226 (d : nat) : (term541 d) = (term542 d).
Proof. exact (@lem19367 (term499 d) (term495 d) term531). Qed.
Lemma lem2279227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2279228 (d : nat) : (term543 d) = (term544 d).
Proof. exact (MK_COMB (@lem2279227) (@lem2279226 d)). Qed.
Lemma lem2279229 (d : nat) : (term540 d) = (term545 d).
Proof. exact (MK_COMB (@lem2279228 d) (@lem2279219 d)). Qed.
Lemma lem2279231 (d : nat) : (term539 d) = (term545 d).
Proof. exact (TRANS (@lem2279212 d) (@lem2279229 d)). Qed.
Lemma lem2279232 (n : nat) (d : nat) : (term664 n d) = (term545 d).
Proof. exact (TRANS (@lem2279198 n d) (@lem2279231 d)). Qed.
Lemma lem2279254 (d : nat) (h1 : term545 d) : term545 d.
Proof. exact (h1). Qed.
Lemma lem2279255 (d : nat) (h1 : term542 d) : term542 d.
Proof. exact (h1). Qed.
Lemma lem2279256 (d : nat) (h1 : term546 d) : term546 d.
Proof. exact (h1). Qed.
Lemma lem2279257 (d : nat) (h1 : term546 d) : term531.
Proof. exact (proj2 (@lem2279256 d h1)). Qed.
Lemma lem2279261 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2279262 : term531 = term547.
Proof. exact (@lem2279261 term408 term408). Qed.
Lemma lem2279264 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279265 : term408 = term435.
Proof. exact (@lem2279264 (NUMERAL 0)). Qed.
Lemma lem2279267 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279268 : term408 = term435.
Proof. exact (@lem2279267 (NUMERAL 0)). Qed.
Lemma lem2279269 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279270 : term548 = term549.
Proof. exact (MK_COMB (@lem2279269) (@lem2279268)). Qed.
Lemma lem2279271 : term547 = term550.
Proof. exact (MK_COMB (@lem2279270) (@lem2279265)). Qed.
Lemma lem2279272 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2279274 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279275 : term410 = term411.
Proof. exact (@lem2279274 (NUMERAL 0) term400). Qed.
Lemma lem2279276 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279277 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279278 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279277 h1) (fun h1 : term411 = True => @lem2279276)). Qed.
Lemma lem2279279 : term411 = True.
Proof. exact (EQ_MP (@lem2279278) (@lem2279276)). Qed.
Lemma lem2279280 : term410 = True.
Proof. exact (TRANS (@lem2279275) (@lem2279279)). Qed.
Lemma lem2279281 : True = term410.
Proof. exact (SYM (@lem2279280)). Qed.
Lemma lem2279282 : term410.
Proof. exact (EQ_MP (@lem2279281) (@lem0)). Qed.
Lemma lem2279283 : term552.
Proof. exact (@lem2279272 (@lem2279282)). Qed.
Lemma lem2279285 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279286 : term410 = term411.
Proof. exact (@lem2279285 (NUMERAL 0) term400). Qed.
Lemma lem2279287 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279288 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279289 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279288 h1) (fun h1 : term411 = True => @lem2279287)). Qed.
Lemma lem2279290 : term411 = True.
Proof. exact (EQ_MP (@lem2279289) (@lem2279287)). Qed.
Lemma lem2279291 : term410 = True.
Proof. exact (TRANS (@lem2279286) (@lem2279290)). Qed.
Lemma lem2279292 : True = term410.
Proof. exact (SYM (@lem2279291)). Qed.
Lemma lem2279293 : term410.
Proof. exact (EQ_MP (@lem2279292) (@lem0)). Qed.
Lemma lem2279294 : term550 = term553.
Proof. exact (@lem2279283 (@lem2279293)). Qed.
Lemma lem2279296 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279297 : term432 = term408.
Proof. exact (@lem2279296 term400). Qed.
Lemma lem2279299 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279300 : term432 = term408.
Proof. exact (@lem2279299 term400). Qed.
Lemma lem2279301 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279302 : term554 = term548.
Proof. exact (MK_COMB (@lem2279301) (@lem2279300)). Qed.
Lemma lem2279303 : term553 = term547.
Proof. exact (MK_COMB (@lem2279302) (@lem2279297)). Qed.
Lemma lem2279305 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279306 : term547 = term555.
Proof. exact (@lem2279305 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2279307 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2279308 : term547 = False.
Proof. exact (TRANS (@lem2279306) (@lem2279307)). Qed.
Lemma lem2279309 : term553 = False.
Proof. exact (TRANS (@lem2279303) (@lem2279308)). Qed.
Lemma lem2279310 : term550 = False.
Proof. exact (TRANS (@lem2279294) (@lem2279309)). Qed.
Lemma lem2279311 : term547 = False.
Proof. exact (TRANS (@lem2279271) (@lem2279310)). Qed.
Lemma lem2279312 : term531 = False.
Proof. exact (TRANS (@lem2279262) (@lem2279311)). Qed.
Lemma lem2279313 (d : nat) (h1 : term546 d) : False.
Proof. exact (EQ_MP (@lem2279312) (@lem2279257 d h1)). Qed.
Lemma lem2279314 (d : nat) (h1 : term556 d) : term556 d.
Proof. exact (h1). Qed.
Lemma lem2279315 (d : nat) (h1 : term556 d) : term531.
Proof. exact (proj2 (@lem2279314 d h1)). Qed.
Lemma lem2279319 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2279320 : term531 = term547.
Proof. exact (@lem2279319 term408 term408). Qed.
Lemma lem2279322 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279323 : term408 = term435.
Proof. exact (@lem2279322 (NUMERAL 0)). Qed.
Lemma lem2279325 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279326 : term408 = term435.
Proof. exact (@lem2279325 (NUMERAL 0)). Qed.
Lemma lem2279327 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279328 : term548 = term549.
Proof. exact (MK_COMB (@lem2279327) (@lem2279326)). Qed.
Lemma lem2279329 : term547 = term550.
Proof. exact (MK_COMB (@lem2279328) (@lem2279323)). Qed.
Lemma lem2279330 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2279332 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279333 : term410 = term411.
Proof. exact (@lem2279332 (NUMERAL 0) term400). Qed.
Lemma lem2279334 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279335 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279336 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279335 h1) (fun h1 : term411 = True => @lem2279334)). Qed.
Lemma lem2279337 : term411 = True.
Proof. exact (EQ_MP (@lem2279336) (@lem2279334)). Qed.
Lemma lem2279338 : term410 = True.
Proof. exact (TRANS (@lem2279333) (@lem2279337)). Qed.
Lemma lem2279339 : True = term410.
Proof. exact (SYM (@lem2279338)). Qed.
Lemma lem2279340 : term410.
Proof. exact (EQ_MP (@lem2279339) (@lem0)). Qed.
Lemma lem2279341 : term552.
Proof. exact (@lem2279330 (@lem2279340)). Qed.
Lemma lem2279343 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279344 : term410 = term411.
Proof. exact (@lem2279343 (NUMERAL 0) term400). Qed.
Lemma lem2279345 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279346 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279347 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279346 h1) (fun h1 : term411 = True => @lem2279345)). Qed.
Lemma lem2279348 : term411 = True.
Proof. exact (EQ_MP (@lem2279347) (@lem2279345)). Qed.
Lemma lem2279349 : term410 = True.
Proof. exact (TRANS (@lem2279344) (@lem2279348)). Qed.
Lemma lem2279350 : True = term410.
Proof. exact (SYM (@lem2279349)). Qed.
Lemma lem2279351 : term410.
Proof. exact (EQ_MP (@lem2279350) (@lem0)). Qed.
Lemma lem2279352 : term550 = term553.
Proof. exact (@lem2279341 (@lem2279351)). Qed.
Lemma lem2279354 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279355 : term432 = term408.
Proof. exact (@lem2279354 term400). Qed.
Lemma lem2279357 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279358 : term432 = term408.
Proof. exact (@lem2279357 term400). Qed.
Lemma lem2279359 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279360 : term554 = term548.
Proof. exact (MK_COMB (@lem2279359) (@lem2279358)). Qed.
Lemma lem2279361 : term553 = term547.
Proof. exact (MK_COMB (@lem2279360) (@lem2279355)). Qed.
Lemma lem2279363 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279364 : term547 = term555.
Proof. exact (@lem2279363 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2279365 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2279366 : term547 = False.
Proof. exact (TRANS (@lem2279364) (@lem2279365)). Qed.
Lemma lem2279367 : term553 = False.
Proof. exact (TRANS (@lem2279361) (@lem2279366)). Qed.
Lemma lem2279368 : term550 = False.
Proof. exact (TRANS (@lem2279352) (@lem2279367)). Qed.
Lemma lem2279369 : term547 = False.
Proof. exact (TRANS (@lem2279329) (@lem2279368)). Qed.
Lemma lem2279370 : term531 = False.
Proof. exact (TRANS (@lem2279320) (@lem2279369)). Qed.
Lemma lem2279371 (d : nat) (h1 : term556 d) : False.
Proof. exact (EQ_MP (@lem2279370) (@lem2279315 d h1)). Qed.
Lemma lem2279372 (d : nat) (h1 : term542 d) : False.
Proof. exact (or_elim (@lem2279255 d h1) (fun h0 : term546 d => @lem2279313 d h0) (fun h0 : term556 d => @lem2279371 d h0)). Qed.
Lemma lem2279373 (d : nat) (h1 : term542 d) : term542 d.
Proof. exact (h1). Qed.
Lemma lem2279374 (d : nat) (h1 : term546 d) : term546 d.
Proof. exact (h1). Qed.
Lemma lem2279375 (d : nat) (h1 : term546 d) : term531.
Proof. exact (proj2 (@lem2279374 d h1)). Qed.
Lemma lem2279379 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2279380 : term531 = term547.
Proof. exact (@lem2279379 term408 term408). Qed.
Lemma lem2279382 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279383 : term408 = term435.
Proof. exact (@lem2279382 (NUMERAL 0)). Qed.
Lemma lem2279385 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279386 : term408 = term435.
Proof. exact (@lem2279385 (NUMERAL 0)). Qed.
Lemma lem2279387 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279388 : term548 = term549.
Proof. exact (MK_COMB (@lem2279387) (@lem2279386)). Qed.
Lemma lem2279389 : term547 = term550.
Proof. exact (MK_COMB (@lem2279388) (@lem2279383)). Qed.
Lemma lem2279390 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2279392 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279393 : term410 = term411.
Proof. exact (@lem2279392 (NUMERAL 0) term400). Qed.
Lemma lem2279394 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279395 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279396 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279395 h1) (fun h1 : term411 = True => @lem2279394)). Qed.
Lemma lem2279397 : term411 = True.
Proof. exact (EQ_MP (@lem2279396) (@lem2279394)). Qed.
Lemma lem2279398 : term410 = True.
Proof. exact (TRANS (@lem2279393) (@lem2279397)). Qed.
Lemma lem2279399 : True = term410.
Proof. exact (SYM (@lem2279398)). Qed.
Lemma lem2279400 : term410.
Proof. exact (EQ_MP (@lem2279399) (@lem0)). Qed.
Lemma lem2279401 : term552.
Proof. exact (@lem2279390 (@lem2279400)). Qed.
Lemma lem2279403 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279404 : term410 = term411.
Proof. exact (@lem2279403 (NUMERAL 0) term400). Qed.
Lemma lem2279405 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279406 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279407 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279406 h1) (fun h1 : term411 = True => @lem2279405)). Qed.
Lemma lem2279408 : term411 = True.
Proof. exact (EQ_MP (@lem2279407) (@lem2279405)). Qed.
Lemma lem2279409 : term410 = True.
Proof. exact (TRANS (@lem2279404) (@lem2279408)). Qed.
Lemma lem2279410 : True = term410.
Proof. exact (SYM (@lem2279409)). Qed.
Lemma lem2279411 : term410.
Proof. exact (EQ_MP (@lem2279410) (@lem0)). Qed.
Lemma lem2279412 : term550 = term553.
Proof. exact (@lem2279401 (@lem2279411)). Qed.
Lemma lem2279414 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279415 : term432 = term408.
Proof. exact (@lem2279414 term400). Qed.
Lemma lem2279417 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279418 : term432 = term408.
Proof. exact (@lem2279417 term400). Qed.
Lemma lem2279419 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279420 : term554 = term548.
Proof. exact (MK_COMB (@lem2279419) (@lem2279418)). Qed.
Lemma lem2279421 : term553 = term547.
Proof. exact (MK_COMB (@lem2279420) (@lem2279415)). Qed.
Lemma lem2279423 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279424 : term547 = term555.
Proof. exact (@lem2279423 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2279425 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2279426 : term547 = False.
Proof. exact (TRANS (@lem2279424) (@lem2279425)). Qed.
Lemma lem2279427 : term553 = False.
Proof. exact (TRANS (@lem2279421) (@lem2279426)). Qed.
Lemma lem2279428 : term550 = False.
Proof. exact (TRANS (@lem2279412) (@lem2279427)). Qed.
Lemma lem2279429 : term547 = False.
Proof. exact (TRANS (@lem2279389) (@lem2279428)). Qed.
Lemma lem2279430 : term531 = False.
Proof. exact (TRANS (@lem2279380) (@lem2279429)). Qed.
Lemma lem2279431 (d : nat) (h1 : term546 d) : False.
Proof. exact (EQ_MP (@lem2279430) (@lem2279375 d h1)). Qed.
Lemma lem2279432 (d : nat) (h1 : term556 d) : term556 d.
Proof. exact (h1). Qed.
Lemma lem2279433 (d : nat) (h1 : term556 d) : term531.
Proof. exact (proj2 (@lem2279432 d h1)). Qed.
Lemma lem2279437 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2279438 : term531 = term547.
Proof. exact (@lem2279437 term408 term408). Qed.
Lemma lem2279440 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279441 : term408 = term435.
Proof. exact (@lem2279440 (NUMERAL 0)). Qed.
Lemma lem2279443 (x : nat) : (real_of_num x) = (term397 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2279444 : term408 = term435.
Proof. exact (@lem2279443 (NUMERAL 0)). Qed.
Lemma lem2279445 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279446 : term548 = term549.
Proof. exact (MK_COMB (@lem2279445) (@lem2279444)). Qed.
Lemma lem2279447 : term547 = term550.
Proof. exact (MK_COMB (@lem2279446) (@lem2279441)). Qed.
Lemma lem2279448 : term551.
Proof. exact (@lem1980255 term408 term398 term408 term398). Qed.
Lemma lem2279450 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279451 : term410 = term411.
Proof. exact (@lem2279450 (NUMERAL 0) term400). Qed.
Lemma lem2279452 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279453 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279454 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279453 h1) (fun h1 : term411 = True => @lem2279452)). Qed.
Lemma lem2279455 : term411 = True.
Proof. exact (EQ_MP (@lem2279454) (@lem2279452)). Qed.
Lemma lem2279456 : term410 = True.
Proof. exact (TRANS (@lem2279451) (@lem2279455)). Qed.
Lemma lem2279457 : True = term410.
Proof. exact (SYM (@lem2279456)). Qed.
Lemma lem2279458 : term410.
Proof. exact (EQ_MP (@lem2279457) (@lem0)). Qed.
Lemma lem2279459 : term552.
Proof. exact (@lem2279448 (@lem2279458)). Qed.
Lemma lem2279461 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279462 : term410 = term411.
Proof. exact (@lem2279461 (NUMERAL 0) term400). Qed.
Lemma lem2279463 : term412 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2279464 (h1 : term412 = (BIT1 0)) : term411 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2279465 : (term412 = (BIT1 0)) = (term411 = True).
Proof. exact (prop_ext (fun h1 : term412 = (BIT1 0) => @lem2279464 h1) (fun h1 : term411 = True => @lem2279463)). Qed.
Lemma lem2279466 : term411 = True.
Proof. exact (EQ_MP (@lem2279465) (@lem2279463)). Qed.
Lemma lem2279467 : term410 = True.
Proof. exact (TRANS (@lem2279462) (@lem2279466)). Qed.
Lemma lem2279468 : True = term410.
Proof. exact (SYM (@lem2279467)). Qed.
Lemma lem2279469 : term410.
Proof. exact (EQ_MP (@lem2279468) (@lem0)). Qed.
Lemma lem2279470 : term550 = term553.
Proof. exact (@lem2279459 (@lem2279469)). Qed.
Lemma lem2279472 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279473 : term432 = term408.
Proof. exact (@lem2279472 term400). Qed.
Lemma lem2279475 (x : nat) : (term433 x) = term408.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2279476 : term432 = term408.
Proof. exact (@lem2279475 term400). Qed.
Lemma lem2279477 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2279478 : term554 = term548.
Proof. exact (MK_COMB (@lem2279477) (@lem2279476)). Qed.
Lemma lem2279479 : term553 = term547.
Proof. exact (MK_COMB (@lem2279478) (@lem2279473)). Qed.
Lemma lem2279481 (m : nat) (n : nat) : (term409 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2279482 : term547 = term555.
Proof. exact (@lem2279481 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2279483 : term555 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2279484 : term547 = False.
Proof. exact (TRANS (@lem2279482) (@lem2279483)). Qed.
Lemma lem2279485 : term553 = False.
Proof. exact (TRANS (@lem2279479) (@lem2279484)). Qed.
Lemma lem2279486 : term550 = False.
Proof. exact (TRANS (@lem2279470) (@lem2279485)). Qed.
Lemma lem2279487 : term547 = False.
Proof. exact (TRANS (@lem2279447) (@lem2279486)). Qed.
Lemma lem2279488 : term531 = False.
Proof. exact (TRANS (@lem2279438) (@lem2279487)). Qed.
Lemma lem2279489 (d : nat) (h1 : term556 d) : False.
Proof. exact (EQ_MP (@lem2279488) (@lem2279433 d h1)). Qed.
Lemma lem2279490 (d : nat) (h1 : term542 d) : False.
Proof. exact (or_elim (@lem2279373 d h1) (fun h0 : term546 d => @lem2279431 d h0) (fun h0 : term556 d => @lem2279489 d h0)). Qed.
Lemma lem2279491 (d : nat) (h1 : term545 d) : False.
Proof. exact (or_elim (@lem2279254 d h1) (fun h0 : term542 d => @lem2279372 d h0) (fun h0 : term542 d => @lem2279490 d h0)). Qed.
Lemma lem2279493 (d : nat) (h1 : term545 d) : term545 d.
Proof. exact (h1). Qed.
Lemma lem2279494 (d : nat) (h1 : term545 d) : (term545 d) = False.
Proof. exact (prop_ext (fun h2 : term545 d => @lem2279491 d h1) (fun h2 : False => @lem2279493 d h1)). Qed.
Lemma lem2279495 (d : nat) (h1 : term545 d) : False.
Proof. exact (EQ_MP (@lem2279494 d h1) (@lem2279493 d h1)). Qed.
Lemma lem2279496 (n : nat) (d : nat) (h1 : term664 n d) : term664 n d.
Proof. exact (h1). Qed.
Lemma lem2279497 (n : nat) (d : nat) (h1 : term664 n d) : term545 d.
Proof. exact (EQ_MP (@lem2279232 n d) (@lem2279496 n d h1)). Qed.
Lemma lem2279498 (n : nat) (d : nat) (h1 : term664 n d) : (term545 d) = False.
Proof. exact (prop_ext (fun h2 : term545 d => @lem2279495 d h2) (fun h2 : False => @lem2279497 n d h1)). Qed.
Lemma lem2279499 (n : nat) (d : nat) (h1 : term664 n d) : False.
Proof. exact (EQ_MP (@lem2279498 n d h1) (@lem2279497 n d h1)). Qed.
Lemma lem2279500 (n : nat) (d : nat) : term691 n d.
Proof. exact (fun h0 : term664 n d => @lem2279499 n d h0). Qed.
Lemma lem2279501 (n : nat) (d : nat) : term692 n d.
Proof. exact (@lem1386578 (term693 n d)). Qed.
Lemma lem2279504 (n : nat) (d : nat) : term693 n d.
Proof. exact (@lem2279501 n d (@lem2279500 n d)). Qed.
Lemma lem2279505 (d : nat) (n : nat) : term322 d n.
Proof. exact (ex_intro (term321 d n) d (@lem2279504 n d)). Qed.
Lemma lem2284381 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2273845 A P Q) (@lem2273844 A P Q)). Qed.
Lemma lem2284382 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2284381 nat P Q). Qed.
Lemma lem2284383 (m : nat) (d : nat) : (term694 m d) = (term695 m d).
Proof. exact (@lem2284382 (term696 m d) (term697 m d)). Qed.
Lemma lem2284384 (m : nat) (d : nat) (n' : nat) : (term698 m d n') = ((term347 m d) = (real_of_num n')).
Proof. exact (eq_refl (term698 m d n')). Qed.
Lemma lem2284385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284386 (m : nat) (d : nat) (n' : nat) : (term699 m d n') = (term350 m d n').
Proof. exact (MK_COMB (@lem2284385) (@lem2284384 m d n')). Qed.
Lemma lem2284387 (m : nat) (d : nat) (n' : nat) : (term700 m d n') = ((term347 m d) = (term93 n')).
Proof. exact (eq_refl (term700 m d n')). Qed.
Lemma lem2284388 (m : nat) (d : nat) (n' : nat) : (term701 m d n') = (term351 m d n').
Proof. exact (MK_COMB (@lem2284386 m d n') (@lem2284387 m d n')). Qed.
Lemma lem2284389 (m : nat) (d : nat) : (term702 m d) = (term352 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2284388 m d n')). Qed.
Lemma lem2284390 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284391 (m : nat) (d : nat) : (term694 m d) = (term353 m d).
Proof. exact (MK_COMB (@lem2284390) (@lem2284389 m d)). Qed.
Lemma lem2284392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2284393 (m : nat) (d : nat) : (term703 m d) = (term704 m d).
Proof. exact (MK_COMB (@lem2284392) (@lem2284391 m d)). Qed.
Lemma lem2284394 (m : nat) (d : nat) (n' : nat) : (term698 m d n') = ((term347 m d) = (real_of_num n')).
Proof. exact (eq_refl (term698 m d n')). Qed.
Lemma lem2284395 (m : nat) (d : nat) : (term705 m d) = (term696 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2284394 m d n')). Qed.
Lemma lem2284396 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284397 (m : nat) (d : nat) : (term706 m d) = (term707 m d).
Proof. exact (MK_COMB (@lem2284396) (@lem2284395 m d)). Qed.
Lemma lem2284398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284399 (m : nat) (d : nat) : (term708 m d) = (term709 m d).
Proof. exact (MK_COMB (@lem2284398) (@lem2284397 m d)). Qed.
Lemma lem2284400 (m : nat) (d : nat) (n' : nat) : (term700 m d n') = ((term347 m d) = (term93 n')).
Proof. exact (eq_refl (term700 m d n')). Qed.
Lemma lem2284401 (m : nat) (d : nat) : (term710 m d) = (term697 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2284400 m d n')). Qed.
Lemma lem2284402 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284403 (m : nat) (d : nat) : (term711 m d) = (term712 m d).
Proof. exact (MK_COMB (@lem2284402) (@lem2284401 m d)). Qed.
Lemma lem2284404 (m : nat) (d : nat) : (term695 m d) = (term713 m d).
Proof. exact (MK_COMB (@lem2284399 m d) (@lem2284403 m d)). Qed.
Lemma lem2284405 (m : nat) (d : nat) : ((term694 m d) = (term695 m d)) = ((term353 m d) = (term713 m d)).
Proof. exact (MK_COMB (@lem2284393 m d) (@lem2284404 m d)). Qed.
Lemma lem2284406 (m : nat) (d : nat) : (term353 m d) = (term713 m d).
Proof. exact (EQ_MP (@lem2284405 m d) (@lem2284383 m d)). Qed.
Lemma lem2284418 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284419 (m : nat) (d : nat) : (term136 m d) = (term218 m d).
Proof. exact (@lem2284418 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2284421 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284422 (m : nat) (d : nat) : (term25 m d) = (term26 m d).
Proof. exact (@lem2284421 m d). Qed.
Lemma lem2284423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284424 (m : nat) (d : nat) : (term218 m d) = (term217 m d).
Proof. exact (MK_COMB (@lem2284423) (@lem2284422 m d)). Qed.
Lemma lem2284425 (m : nat) (d : nat) : (term136 m d) = (term217 m d).
Proof. exact (TRANS (@lem2284419 m d) (@lem2284424 m d)). Qed.
Lemma lem2284426 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2284427 (m : nat) (d : nat) : (term347 m d) = (term328 m d).
Proof. exact (MK_COMB (@lem2284426 m) (@lem2284425 m d)). Qed.
Lemma lem2284429 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284430 (m : nat) (d : nat) : (term328 m d) = (term714 m d).
Proof. exact (@lem2284429 (real_of_num m) (term26 m d)). Qed.
Lemma lem2284432 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284433 (m : nat) (d : nat) : (term715 m d) = (term716 m d).
Proof. exact (@lem2284432 m (Nat.add m d)). Qed.
Lemma lem2284434 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284435 (m : nat) (d : nat) : (term714 m d) = (term717 m d).
Proof. exact (MK_COMB (@lem2284434) (@lem2284433 m d)). Qed.
Lemma lem2284436 (m : nat) (d : nat) : (term328 m d) = (term717 m d).
Proof. exact (TRANS (@lem2284430 m d) (@lem2284435 m d)). Qed.
Lemma lem2284437 (m : nat) (d : nat) : (term347 m d) = (term717 m d).
Proof. exact (TRANS (@lem2284427 m d) (@lem2284436 m d)). Qed.
Lemma lem2284438 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2284439 (m : nat) (d : nat) : (term349 m d) = (term718 m d).
Proof. exact (MK_COMB (@lem2284438) (@lem2284437 m d)). Qed.
Lemma lem2284440 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2284441 (m : nat) (d : nat) (n' : nat) : ((term347 m d) = (real_of_num n')) = ((term717 m d) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2284439 m d) (@lem2284440 n')). Qed.
Lemma lem2284444 (m : nat) (d : nat) : (term696 m d) = (term719 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2284441 m d n')). Qed.
Lemma lem2284445 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284446 (m : nat) (d : nat) : (term707 m d) = (term720 m d).
Proof. exact (MK_COMB (@lem2284445) (@lem2284444 m d)). Qed.
Lemma lem2284453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284454 (m : nat) (d : nat) : (term709 m d) = (term721 m d).
Proof. exact (MK_COMB (@lem2284453) (@lem2284446 m d)). Qed.
Lemma lem2284464 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284465 (m : nat) (d : nat) : (term136 m d) = (term218 m d).
Proof. exact (@lem2284464 (real_of_num m) (real_of_num d)). Qed.
Lemma lem2284467 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284468 (m : nat) (d : nat) : (term25 m d) = (term26 m d).
Proof. exact (@lem2284467 m d). Qed.
Lemma lem2284469 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284470 (m : nat) (d : nat) : (term218 m d) = (term217 m d).
Proof. exact (MK_COMB (@lem2284469) (@lem2284468 m d)). Qed.
Lemma lem2284471 (m : nat) (d : nat) : (term136 m d) = (term217 m d).
Proof. exact (TRANS (@lem2284465 m d) (@lem2284470 m d)). Qed.
Lemma lem2284472 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem2284473 (m : nat) (d : nat) : (term347 m d) = (term328 m d).
Proof. exact (MK_COMB (@lem2284472 m) (@lem2284471 m d)). Qed.
Lemma lem2284475 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284476 (m : nat) (d : nat) : (term328 m d) = (term714 m d).
Proof. exact (@lem2284475 (real_of_num m) (term26 m d)). Qed.
Lemma lem2284478 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284479 (m : nat) (d : nat) : (term715 m d) = (term716 m d).
Proof. exact (@lem2284478 m (Nat.add m d)). Qed.
Lemma lem2284480 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284481 (m : nat) (d : nat) : (term714 m d) = (term717 m d).
Proof. exact (MK_COMB (@lem2284480) (@lem2284479 m d)). Qed.
Lemma lem2284482 (m : nat) (d : nat) : (term328 m d) = (term717 m d).
Proof. exact (TRANS (@lem2284476 m d) (@lem2284481 m d)). Qed.
Lemma lem2284483 (m : nat) (d : nat) : (term347 m d) = (term717 m d).
Proof. exact (TRANS (@lem2284473 m d) (@lem2284482 m d)). Qed.
Lemma lem2284484 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2284485 (m : nat) (d : nat) : (term349 m d) = (term718 m d).
Proof. exact (MK_COMB (@lem2284484) (@lem2284483 m d)). Qed.
Lemma lem2284486 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2284487 (m : nat) (d : nat) (n' : nat) : ((term347 m d) = (term93 n')) = ((term717 m d) = (term93 n')).
Proof. exact (MK_COMB (@lem2284485 m d) (@lem2284486 n')). Qed.
Lemma lem2284489 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2273833 x y) (@lem2273832 x y)). Qed.
Lemma lem2284490 (m : nat) (d : nat) (n' : nat) : ((term717 m d) = (term93 n')) = ((term716 m d) = (real_of_num n')).
Proof. exact (@lem2284489 (term716 m d) (real_of_num n')). Qed.
Lemma lem2284492 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2273821 m n) (@lem2273820 m n)). Qed.
Lemma lem2284493 (m : nat) (d : nat) (n' : nat) : ((term716 m d) = (real_of_num n')) = ((term722 m d) = n').
Proof. exact (@lem2284492 (term722 m d) n'). Qed.
Lemma lem2284496 (m : nat) (d : nat) (n' : nat) : ((term717 m d) = (term93 n')) = ((term722 m d) = n').
Proof. exact (TRANS (@lem2284490 m d n') (@lem2284493 m d n')). Qed.
Lemma lem2284497 (m : nat) (d : nat) (n' : nat) : ((term347 m d) = (term93 n')) = ((term722 m d) = n').
Proof. exact (TRANS (@lem2284487 m d n') (@lem2284496 m d n')). Qed.
Lemma lem2284498 (m : nat) (d : nat) : (term697 m d) = (term723 m d).
Proof. exact (fun_ext (fun n' : nat => @lem2284497 m d n')). Qed.
Lemma lem2284499 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284500 (m : nat) (d : nat) : (term712 m d) = (term724 m d).
Proof. exact (MK_COMB (@lem2284499) (@lem2284498 m d)). Qed.
Lemma lem2284502 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2273815 A a) (@lem2273814 A a)). Qed.
Lemma lem2284503 (a : nat) : (term144 a) = True.
Proof. exact (@lem2284502 nat a). Qed.
Lemma lem2284504 (m : nat) (d : nat) : (term724 m d) = True.
Proof. exact (@lem2284503 (term722 m d)). Qed.
Lemma lem2284505 (m : nat) (d : nat) : (term712 m d) = True.
Proof. exact (TRANS (@lem2284500 m d) (@lem2284504 m d)). Qed.
Lemma lem2284506 (m : nat) (d : nat) : (term713 m d) = (term725 m d).
Proof. exact (MK_COMB (@lem2284454 m d) (@lem2284505 m d)). Qed.
Lemma lem2284508 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2284509 (m : nat) (d : nat) : (term725 m d) = True.
Proof. exact (@lem2284508 (term720 m d)). Qed.
Lemma lem2284510 (m : nat) (d : nat) : (term713 m d) = True.
Proof. exact (TRANS (@lem2284506 m d) (@lem2284509 m d)). Qed.
Lemma lem2284511 (m : nat) (d : nat) : (term353 m d) = True.
Proof. exact (TRANS (@lem2284406 m d) (@lem2284510 m d)). Qed.
Lemma lem2284512 (m : nat) (d : nat) : True = (term353 m d).
Proof. exact (SYM (@lem2284511 m d)). Qed.
Lemma lem2284513 (m : nat) (d : nat) : term353 m d.
Proof. exact (EQ_MP (@lem2284512 m d) (@lem0)). Qed.
Lemma lem2284515 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem2273845 A P Q) (@lem2273844 A P Q)). Qed.
Lemma lem2284516 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2284515 nat P Q). Qed.
Lemma lem2284517 (d : nat) (n : nat) : (term726 d n) = (term727 d n).
Proof. exact (@lem2284516 (term728 d n) (term729 d n)). Qed.
Lemma lem2284518 (d : nat) (n : nat) (n' : nat) : (term730 d n n') = ((term378 d n) = (real_of_num n')).
Proof. exact (eq_refl (term730 d n n')). Qed.
Lemma lem2284519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284520 (d : nat) (n : nat) (n' : nat) : (term731 d n n') = (term381 d n n').
Proof. exact (MK_COMB (@lem2284519) (@lem2284518 d n n')). Qed.
Lemma lem2284521 (d : nat) (n : nat) (n' : nat) : (term732 d n n') = ((term378 d n) = (term93 n')).
Proof. exact (eq_refl (term732 d n n')). Qed.
Lemma lem2284522 (d : nat) (n : nat) (n' : nat) : (term733 d n n') = (term382 d n n').
Proof. exact (MK_COMB (@lem2284520 d n n') (@lem2284521 d n n')). Qed.
Lemma lem2284523 (d : nat) (n : nat) : (term734 d n) = (term383 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2284522 d n n')). Qed.
Lemma lem2284524 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284525 (d : nat) (n : nat) : (term726 d n) = (term384 d n).
Proof. exact (MK_COMB (@lem2284524) (@lem2284523 d n)). Qed.
Lemma lem2284526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2284527 (d : nat) (n : nat) : (term735 d n) = (term736 d n).
Proof. exact (MK_COMB (@lem2284526) (@lem2284525 d n)). Qed.
Lemma lem2284528 (d : nat) (n : nat) (n' : nat) : (term730 d n n') = ((term378 d n) = (real_of_num n')).
Proof. exact (eq_refl (term730 d n n')). Qed.
Lemma lem2284529 (d : nat) (n : nat) : (term737 d n) = (term728 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2284528 d n n')). Qed.
Lemma lem2284530 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284531 (d : nat) (n : nat) : (term738 d n) = (term739 d n).
Proof. exact (MK_COMB (@lem2284530) (@lem2284529 d n)). Qed.
Lemma lem2284532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284533 (d : nat) (n : nat) : (term740 d n) = (term741 d n).
Proof. exact (MK_COMB (@lem2284532) (@lem2284531 d n)). Qed.
Lemma lem2284534 (d : nat) (n : nat) (n' : nat) : (term732 d n n') = ((term378 d n) = (term93 n')).
Proof. exact (eq_refl (term732 d n n')). Qed.
Lemma lem2284535 (d : nat) (n : nat) : (term742 d n) = (term729 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2284534 d n n')). Qed.
Lemma lem2284536 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284537 (d : nat) (n : nat) : (term743 d n) = (term744 d n).
Proof. exact (MK_COMB (@lem2284536) (@lem2284535 d n)). Qed.
Lemma lem2284538 (d : nat) (n : nat) : (term727 d n) = (term745 d n).
Proof. exact (MK_COMB (@lem2284533 d n) (@lem2284537 d n)). Qed.
Lemma lem2284539 (d : nat) (n : nat) : ((term726 d n) = (term727 d n)) = ((term384 d n) = (term745 d n)).
Proof. exact (MK_COMB (@lem2284527 d n) (@lem2284538 d n)). Qed.
Lemma lem2284540 (d : nat) (n : nat) : (term384 d n) = (term745 d n).
Proof. exact (EQ_MP (@lem2284539 d n) (@lem2284517 d n)). Qed.
Lemma lem2284552 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284553 (n : nat) (d : nat) : (term136 n d) = (term218 n d).
Proof. exact (@lem2284552 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2284555 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284556 (n : nat) (d : nat) : (term25 n d) = (term26 n d).
Proof. exact (@lem2284555 n d). Qed.
Lemma lem2284557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284558 (n : nat) (d : nat) : (term218 n d) = (term217 n d).
Proof. exact (MK_COMB (@lem2284557) (@lem2284556 n d)). Qed.
Lemma lem2284559 (n : nat) (d : nat) : (term136 n d) = (term217 n d).
Proof. exact (TRANS (@lem2284553 n d) (@lem2284558 n d)). Qed.
Lemma lem2284560 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2284561 (n : nat) (d : nat) : (term315 n d) = (term314 n d).
Proof. exact (MK_COMB (@lem2284560) (@lem2284559 n d)). Qed.
Lemma lem2284562 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2284563 (d : nat) (n : nat) : (term378 d n) = (term359 d n).
Proof. exact (MK_COMB (@lem2284561 n d) (@lem2284562 n)). Qed.
Lemma lem2284565 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284566 (d : nat) (n : nat) : (term359 d n) = (term746 d n).
Proof. exact (@lem2284565 (term26 n d) (real_of_num n)). Qed.
Lemma lem2284568 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284569 (d : nat) (n : nat) : (term747 d n) = (term748 d n).
Proof. exact (@lem2284568 (Nat.add n d) n). Qed.
Lemma lem2284570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284571 (d : nat) (n : nat) : (term746 d n) = (term749 d n).
Proof. exact (MK_COMB (@lem2284570) (@lem2284569 d n)). Qed.
Lemma lem2284572 (d : nat) (n : nat) : (term359 d n) = (term749 d n).
Proof. exact (TRANS (@lem2284566 d n) (@lem2284571 d n)). Qed.
Lemma lem2284573 (d : nat) (n : nat) : (term378 d n) = (term749 d n).
Proof. exact (TRANS (@lem2284563 d n) (@lem2284572 d n)). Qed.
Lemma lem2284574 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2284575 (d : nat) (n : nat) : (term380 d n) = (term750 d n).
Proof. exact (MK_COMB (@lem2284574) (@lem2284573 d n)). Qed.
Lemma lem2284576 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2284577 (d : nat) (n : nat) (n' : nat) : ((term378 d n) = (real_of_num n')) = ((term749 d n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2284575 d n) (@lem2284576 n')). Qed.
Lemma lem2284580 (d : nat) (n : nat) : (term728 d n) = (term751 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2284577 d n n')). Qed.
Lemma lem2284581 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284582 (d : nat) (n : nat) : (term739 d n) = (term752 d n).
Proof. exact (MK_COMB (@lem2284581) (@lem2284580 d n)). Qed.
Lemma lem2284589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2284590 (d : nat) (n : nat) : (term741 d n) = (term753 d n).
Proof. exact (MK_COMB (@lem2284589) (@lem2284582 d n)). Qed.
Lemma lem2284600 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284601 (n : nat) (d : nat) : (term136 n d) = (term218 n d).
Proof. exact (@lem2284600 (real_of_num n) (real_of_num d)). Qed.
Lemma lem2284603 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284604 (n : nat) (d : nat) : (term25 n d) = (term26 n d).
Proof. exact (@lem2284603 n d). Qed.
Lemma lem2284605 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284606 (n : nat) (d : nat) : (term218 n d) = (term217 n d).
Proof. exact (MK_COMB (@lem2284605) (@lem2284604 n d)). Qed.
Lemma lem2284607 (n : nat) (d : nat) : (term136 n d) = (term217 n d).
Proof. exact (TRANS (@lem2284601 n d) (@lem2284606 n d)). Qed.
Lemma lem2284608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2284609 (n : nat) (d : nat) : (term315 n d) = (term314 n d).
Proof. exact (MK_COMB (@lem2284608) (@lem2284607 n d)). Qed.
Lemma lem2284610 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2284611 (d : nat) (n : nat) : (term378 d n) = (term359 d n).
Proof. exact (MK_COMB (@lem2284609 n d) (@lem2284610 n)). Qed.
Lemma lem2284613 (x : real) (y : real) : (term9 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2273839 x y) (@lem2273838 x y)). Qed.
Lemma lem2284614 (d : nat) (n : nat) : (term359 d n) = (term746 d n).
Proof. exact (@lem2284613 (term26 n d) (real_of_num n)). Qed.
Lemma lem2284616 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem2273827 m n) (@lem2273826 m n)). Qed.
Lemma lem2284617 (d : nat) (n : nat) : (term747 d n) = (term748 d n).
Proof. exact (@lem2284616 (Nat.add n d) n). Qed.
Lemma lem2284618 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2284619 (d : nat) (n : nat) : (term746 d n) = (term749 d n).
Proof. exact (MK_COMB (@lem2284618) (@lem2284617 d n)). Qed.
Lemma lem2284620 (d : nat) (n : nat) : (term359 d n) = (term749 d n).
Proof. exact (TRANS (@lem2284614 d n) (@lem2284619 d n)). Qed.
Lemma lem2284621 (d : nat) (n : nat) : (term378 d n) = (term749 d n).
Proof. exact (TRANS (@lem2284611 d n) (@lem2284620 d n)). Qed.
Lemma lem2284622 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2284623 (d : nat) (n : nat) : (term380 d n) = (term750 d n).
Proof. exact (MK_COMB (@lem2284622) (@lem2284621 d n)). Qed.
Lemma lem2284624 (n' : nat) : (term93 n') = (term93 n').
Proof. exact (eq_refl (term93 n')). Qed.
Lemma lem2284625 (d : nat) (n : nat) (n' : nat) : ((term378 d n) = (term93 n')) = ((term749 d n) = (term93 n')).
Proof. exact (MK_COMB (@lem2284623 d n) (@lem2284624 n')). Qed.
Lemma lem2284627 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2273833 x y) (@lem2273832 x y)). Qed.
Lemma lem2284628 (d : nat) (n : nat) (n' : nat) : ((term749 d n) = (term93 n')) = ((term748 d n) = (real_of_num n')).
Proof. exact (@lem2284627 (term748 d n) (real_of_num n')). Qed.
Lemma lem2284630 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2273821 m n) (@lem2273820 m n)). Qed.
Lemma lem2284631 (d : nat) (n : nat) (n' : nat) : ((term748 d n) = (real_of_num n')) = ((term754 d n) = n').
Proof. exact (@lem2284630 (term754 d n) n'). Qed.
Lemma lem2284634 (d : nat) (n : nat) (n' : nat) : ((term749 d n) = (term93 n')) = ((term754 d n) = n').
Proof. exact (TRANS (@lem2284628 d n n') (@lem2284631 d n n')). Qed.
Lemma lem2284635 (d : nat) (n : nat) (n' : nat) : ((term378 d n) = (term93 n')) = ((term754 d n) = n').
Proof. exact (TRANS (@lem2284625 d n n') (@lem2284634 d n n')). Qed.
Lemma lem2284636 (d : nat) (n : nat) : (term729 d n) = (term755 d n).
Proof. exact (fun_ext (fun n' : nat => @lem2284635 d n n')). Qed.
Lemma lem2284637 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2284638 (d : nat) (n : nat) : (term744 d n) = (term756 d n).
Proof. exact (MK_COMB (@lem2284637) (@lem2284636 d n)). Qed.
Lemma lem2284640 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2273815 A a) (@lem2273814 A a)). Qed.
Lemma lem2284641 (a : nat) : (term144 a) = True.
Proof. exact (@lem2284640 nat a). Qed.
Lemma lem2284642 (d : nat) (n : nat) : (term756 d n) = True.
Proof. exact (@lem2284641 (term754 d n)). Qed.
Lemma lem2284643 (d : nat) (n : nat) : (term744 d n) = True.
Proof. exact (TRANS (@lem2284638 d n) (@lem2284642 d n)). Qed.
Lemma lem2284644 (d : nat) (n : nat) : (term745 d n) = (term757 d n).
Proof. exact (MK_COMB (@lem2284590 d n) (@lem2284643 d n)). Qed.
Lemma lem2284646 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2284647 (d : nat) (n : nat) : (term757 d n) = True.
Proof. exact (@lem2284646 (term752 d n)). Qed.
Lemma lem2284648 (d : nat) (n : nat) : (term745 d n) = True.
Proof. exact (TRANS (@lem2284644 d n) (@lem2284647 d n)). Qed.
Lemma lem2284649 (d : nat) (n : nat) : (term384 d n) = True.
Proof. exact (TRANS (@lem2284540 d n) (@lem2284648 d n)). Qed.
Lemma lem2284650 (d : nat) (n : nat) : True = (term384 d n).
Proof. exact (SYM (@lem2284649 d n)). Qed.
Lemma lem2284651 (d : nat) (n : nat) : term384 d n.
Proof. exact (EQ_MP (@lem2284650 d n) (@lem0)). Qed.
Lemma lem2284652 (d : nat) (n : nat) : term191 d n.
Proof. exact (EQ_MP (@lem2275429 d n) (@lem2284651 d n)). Qed.
Lemma lem2284653 (m : nat) (d : nat) : term185 m d.
Proof. exact (EQ_MP (@lem2275340 m d) (@lem2284513 m d)). Qed.
Lemma lem2284654 (d : nat) (n : nat) : term180 d n.
Proof. exact (EQ_MP (@lem2275255 d n) (@lem2279505 d n)). Qed.
Lemma lem2284655 (m : nat) (d : nat) : term174 m d.
Proof. exact (EQ_MP (@lem2275166 m d) (@lem2278476 m d)). Qed.
Lemma lem2284656 (d : nat) (n : nat) : term169 d n.
Proof. exact (EQ_MP (@lem2275093 d n) (@lem2277467 d n)). Qed.
Lemma lem2284657 (m : nat) (d : nat) : term163 m d.
Proof. exact (EQ_MP (@lem2275016 m d) (@lem2276458 m d)). Qed.
Lemma lem2284658 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : term143 m n.
Proof. exact (EQ_MP (@lem2274931 m n d h1) (@lem2284652 d n)). Qed.
Lemma lem2284659 (m : nat) (n : nat) (h1 : term54 m n) : term143 m n.
Proof. exact (ex_elim (@lem2274917 m n h1) (fun d : nat => fun h0 : term758 m n d => @lem2284658 m n d h0)). Qed.
Lemma lem2284660 (m : nat) (n : nat) : term159 m n.
Proof. exact (fun h0 : term54 m n => @lem2284659 m n h0). Qed.
Lemma lem2284661 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term143 m n.
Proof. exact (EQ_MP (@lem2274916 n m d h1) (@lem2284653 m d)). Qed.
Lemma lem2284662 (n : nat) (m : nat) (h1 : term54 n m) : term143 m n.
Proof. exact (ex_elim (@lem2274902 n m h1) (fun d : nat => fun h0 : term758 n m d => @lem2284661 n m d h0)). Qed.
Lemma lem2284663 (m : nat) (n : nat) : term157 m n.
Proof. exact (fun h0 : term54 n m => @lem2284662 n m h0). Qed.
Lemma lem2284664 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : term135 m n.
Proof. exact (EQ_MP (@lem2274901 m n d h1) (@lem2284654 d n)). Qed.
Lemma lem2284665 (m : nat) (n : nat) (h1 : term54 m n) : term135 m n.
Proof. exact (ex_elim (@lem2274887 m n h1) (fun d : nat => fun h0 : term758 m n d => @lem2284664 m n d h0)). Qed.
Lemma lem2284666 (m : nat) (n : nat) : term155 m n.
Proof. exact (fun h0 : term54 m n => @lem2284665 m n h0). Qed.
Lemma lem2284667 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term135 m n.
Proof. exact (EQ_MP (@lem2274886 n m d h1) (@lem2284655 m d)). Qed.
Lemma lem2284668 (n : nat) (m : nat) (h1 : term54 n m) : term135 m n.
Proof. exact (ex_elim (@lem2274872 n m h1) (fun d : nat => fun h0 : term758 n m d => @lem2284667 n m d h0)). Qed.
Lemma lem2284669 (m : nat) (n : nat) : term153 m n.
Proof. exact (fun h0 : term54 n m => @lem2284668 n m h0). Qed.
Lemma lem2284670 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : term126 m n.
Proof. exact (EQ_MP (@lem2274871 m n d h1) (@lem2284656 d n)). Qed.
Lemma lem2284671 (m : nat) (n : nat) (h1 : term54 m n) : term126 m n.
Proof. exact (ex_elim (@lem2274857 m n h1) (fun d : nat => fun h0 : term758 m n d => @lem2284670 m n d h0)). Qed.
Lemma lem2284672 (m : nat) (n : nat) : term151 m n.
Proof. exact (fun h0 : term54 m n => @lem2284671 m n h0). Qed.
Lemma lem2284673 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term126 m n.
Proof. exact (EQ_MP (@lem2274856 n m d h1) (@lem2284657 m d)). Qed.
Lemma lem2284674 (n : nat) (m : nat) (h1 : term54 n m) : term126 m n.
Proof. exact (ex_elim (@lem2274842 n m h1) (fun d : nat => fun h0 : term758 n m d => @lem2284673 n m d h0)). Qed.
Lemma lem2284675 (m : nat) (n : nat) : term149 m n.
Proof. exact (fun h0 : term54 n m => @lem2284674 n m h0). Qed.
Lemma lem2284676 (m : nat) (n : nat) : term158 m n.
Proof. exact (EQ_MP (@lem2274841 m n) (@lem2284660 m n)). Qed.
Lemma lem2284677 (m : nat) (n : nat) : term156 m n.
Proof. exact (EQ_MP (@lem2274809 m n) (@lem2284663 m n)). Qed.
Lemma lem2284678 (m : nat) (n : nat) : term154 m n.
Proof. exact (EQ_MP (@lem2274778 m n) (@lem2284666 m n)). Qed.
Lemma lem2284679 (m : nat) (n : nat) : term152 m n.
Proof. exact (EQ_MP (@lem2274746 m n) (@lem2284669 m n)). Qed.
Lemma lem2284680 (m : nat) (n : nat) : term150 m n.
Proof. exact (EQ_MP (@lem2274715 m n) (@lem2284672 m n)). Qed.
Lemma lem2284681 (m : nat) (n : nat) : term148 m n.
Proof. exact (EQ_MP (@lem2274683 m n) (@lem2284675 m n)). Qed.
Lemma lem2284682 (n : nat) (m : nat) (h1 : Peano.le n m) : term143 m n.
Proof. exact (@lem2284676 m n (@lem2273892 n m h1)). Qed.
Lemma lem2284683 (m : nat) (n : nat) (h1 : Peano.le m n) : term143 m n.
Proof. exact (@lem2284677 m n (@lem2273891 m n h1)). Qed.
Lemma lem2284685 (n : nat) (m : nat) (h1 : Peano.le n m) : term135 m n.
Proof. exact (@lem2284678 m n (@lem2273892 n m h1)). Qed.
Lemma lem2284686 (m : nat) (n : nat) (h1 : Peano.le m n) : term135 m n.
Proof. exact (@lem2284679 m n (@lem2273891 m n h1)). Qed.
Lemma lem2284688 (n : nat) (m : nat) (h1 : Peano.le n m) : term126 m n.
Proof. exact (@lem2284680 m n (@lem2273892 n m h1)). Qed.
Lemma lem2284689 (m : nat) (n : nat) (h1 : Peano.le m n) : term126 m n.
Proof. exact (@lem2284681 m n (@lem2273891 m n h1)). Qed.
Lemma lem2284691 (m : nat) (n : nat) : term143 m n.
Proof. exact (or_elim (@lem2273890 n m) (fun h0 : Peano.le m n => @lem2284683 m n h0) (fun h0 : Peano.le n m => @lem2284682 n m h0)). Qed.
Lemma lem2284692 (m : nat) (n : nat) : term135 m n.
Proof. exact (or_elim (@lem2273890 n m) (fun h0 : Peano.le m n => @lem2284686 m n h0) (fun h0 : Peano.le n m => @lem2284685 n m h0)). Qed.
Lemma lem2284693 (m : nat) (n : nat) : term126 m n.
Proof. exact (or_elim (@lem2273890 n m) (fun h0 : Peano.le m n => @lem2284689 m n h0) (fun h0 : Peano.le n m => @lem2284688 n m h0)). Qed.
Lemma lem2284694 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (term93 n)) : term74 x y.
Proof. exact (EQ_MP (@lem2274568 x m y n h1 h2) (@lem2284691 m n)). Qed.
Lemma lem2284695 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : (real_of_int y) = (real_of_num n)) : term74 x y.
Proof. exact (EQ_MP (@lem2274428 x m y n h1 h2) (@lem2284692 m n)). Qed.
Lemma lem2284696 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term93 n)) : term74 x y.
Proof. exact (EQ_MP (@lem2274288 x m y n h1 h2) (@lem2284693 m n)). Qed.
Lemma lem2284697 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : term74 x y.
Proof. exact (EQ_MP (@lem2274148 x m y n h1 h2) (@lem2274592 m n)). Qed.
Lemma lem2284698 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term93 m)) (h2 : term61 y n) : term74 x y.
Proof. exact (or_elim (@lem2273915 y n h2) (fun h0 : (real_of_int y) = (real_of_num n) => @lem2284695 x m y n h1 h0) (fun h0 : (real_of_int y) = (term93 n) => @lem2284694 x m y n h1 h0)). Qed.
Lemma lem2284699 (y : int) (x : int) (m : nat) (h1 : (real_of_int x) = (term93 m)) : term74 x y.
Proof. exact (ex_elim (@lem2273914 y) (fun n : nat => fun h0 : term759 y n => @lem2284698 x m y n h1 h0)). Qed.
Lemma lem2284700 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : term61 y n) : term74 x y.
Proof. exact (or_elim (@lem2273915 y n h2) (fun h0 : (real_of_int y) = (real_of_num n) => @lem2284697 x m y n h1 h0) (fun h0 : (real_of_int y) = (term93 n) => @lem2284696 x m y n h1 h0)). Qed.
Lemma lem2284701 (y : int) (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : term74 x y.
Proof. exact (ex_elim (@lem2273914 y) (fun n : nat => fun h0 : term759 y n => @lem2284700 x m y n h1 h0)). Qed.
Lemma lem2284702 (y : int) (x : int) (m : nat) (h1 : term61 x m) : term74 x y.
Proof. exact (or_elim (@lem2273919 x m h1) (fun h0 : (real_of_int x) = (real_of_num m) => @lem2284701 y x m h0) (fun h0 : (real_of_int x) = (term93 m) => @lem2284699 y x m h0)). Qed.
Lemma lem2284703 (x : int) (y : int) : term74 x y.
Proof. exact (ex_elim (@lem2273918 x) (fun m : nat => fun h0 : term759 x m => @lem2284702 y x m h0)). Qed.
Lemma lem2284708 (x : int) : term78 x.
Proof. exact (fun y : int => @lem2284703 x y). Qed.
Lemma lem2284713 : term82.
Proof. exact (fun x : int => @lem2284708 x). Qed.
Lemma lem2284714 : term81.
Proof. exact (EQ_MP (@lem2273982) (@lem2284713)). Qed.
