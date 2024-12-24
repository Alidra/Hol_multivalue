Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_of_num_th_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Require Import EXISTS_REFL_spec.
Require Import int_of_num_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Require Import thm2267742_spec.
Require Import thm7_spec.
Lemma lem2271823 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2271824 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2271823 A x a h1)). Qed.
Lemma lem2271825 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2271826 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2271825 A a x h1)). Qed.
Lemma lem2271827 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2271824 A x a h1) (fun h1 : a = x => @lem2271826 A a x h1)). Qed.
Lemma lem2271828 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2271827 A a x)). Qed.
Lemma lem2271829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2271830 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2271829 A) (@lem2271828 A a)). Qed.
Lemma lem2271831 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2271830 A a)). Qed.
Lemma lem2271832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2271833 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2271832 A) (@lem2271831 A)). Qed.
Lemma lem2271834 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2271833 A) (@lem4363 A)). Qed.
Lemma lem2271835 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem2271834 A a). Qed.
Lemma lem2271836 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem2271837 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2271836 A a) (@lem2271835 A a)). Qed.
Lemma lem2271838 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2271840 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2271841 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem2271842 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem2271841 A P) (@lem2271840 A P)). Qed.
Lemma lem2271843 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (@lem2271842 A P Q). Qed.
Lemma lem2271844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term11 A P Q) = ((term12 A P Q) = (term13 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem2271846 (m : nat) : term14 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2271847 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem2271848 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem2271847 m) (@lem2271846 m)). Qed.
Lemma lem2271849 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem2271848 m n). Qed.
Lemma lem2271850 (m : nat) (n : nat) : (term16 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem2271852 (r : real) (h1 : (integer r) = ((term17 r) = r)) : (integer r) = ((term17 r) = r).
Proof. exact (h1). Qed.
Lemma lem2271853 (r : real) (h1 : (integer r) = ((term17 r) = r)) : ((term17 r) = r) = (integer r).
Proof. exact (SYM (@lem2271852 r h1)). Qed.
Lemma lem2271854 (r : real) (h1 : ((term17 r) = r) = (integer r)) : ((term17 r) = r) = (integer r).
Proof. exact (h1). Qed.
Lemma lem2271855 (r : real) (h1 : ((term17 r) = r) = (integer r)) : (integer r) = ((term17 r) = r).
Proof. exact (SYM (@lem2271854 r h1)). Qed.
Lemma lem2271856 (r : real) : ((integer r) = ((term17 r) = r)) = (((term17 r) = r) = (integer r)).
Proof. exact (prop_ext (fun h1 : (integer r) = ((term17 r) = r) => @lem2271853 r h1) (fun h1 : ((term17 r) = r) = (integer r) => @lem2271855 r h1)). Qed.
Lemma lem2271858 (n : nat) : term18 n.
Proof. exact (@lem2271820 n). Qed.
Lemma lem2271859 (n : nat) : (term18 n) = ((int_of_num n) = (term19 n)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem2271868 (n : nat) : (int_of_num n) = (term19 n).
Proof. exact (EQ_MP (@lem2271859 n) (@lem2271858 n)). Qed.
Lemma lem2271869 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2271870 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem2271869) (@lem2271868 n)). Qed.
Lemma lem2271871 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2271872 (n : nat) : (term22 n) = (term23 n).
Proof. exact (MK_COMB (@lem2271871) (@lem2271870 n)). Qed.
Lemma lem2271873 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2271874 (n : nat) : ((term20 n) = (real_of_num n)) = ((term21 n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem2271872 n) (@lem2271873 n)). Qed.
Lemma lem2271876 (r : real) : ((term17 r) = r) = (integer r).
Proof. exact (EQ_MP (@lem2271856 r) (@lem2267742 r)). Qed.
Lemma lem2271877 (n : nat) : ((term21 n) = (real_of_num n)) = (term24 n).
Proof. exact (@lem2271876 (real_of_num n)). Qed.
Lemma lem2271879 (x : real) : (integer x) = (term25 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.
Lemma lem2271880 (n : nat) : (term24 n) = (term26 n).
Proof. exact (@lem2271879 (real_of_num n)). Qed.
Lemma lem2271891 (n : nat) : ((term21 n) = (real_of_num n)) = (term26 n).
Proof. exact (TRANS (@lem2271877 n) (@lem2271880 n)). Qed.
Lemma lem2271892 (n : nat) : ((term20 n) = (real_of_num n)) = (term26 n).
Proof. exact (TRANS (@lem2271874 n) (@lem2271891 n)). Qed.
Lemma lem2271893 : term27 = term28.
Proof. exact (fun_ext (fun n : nat => @lem2271892 n)). Qed.
Lemma lem2271894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2271895 : term29 = term30.
Proof. exact (MK_COMB (@lem2271894) (@lem2271893)). Qed.
Lemma lem2271900 : term30 = term29.
Proof. exact (SYM (@lem2271895)). Qed.
Lemma lem2271906 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term12 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem2271844 A P Q) (@lem2271843 A P Q)). Qed.
Lemma lem2271907 (P : nat -> Prop) (Q : nat -> Prop) : (term31 P Q) = (term32 P Q).
Proof. exact (@lem2271906 nat P Q). Qed.
Lemma lem2271908 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem2271907 (term35 n) (term36 n)). Qed.
Lemma lem2271909 (n : nat) (n' : nat) : (term37 n n') = ((real_of_num n) = (real_of_num n')).
Proof. exact (eq_refl (term37 n n')). Qed.
Lemma lem2271910 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2271911 (n : nat) (n' : nat) : (term38 n n') = (term39 n n').
Proof. exact (MK_COMB (@lem2271910) (@lem2271909 n n')). Qed.
Lemma lem2271912 (n : nat) (n' : nat) : (term40 n n') = ((real_of_num n) = (term41 n')).
Proof. exact (eq_refl (term40 n n')). Qed.
Lemma lem2271913 (n : nat) (n' : nat) : (term42 n n') = (term43 n n').
Proof. exact (MK_COMB (@lem2271911 n n') (@lem2271912 n n')). Qed.
Lemma lem2271914 (n : nat) : (term44 n) = (term45 n).
Proof. exact (fun_ext (fun n' : nat => @lem2271913 n n')). Qed.
Lemma lem2271915 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2271916 (n : nat) : (term33 n) = (term26 n).
Proof. exact (MK_COMB (@lem2271915) (@lem2271914 n)). Qed.
Lemma lem2271917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2271918 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem2271917) (@lem2271916 n)). Qed.
Lemma lem2271919 (n : nat) (n' : nat) : (term37 n n') = ((real_of_num n) = (real_of_num n')).
Proof. exact (eq_refl (term37 n n')). Qed.
Lemma lem2271920 (n : nat) : (term48 n) = (term35 n).
Proof. exact (fun_ext (fun n' : nat => @lem2271919 n n')). Qed.
Lemma lem2271921 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2271922 (n : nat) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem2271921) (@lem2271920 n)). Qed.
Lemma lem2271923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2271924 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem2271923) (@lem2271922 n)). Qed.
Lemma lem2271925 (n : nat) (n' : nat) : (term40 n n') = ((real_of_num n) = (term41 n')).
Proof. exact (eq_refl (term40 n n')). Qed.
Lemma lem2271926 (n : nat) : (term53 n) = (term36 n).
Proof. exact (fun_ext (fun n' : nat => @lem2271925 n n')). Qed.
Lemma lem2271927 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2271928 (n : nat) : (term54 n) = (term55 n).
Proof. exact (MK_COMB (@lem2271927) (@lem2271926 n)). Qed.
Lemma lem2271929 (n : nat) : (term34 n) = (term56 n).
Proof. exact (MK_COMB (@lem2271924 n) (@lem2271928 n)). Qed.
Lemma lem2271930 (n : nat) : ((term33 n) = (term34 n)) = ((term26 n) = (term56 n)).
Proof. exact (MK_COMB (@lem2271918 n) (@lem2271929 n)). Qed.
Lemma lem2271931 (n : nat) : (term26 n) = (term56 n).
Proof. exact (EQ_MP (@lem2271930 n) (@lem2271908 n)). Qed.
Lemma lem2271941 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2271850 m n) (@lem2271849 m n)). Qed.
Lemma lem2271942 (n : nat) (n' : nat) : ((real_of_num n) = (real_of_num n')) = (n = n').
Proof. exact (@lem2271941 n n'). Qed.
Lemma lem2271945 (n : nat) : (term35 n) = (term57 n).
Proof. exact (fun_ext (fun n' : nat => @lem2271942 n n')). Qed.
Lemma lem2271946 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2271947 (n : nat) : (term50 n) = (term58 n).
Proof. exact (MK_COMB (@lem2271946) (@lem2271945 n)). Qed.
Lemma lem2271949 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2271838 A a) (@lem2271837 A a)). Qed.
Lemma lem2271950 (a : nat) : (term58 a) = True.
Proof. exact (@lem2271949 nat a). Qed.
Lemma lem2271951 (n : nat) : (term58 n) = True.
Proof. exact (@lem2271950 n). Qed.
Lemma lem2271952 (n : nat) : (term50 n) = True.
Proof. exact (TRANS (@lem2271947 n) (@lem2271951 n)). Qed.
Lemma lem2271953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2271954 (n : nat) : (term52 n) = (or True).
Proof. exact (MK_COMB (@lem2271953) (@lem2271952 n)). Qed.
Lemma lem2271963 (n : nat) : (term55 n) = (term55 n).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem2271964 (n : nat) : (term56 n) = (term59 n).
Proof. exact (MK_COMB (@lem2271954 n) (@lem2271963 n)). Qed.
Lemma lem2271966 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2271967 (n : nat) : (term59 n) = True.
Proof. exact (@lem2271966 (term55 n)). Qed.
Lemma lem2271968 (n : nat) : (term56 n) = True.
Proof. exact (TRANS (@lem2271964 n) (@lem2271967 n)). Qed.
Lemma lem2271969 (n : nat) : (term26 n) = True.
Proof. exact (TRANS (@lem2271931 n) (@lem2271968 n)). Qed.
Lemma lem2271970 : term28 = term60.
Proof. exact (fun_ext (fun n : nat => @lem2271969 n)). Qed.
Lemma lem2271971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2271972 : term30 = term61.
Proof. exact (MK_COMB (@lem2271971) (@lem2271970)). Qed.
Lemma lem2271974 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2271975 (t : Prop) : (term63 t) = t.
Proof. exact (@lem2271974 nat t). Qed.
Lemma lem2271976 : term61 = True.
Proof. exact (@lem2271975 True). Qed.
Lemma lem2271977 : term30 = True.
Proof. exact (TRANS (@lem2271972) (@lem2271976)). Qed.
Lemma lem2271978 : True = term30.
Proof. exact (SYM (@lem2271977)). Qed.
Lemma lem2271979 : term30.
Proof. exact (EQ_MP (@lem2271978) (@lem0)). Qed.
Lemma lem2271980 : term29.
Proof. exact (EQ_MP (@lem2271900) (@lem2271979)). Qed.
