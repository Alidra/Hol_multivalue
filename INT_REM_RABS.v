Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_RABS_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import INT_ABS_NEG_spec.
Require Import INT_ABS_NUM_spec.
Require Import INT_REM_RNEG_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2519807 (n : nat) : term0 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2519808 (n : nat) : (term0 n) = ((term1 n) = (int_of_num n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2519810 (m : int) : term2 m.
Proof. exact (@lem2519805 m). Qed.
Lemma lem2519811 (m : int) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem2519812 (m : int) : term3 m.
Proof. exact (EQ_MP (@lem2519811 m) (@lem2519810 m)). Qed.
Lemma lem2519813 (m : int) (n : int) : term4 m n.
Proof. exact (@lem2519812 m n). Qed.
Lemma lem2519814 (m : int) (n : int) : (term4 m n) = ((term5 m n) = (rem m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2519816 (x : int) : term6 x.
Proof. exact (@lem2300452 x). Qed.
Lemma lem2519817 (x : int) : (term6 x) = ((term7 x) = (int_abs x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2519819 (P : int -> Prop) : term8 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2519820 (P : int -> Prop) : (term8 P) = ((term9 P) = (term10 P)).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem2519827 (P : int -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem2519820 P) (@lem2519819 P)). Qed.
Lemma lem2519828 : term11 = term12.
Proof. exact (@lem2519827 term13). Qed.
Lemma lem2519829 (x : int) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2519830 : term16 = term13.
Proof. exact (fun_ext (fun x : int => @lem2519829 x)). Qed.
Lemma lem2519831 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2519832 : term11 = term17.
Proof. exact (MK_COMB (@lem2519831) (@lem2519830)). Qed.
Lemma lem2519833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2519834 : term18 = term19.
Proof. exact (MK_COMB (@lem2519833) (@lem2519832)). Qed.
Lemma lem2519835 (n : nat) : (term20 n) = (term21 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem2519836 : term22 = term23.
Proof. exact (fun_ext (fun n : nat => @lem2519835 n)). Qed.
Lemma lem2519837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519838 : term24 = term25.
Proof. exact (MK_COMB (@lem2519837) (@lem2519836)). Qed.
Lemma lem2519839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2519840 : term26 = term27.
Proof. exact (MK_COMB (@lem2519839) (@lem2519838)). Qed.
Lemma lem2519841 (n : nat) : (term28 n) = (term29 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem2519842 : term30 = term31.
Proof. exact (fun_ext (fun n : nat => @lem2519841 n)). Qed.
Lemma lem2519843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519844 : term32 = term33.
Proof. exact (MK_COMB (@lem2519843) (@lem2519842)). Qed.
Lemma lem2519845 : term12 = term34.
Proof. exact (MK_COMB (@lem2519840) (@lem2519844)). Qed.
Lemma lem2519846 : (term11 = term12) = (term17 = term34).
Proof. exact (MK_COMB (@lem2519834) (@lem2519845)). Qed.
Lemma lem2519847 : term17 = term34.
Proof. exact (EQ_MP (@lem2519846) (@lem2519828)). Qed.
Lemma lem2519861 (P : int -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem2519820 P) (@lem2519819 P)). Qed.
Lemma lem2519862 (n : nat) : (term35 n) = (term36 n).
Proof. exact (@lem2519861 (term37 n)). Qed.
Lemma lem2519863 (n : nat) (y : int) : (term38 n y) = ((term39 n y) = (term40 n y)).
Proof. exact (eq_refl (term38 n y)). Qed.
Lemma lem2519864 (n : nat) : (term41 n) = (term37 n).
Proof. exact (fun_ext (fun y : int => @lem2519863 n y)). Qed.
Lemma lem2519865 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2519866 (n : nat) : (term35 n) = (term21 n).
Proof. exact (MK_COMB (@lem2519865) (@lem2519864 n)). Qed.
Lemma lem2519867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2519868 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem2519867) (@lem2519866 n)). Qed.
Lemma lem2519869 (n : nat) (n' : nat) : (term44 n n') = ((term45 n n') = (term46 n n')).
Proof. exact (eq_refl (term44 n n')). Qed.
Lemma lem2519870 (n : nat) : (term47 n) = (term48 n).
Proof. exact (fun_ext (fun n' : nat => @lem2519869 n n')). Qed.
Lemma lem2519871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519872 (n : nat) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem2519871) (@lem2519870 n)). Qed.
Lemma lem2519873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2519874 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem2519873) (@lem2519872 n)). Qed.
Lemma lem2519875 (n : nat) (n' : nat) : (term53 n n') = ((term54 n n') = (term55 n n')).
Proof. exact (eq_refl (term53 n n')). Qed.
Lemma lem2519876 (n : nat) : (term56 n) = (term57 n).
Proof. exact (fun_ext (fun n' : nat => @lem2519875 n n')). Qed.
Lemma lem2519877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519878 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem2519877) (@lem2519876 n)). Qed.
Lemma lem2519879 (n : nat) : (term36 n) = (term60 n).
Proof. exact (MK_COMB (@lem2519874 n) (@lem2519878 n)). Qed.
Lemma lem2519880 (n : nat) : ((term35 n) = (term36 n)) = ((term21 n) = (term60 n)).
Proof. exact (MK_COMB (@lem2519868 n) (@lem2519879 n)). Qed.
Lemma lem2519881 (n : nat) : (term21 n) = (term60 n).
Proof. exact (EQ_MP (@lem2519880 n) (@lem2519862 n)). Qed.
Lemma lem2519893 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2519808 n) (@lem2519807 n)). Qed.
Lemma lem2519894 (n' : nat) : (term1 n') = (int_of_num n').
Proof. exact (@lem2519893 n'). Qed.
Lemma lem2519895 (n : nat) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem2519896 (n : nat) (n' : nat) : (term45 n n') = (term46 n n').
Proof. exact (MK_COMB (@lem2519895 n) (@lem2519894 n')). Qed.
Lemma lem2519897 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2519898 (n : nat) (n' : nat) : (term62 n n') = (term63 n n').
Proof. exact (MK_COMB (@lem2519897) (@lem2519896 n n')). Qed.
Lemma lem2519899 (n : nat) (n' : nat) : (term46 n n') = (term46 n n').
Proof. exact (eq_refl (term46 n n')). Qed.
Lemma lem2519900 (n : nat) (n' : nat) : ((term45 n n') = (term46 n n')) = ((term46 n n') = (term46 n n')).
Proof. exact (MK_COMB (@lem2519898 n n') (@lem2519899 n n')). Qed.
Lemma lem2519902 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2519903 (x : int) : (x = x) = True.
Proof. exact (@lem2519902 int x). Qed.
Lemma lem2519904 (n : nat) (n' : nat) : ((term46 n n') = (term46 n n')) = True.
Proof. exact (@lem2519903 (term46 n n')). Qed.
Lemma lem2519905 (n : nat) (n' : nat) : ((term45 n n') = (term46 n n')) = True.
Proof. exact (TRANS (@lem2519900 n n') (@lem2519904 n n')). Qed.
Lemma lem2519906 (n : nat) : (term48 n) = term64.
Proof. exact (fun_ext (fun n' : nat => @lem2519905 n n')). Qed.
Lemma lem2519907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519908 (n : nat) : (term50 n) = term65.
Proof. exact (MK_COMB (@lem2519907) (@lem2519906 n)). Qed.
Lemma lem2519910 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2519911 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2519910 nat t). Qed.
Lemma lem2519912 : term65 = True.
Proof. exact (@lem2519911 True). Qed.
Lemma lem2519913 (n : nat) : (term50 n) = True.
Proof. exact (TRANS (@lem2519908 n) (@lem2519912)). Qed.
Lemma lem2519914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2519915 (n : nat) : (term52 n) = (and True).
Proof. exact (MK_COMB (@lem2519914) (@lem2519913 n)). Qed.
Lemma lem2519925 (x : int) : (term7 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2519817 x) (@lem2519816 x)). Qed.
Lemma lem2519926 (n' : nat) : (term68 n') = (term1 n').
Proof. exact (@lem2519925 (int_of_num n')). Qed.
Lemma lem2519928 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2519808 n) (@lem2519807 n)). Qed.
Lemma lem2519929 (n' : nat) : (term1 n') = (int_of_num n').
Proof. exact (@lem2519928 n'). Qed.
Lemma lem2519930 (n' : nat) : (term68 n') = (int_of_num n').
Proof. exact (TRANS (@lem2519926 n') (@lem2519929 n')). Qed.
Lemma lem2519931 (n : nat) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem2519932 (n : nat) (n' : nat) : (term54 n n') = (term46 n n').
Proof. exact (MK_COMB (@lem2519931 n) (@lem2519930 n')). Qed.
Lemma lem2519933 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2519934 (n : nat) (n' : nat) : (term69 n n') = (term63 n n').
Proof. exact (MK_COMB (@lem2519933) (@lem2519932 n n')). Qed.
Lemma lem2519936 (m : int) (n : int) : (term5 m n) = (rem m n).
Proof. exact (EQ_MP (@lem2519814 m n) (@lem2519813 m n)). Qed.
Lemma lem2519937 (n : nat) (n' : nat) : (term55 n n') = (term46 n n').
Proof. exact (@lem2519936 (int_of_num n) (int_of_num n')). Qed.
Lemma lem2519938 (n : nat) (n' : nat) : ((term54 n n') = (term55 n n')) = ((term46 n n') = (term46 n n')).
Proof. exact (MK_COMB (@lem2519934 n n') (@lem2519937 n n')). Qed.
Lemma lem2519940 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2519941 (x : int) : (x = x) = True.
Proof. exact (@lem2519940 int x). Qed.
Lemma lem2519942 (n : nat) (n' : nat) : ((term46 n n') = (term46 n n')) = True.
Proof. exact (@lem2519941 (term46 n n')). Qed.
Lemma lem2519943 (n : nat) (n' : nat) : ((term54 n n') = (term55 n n')) = True.
Proof. exact (TRANS (@lem2519938 n n') (@lem2519942 n n')). Qed.
Lemma lem2519944 (n : nat) : (term57 n) = term64.
Proof. exact (fun_ext (fun n' : nat => @lem2519943 n n')). Qed.
Lemma lem2519945 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519946 (n : nat) : (term59 n) = term65.
Proof. exact (MK_COMB (@lem2519945) (@lem2519944 n)). Qed.
Lemma lem2519948 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2519949 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2519948 nat t). Qed.
Lemma lem2519950 : term65 = True.
Proof. exact (@lem2519949 True). Qed.
Lemma lem2519951 (n : nat) : (term59 n) = True.
Proof. exact (TRANS (@lem2519946 n) (@lem2519950)). Qed.
Lemma lem2519952 (n : nat) : (term60 n) = (True /\ True).
Proof. exact (MK_COMB (@lem2519915 n) (@lem2519951 n)). Qed.
Lemma lem2519954 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2519955 : (True /\ True) = True.
Proof. exact (@lem2519954 True). Qed.
Lemma lem2519956 (n : nat) : (term60 n) = True.
Proof. exact (TRANS (@lem2519952 n) (@lem2519955)). Qed.
Lemma lem2519957 (n : nat) : (term21 n) = True.
Proof. exact (TRANS (@lem2519881 n) (@lem2519956 n)). Qed.
Lemma lem2519958 : term23 = term64.
Proof. exact (fun_ext (fun n : nat => @lem2519957 n)). Qed.
Lemma lem2519959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519960 : term25 = term65.
Proof. exact (MK_COMB (@lem2519959) (@lem2519958)). Qed.
Lemma lem2519962 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2519963 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2519962 nat t). Qed.
Lemma lem2519964 : term65 = True.
Proof. exact (@lem2519963 True). Qed.
Lemma lem2519965 : term25 = True.
Proof. exact (TRANS (@lem2519960) (@lem2519964)). Qed.
Lemma lem2519966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2519967 : term27 = (and True).
Proof. exact (MK_COMB (@lem2519966) (@lem2519965)). Qed.
Lemma lem2519979 (P : int -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem2519820 P) (@lem2519819 P)). Qed.
Lemma lem2519980 (n : nat) : (term70 n) = (term71 n).
Proof. exact (@lem2519979 (term72 n)). Qed.
Lemma lem2519981 (n : nat) (y : int) : (term73 n y) = ((term74 n y) = (term75 n y)).
Proof. exact (eq_refl (term73 n y)). Qed.
Lemma lem2519982 (n : nat) : (term76 n) = (term72 n).
Proof. exact (fun_ext (fun y : int => @lem2519981 n y)). Qed.
Lemma lem2519983 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2519984 (n : nat) : (term70 n) = (term29 n).
Proof. exact (MK_COMB (@lem2519983) (@lem2519982 n)). Qed.
Lemma lem2519985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2519986 (n : nat) : (term77 n) = (term78 n).
Proof. exact (MK_COMB (@lem2519985) (@lem2519984 n)). Qed.
Lemma lem2519987 (n : nat) (n' : nat) : (term79 n n') = ((term80 n n') = (term81 n n')).
Proof. exact (eq_refl (term79 n n')). Qed.
Lemma lem2519988 (n : nat) : (term82 n) = (term83 n).
Proof. exact (fun_ext (fun n' : nat => @lem2519987 n n')). Qed.
Lemma lem2519989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519990 (n : nat) : (term84 n) = (term85 n).
Proof. exact (MK_COMB (@lem2519989) (@lem2519988 n)). Qed.
Lemma lem2519991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2519992 (n : nat) : (term86 n) = (term87 n).
Proof. exact (MK_COMB (@lem2519991) (@lem2519990 n)). Qed.
Lemma lem2519993 (n : nat) (n' : nat) : (term88 n n') = ((term89 n n') = (term90 n n')).
Proof. exact (eq_refl (term88 n n')). Qed.
Lemma lem2519994 (n : nat) : (term91 n) = (term92 n).
Proof. exact (fun_ext (fun n' : nat => @lem2519993 n n')). Qed.
Lemma lem2519995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2519996 (n : nat) : (term93 n) = (term94 n).
Proof. exact (MK_COMB (@lem2519995) (@lem2519994 n)). Qed.
Lemma lem2519997 (n : nat) : (term71 n) = (term95 n).
Proof. exact (MK_COMB (@lem2519992 n) (@lem2519996 n)). Qed.
Lemma lem2519998 (n : nat) : ((term70 n) = (term71 n)) = ((term29 n) = (term95 n)).
Proof. exact (MK_COMB (@lem2519986 n) (@lem2519997 n)). Qed.
Lemma lem2519999 (n : nat) : (term29 n) = (term95 n).
Proof. exact (EQ_MP (@lem2519998 n) (@lem2519980 n)). Qed.
Lemma lem2520011 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2519808 n) (@lem2519807 n)). Qed.
Lemma lem2520012 (n' : nat) : (term1 n') = (int_of_num n').
Proof. exact (@lem2520011 n'). Qed.
Lemma lem2520013 (n : nat) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem2520014 (n : nat) (n' : nat) : (term80 n n') = (term81 n n').
Proof. exact (MK_COMB (@lem2520013 n) (@lem2520012 n')). Qed.
Lemma lem2520015 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2520016 (n : nat) (n' : nat) : (term97 n n') = (term98 n n').
Proof. exact (MK_COMB (@lem2520015) (@lem2520014 n n')). Qed.
Lemma lem2520017 (n : nat) (n' : nat) : (term81 n n') = (term81 n n').
Proof. exact (eq_refl (term81 n n')). Qed.
Lemma lem2520018 (n : nat) (n' : nat) : ((term80 n n') = (term81 n n')) = ((term81 n n') = (term81 n n')).
Proof. exact (MK_COMB (@lem2520016 n n') (@lem2520017 n n')). Qed.
Lemma lem2520020 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2520021 (x : int) : (x = x) = True.
Proof. exact (@lem2520020 int x). Qed.
Lemma lem2520022 (n : nat) (n' : nat) : ((term81 n n') = (term81 n n')) = True.
Proof. exact (@lem2520021 (term81 n n')). Qed.
Lemma lem2520023 (n : nat) (n' : nat) : ((term80 n n') = (term81 n n')) = True.
Proof. exact (TRANS (@lem2520018 n n') (@lem2520022 n n')). Qed.
Lemma lem2520024 (n : nat) : (term83 n) = term64.
Proof. exact (fun_ext (fun n' : nat => @lem2520023 n n')). Qed.
Lemma lem2520025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2520026 (n : nat) : (term85 n) = term65.
Proof. exact (MK_COMB (@lem2520025) (@lem2520024 n)). Qed.
Lemma lem2520028 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2520029 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2520028 nat t). Qed.
Lemma lem2520030 : term65 = True.
Proof. exact (@lem2520029 True). Qed.
Lemma lem2520031 (n : nat) : (term85 n) = True.
Proof. exact (TRANS (@lem2520026 n) (@lem2520030)). Qed.
Lemma lem2520032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2520033 (n : nat) : (term87 n) = (and True).
Proof. exact (MK_COMB (@lem2520032) (@lem2520031 n)). Qed.
Lemma lem2520043 (x : int) : (term7 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2519817 x) (@lem2519816 x)). Qed.
Lemma lem2520044 (n' : nat) : (term68 n') = (term1 n').
Proof. exact (@lem2520043 (int_of_num n')). Qed.
Lemma lem2520046 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2519808 n) (@lem2519807 n)). Qed.
Lemma lem2520047 (n' : nat) : (term1 n') = (int_of_num n').
Proof. exact (@lem2520046 n'). Qed.
Lemma lem2520048 (n' : nat) : (term68 n') = (int_of_num n').
Proof. exact (TRANS (@lem2520044 n') (@lem2520047 n')). Qed.
Lemma lem2520049 (n : nat) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem2520050 (n : nat) (n' : nat) : (term89 n n') = (term81 n n').
Proof. exact (MK_COMB (@lem2520049 n) (@lem2520048 n')). Qed.
Lemma lem2520051 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2520052 (n : nat) (n' : nat) : (term99 n n') = (term98 n n').
Proof. exact (MK_COMB (@lem2520051) (@lem2520050 n n')). Qed.
Lemma lem2520054 (m : int) (n : int) : (term5 m n) = (rem m n).
Proof. exact (EQ_MP (@lem2519814 m n) (@lem2519813 m n)). Qed.
Lemma lem2520055 (n : nat) (n' : nat) : (term90 n n') = (term81 n n').
Proof. exact (@lem2520054 (term100 n) (int_of_num n')). Qed.
Lemma lem2520056 (n : nat) (n' : nat) : ((term89 n n') = (term90 n n')) = ((term81 n n') = (term81 n n')).
Proof. exact (MK_COMB (@lem2520052 n n') (@lem2520055 n n')). Qed.
Lemma lem2520058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2520059 (x : int) : (x = x) = True.
Proof. exact (@lem2520058 int x). Qed.
Lemma lem2520060 (n : nat) (n' : nat) : ((term81 n n') = (term81 n n')) = True.
Proof. exact (@lem2520059 (term81 n n')). Qed.
Lemma lem2520061 (n : nat) (n' : nat) : ((term89 n n') = (term90 n n')) = True.
Proof. exact (TRANS (@lem2520056 n n') (@lem2520060 n n')). Qed.
Lemma lem2520062 (n : nat) : (term92 n) = term64.
Proof. exact (fun_ext (fun n' : nat => @lem2520061 n n')). Qed.
Lemma lem2520063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2520064 (n : nat) : (term94 n) = term65.
Proof. exact (MK_COMB (@lem2520063) (@lem2520062 n)). Qed.
Lemma lem2520066 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2520067 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2520066 nat t). Qed.
Lemma lem2520068 : term65 = True.
Proof. exact (@lem2520067 True). Qed.
Lemma lem2520069 (n : nat) : (term94 n) = True.
Proof. exact (TRANS (@lem2520064 n) (@lem2520068)). Qed.
Lemma lem2520070 (n : nat) : (term95 n) = (True /\ True).
Proof. exact (MK_COMB (@lem2520033 n) (@lem2520069 n)). Qed.
Lemma lem2520072 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2520073 : (True /\ True) = True.
Proof. exact (@lem2520072 True). Qed.
Lemma lem2520074 (n : nat) : (term95 n) = True.
Proof. exact (TRANS (@lem2520070 n) (@lem2520073)). Qed.
Lemma lem2520075 (n : nat) : (term29 n) = True.
Proof. exact (TRANS (@lem2519999 n) (@lem2520074 n)). Qed.
Lemma lem2520076 : term31 = term64.
Proof. exact (fun_ext (fun n : nat => @lem2520075 n)). Qed.
Lemma lem2520077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2520078 : term33 = term65.
Proof. exact (MK_COMB (@lem2520077) (@lem2520076)). Qed.
Lemma lem2520080 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2520081 (t : Prop) : (term67 t) = t.
Proof. exact (@lem2520080 nat t). Qed.
Lemma lem2520082 : term65 = True.
Proof. exact (@lem2520081 True). Qed.
Lemma lem2520083 : term33 = True.
Proof. exact (TRANS (@lem2520078) (@lem2520082)). Qed.
Lemma lem2520084 : term34 = (True /\ True).
Proof. exact (MK_COMB (@lem2519967) (@lem2520083)). Qed.
Lemma lem2520086 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2520087 : (True /\ True) = True.
Proof. exact (@lem2520086 True). Qed.
Lemma lem2520088 : term34 = True.
Proof. exact (TRANS (@lem2520084) (@lem2520087)). Qed.
Lemma lem2520089 : term17 = True.
Proof. exact (TRANS (@lem2519847) (@lem2520088)). Qed.
Lemma lem2520090 : True = term17.
Proof. exact (SYM (@lem2520089)). Qed.
Lemma lem2520091 : term17.
Proof. exact (EQ_MP (@lem2520090) (@lem0)). Qed.
