Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_ZPOW_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_ABS_INV_spec.
Require Import REAL_ABS_POW_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3179843 (x : real) : term0 x.
Proof. exact (@lem1582667 x). Qed.
Lemma lem3179844 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3179845 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3179844 x) (@lem3179843 x)). Qed.
Lemma lem3179846 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem3179845 x n). Qed.
Lemma lem3179847 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3179849 (x : real) : term5 x.
Proof. exact (@lem1594832 x). Qed.
Lemma lem3179850 (x : real) : (term5 x) = ((term6 x) = (term7 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem3179852 : term8.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3179853 (x : real) : term9 x.
Proof. exact (@lem3179852 x). Qed.
Lemma lem3179854 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem3179855 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem3179854 x) (@lem3179853 x)). Qed.
Lemma lem3179856 (x : real) (n : nat) : term11 x n.
Proof. exact (@lem3179855 x n). Qed.
Lemma lem3179857 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem3179859 : term14.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3179860 (x : real) : term15 x.
Proof. exact (@lem3179859 x). Qed.
Lemma lem3179861 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem3179862 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem3179861 x) (@lem3179860 x)). Qed.
Lemma lem3179863 (x : real) (n : nat) : term17 x n.
Proof. exact (@lem3179862 x n). Qed.
Lemma lem3179864 (x : real) (n : nat) : (term17 x n) = ((term18 x n) = (real_pow x n)).
Proof. exact (eq_refl (term17 x n)). Qed.
Lemma lem3179866 (P : int -> Prop) : term19 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3179867 (P : int -> Prop) : (term19 P) = ((term20 P) = (term21 P)).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem3179880 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem3179867 P) (@lem3179866 P)). Qed.
Lemma lem3179881 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem3179880 (term24 x)). Qed.
Lemma lem3179882 (x : real) (n : int) : (term25 x n) = ((term26 x n) = (term27 x n)).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem3179883 (x : real) : (term28 x) = (term24 x).
Proof. exact (fun_ext (fun n : int => @lem3179882 x n)). Qed.
Lemma lem3179884 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179885 (x : real) : (term22 x) = (term29 x).
Proof. exact (MK_COMB (@lem3179884) (@lem3179883 x)). Qed.
Lemma lem3179886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179887 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem3179886) (@lem3179885 x)). Qed.
Lemma lem3179888 (x : real) (n : nat) : (term32 x n) = ((term33 x n) = (term34 x n)).
Proof. exact (eq_refl (term32 x n)). Qed.
Lemma lem3179889 (x : real) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun n : nat => @lem3179888 x n)). Qed.
Lemma lem3179890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179891 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3179890) (@lem3179889 x)). Qed.
Lemma lem3179892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179893 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem3179892) (@lem3179891 x)). Qed.
Lemma lem3179894 (x : real) (n : nat) : (term41 x n) = ((term42 x n) = (term43 x n)).
Proof. exact (eq_refl (term41 x n)). Qed.
Lemma lem3179895 (x : real) : (term44 x) = (term45 x).
Proof. exact (fun_ext (fun n : nat => @lem3179894 x n)). Qed.
Lemma lem3179896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179897 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem3179896) (@lem3179895 x)). Qed.
Lemma lem3179898 (x : real) : (term23 x) = (term48 x).
Proof. exact (MK_COMB (@lem3179893 x) (@lem3179897 x)). Qed.
Lemma lem3179899 (x : real) : ((term22 x) = (term23 x)) = ((term29 x) = (term48 x)).
Proof. exact (MK_COMB (@lem3179887 x) (@lem3179898 x)). Qed.
Lemma lem3179900 (x : real) : (term29 x) = (term48 x).
Proof. exact (EQ_MP (@lem3179899 x) (@lem3179881 x)). Qed.
Lemma lem3179912 (x : real) (n : nat) : (term18 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3179864 x n) (@lem3179863 x n)). Qed.
Lemma lem3179913 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem3179914 (x : real) (n : nat) : (term33 x n) = (term3 x n).
Proof. exact (MK_COMB (@lem3179913) (@lem3179912 x n)). Qed.
Lemma lem3179916 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem3179847 x n) (@lem3179846 x n)). Qed.
Lemma lem3179917 (x : real) (n : nat) : (term33 x n) = (term4 x n).
Proof. exact (TRANS (@lem3179914 x n) (@lem3179916 x n)). Qed.
Lemma lem3179918 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3179919 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem3179918) (@lem3179917 x n)). Qed.
Lemma lem3179921 (x : real) (n : nat) : (term18 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3179864 x n) (@lem3179863 x n)). Qed.
Lemma lem3179922 (x : real) (n : nat) : (term34 x n) = (term4 x n).
Proof. exact (@lem3179921 (real_abs x) n). Qed.
Lemma lem3179923 (x : real) (n : nat) : ((term33 x n) = (term34 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem3179919 x n) (@lem3179922 x n)). Qed.
Lemma lem3179925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3179926 (x : real) : (x = x) = True.
Proof. exact (@lem3179925 real x). Qed.
Lemma lem3179927 (x : real) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem3179926 (term4 x n)). Qed.
Lemma lem3179928 (x : real) (n : nat) : ((term33 x n) = (term34 x n)) = True.
Proof. exact (TRANS (@lem3179923 x n) (@lem3179927 x n)). Qed.
Lemma lem3179929 (x : real) : (term36 x) = term51.
Proof. exact (fun_ext (fun n : nat => @lem3179928 x n)). Qed.
Lemma lem3179930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179931 (x : real) : (term38 x) = term52.
Proof. exact (MK_COMB (@lem3179930) (@lem3179929 x)). Qed.
Lemma lem3179933 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179934 (t : Prop) : (term54 t) = t.
Proof. exact (@lem3179933 nat t). Qed.
Lemma lem3179935 : term52 = True.
Proof. exact (@lem3179934 True). Qed.
Lemma lem3179936 (x : real) : (term38 x) = True.
Proof. exact (TRANS (@lem3179931 x) (@lem3179935)). Qed.
Lemma lem3179937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179938 (x : real) : (term40 x) = (and True).
Proof. exact (MK_COMB (@lem3179937) (@lem3179936 x)). Qed.
Lemma lem3179948 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem3179857 x n) (@lem3179856 x n)). Qed.
Lemma lem3179949 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem3179950 (x : real) (n : nat) : (term42 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem3179949) (@lem3179948 x n)). Qed.
Lemma lem3179952 (x : real) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem3179850 x) (@lem3179849 x)). Qed.
Lemma lem3179953 (x : real) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (@lem3179952 (real_pow x n)). Qed.
Lemma lem3179955 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem3179847 x n) (@lem3179846 x n)). Qed.
Lemma lem3179956 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3179957 (x : real) (n : nat) : (term56 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem3179956) (@lem3179955 x n)). Qed.
Lemma lem3179958 (x : real) (n : nat) : (term55 x n) = (term57 x n).
Proof. exact (TRANS (@lem3179953 x n) (@lem3179957 x n)). Qed.
Lemma lem3179959 (x : real) (n : nat) : (term42 x n) = (term57 x n).
Proof. exact (TRANS (@lem3179950 x n) (@lem3179958 x n)). Qed.
Lemma lem3179960 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3179961 (x : real) (n : nat) : (term58 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem3179960) (@lem3179959 x n)). Qed.
Lemma lem3179963 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem3179857 x n) (@lem3179856 x n)). Qed.
Lemma lem3179964 (x : real) (n : nat) : (term43 x n) = (term57 x n).
Proof. exact (@lem3179963 (real_abs x) n). Qed.
Lemma lem3179965 (x : real) (n : nat) : ((term42 x n) = (term43 x n)) = ((term57 x n) = (term57 x n)).
Proof. exact (MK_COMB (@lem3179961 x n) (@lem3179964 x n)). Qed.
Lemma lem3179967 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3179968 (x : real) : (x = x) = True.
Proof. exact (@lem3179967 real x). Qed.
Lemma lem3179969 (x : real) (n : nat) : ((term57 x n) = (term57 x n)) = True.
Proof. exact (@lem3179968 (term57 x n)). Qed.
Lemma lem3179970 (x : real) (n : nat) : ((term42 x n) = (term43 x n)) = True.
Proof. exact (TRANS (@lem3179965 x n) (@lem3179969 x n)). Qed.
Lemma lem3179971 (x : real) : (term45 x) = term51.
Proof. exact (fun_ext (fun n : nat => @lem3179970 x n)). Qed.
Lemma lem3179972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179973 (x : real) : (term47 x) = term52.
Proof. exact (MK_COMB (@lem3179972) (@lem3179971 x)). Qed.
Lemma lem3179975 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179976 (t : Prop) : (term54 t) = t.
Proof. exact (@lem3179975 nat t). Qed.
Lemma lem3179977 : term52 = True.
Proof. exact (@lem3179976 True). Qed.
Lemma lem3179978 (x : real) : (term47 x) = True.
Proof. exact (TRANS (@lem3179973 x) (@lem3179977)). Qed.
Lemma lem3179979 (x : real) : (term48 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3179938 x) (@lem3179978 x)). Qed.
Lemma lem3179981 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3179982 : (True /\ True) = True.
Proof. exact (@lem3179981 True). Qed.
Lemma lem3179983 (x : real) : (term48 x) = True.
Proof. exact (TRANS (@lem3179979 x) (@lem3179982)). Qed.
Lemma lem3179984 (x : real) : (term29 x) = True.
Proof. exact (TRANS (@lem3179900 x) (@lem3179983 x)). Qed.
Lemma lem3179985 : term60 = term61.
Proof. exact (fun_ext (fun x : real => @lem3179984 x)). Qed.
Lemma lem3179986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179987 : term62 = term63.
Proof. exact (MK_COMB (@lem3179986) (@lem3179985)). Qed.
Lemma lem3179989 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179990 (t : Prop) : (term64 t) = t.
Proof. exact (@lem3179989 real t). Qed.
Lemma lem3179991 : term63 = True.
Proof. exact (@lem3179990 True). Qed.
Lemma lem3179992 : term62 = True.
Proof. exact (TRANS (@lem3179987) (@lem3179991)). Qed.
Lemma lem3179993 : True = term62.
Proof. exact (SYM (@lem3179992)). Qed.
Lemma lem3179994 : term62.
Proof. exact (EQ_MP (@lem3179993) (@lem0)). Qed.
