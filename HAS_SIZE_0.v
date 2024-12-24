Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_0_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_RULES_spec.
Require Import HAS_SIZE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3863853 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem3863854 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3863855 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3863854 A x) (@lem3863853 A x)). Qed.
Lemma lem3863856 {A : Type'} (x : A) (s : A -> Prop) : term2 A x s.
Proof. exact (@lem3863855 A x s). Qed.
Lemma lem3863857 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term3 A x s).
Proof. exact (eq_refl (term2 A x s)). Qed.
Lemma lem3863858 {A : Type'} (x : A) (s : A -> Prop) : term3 A x s.
Proof. exact (EQ_MP (@lem3863857 A x s) (@lem3863856 A x s)). Qed.
Lemma lem3863859 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem3863872 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem3863873 {A : Type'} (P : type686 A) (h1 : term5 A) : term6 A P.
Proof. exact (@lem3863872 A h1 P). Qed.
Lemma lem3863874 {A : Type'} (P : type686 A) : (term6 A P) = (term7 A P).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem3863875 {A : Type'} (P : type686 A) (h1 : term5 A) : term7 A P.
Proof. exact (EQ_MP (@lem3863874 A P) (@lem3863873 A P h1)). Qed.
Lemma lem3863876 {A : Type'} (P : type686 A) (h1 : term8 A P) : term8 A P.
Proof. exact (h1). Qed.
Lemma lem3863877 {A : Type'} (P : type686 A) (h1 : term5 A) (h2 : term8 A P) : term9 A P.
Proof. exact (@lem3863875 A P h1 (@lem3863876 A P h2)). Qed.
Lemma lem3863878 {A : Type'} (P : type686 A) (h1 : term8 A P) : term10 A P.
Proof. exact (fun h0 : term5 A => @lem3863877 A P h0 h1). Qed.
Lemma lem3863879 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem3863880 {A : Type'} (P : type686 A) (h1 : term5 A) (h2 : term8 A P) : term9 A P.
Proof. exact (@lem3863878 A P h2 (@lem3863879 A h1)). Qed.
Lemma lem3863881 {A : Type'} (P : type686 A) (h1 : term5 A) : term7 A P.
Proof. exact (fun h0 : term8 A P => @lem3863880 A P h1 h0). Qed.
Lemma lem3863882 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (fun P : type686 A => @lem3863881 A P h1). Qed.
Lemma lem3863883 {A : Type'} : term11 A.
Proof. exact (fun h0 : term5 A => @lem3863882 A h0). Qed.
Lemma lem3863884 {A : Type'} : term5 A.
Proof. exact (@lem3863883 A (@lem3558722 A)). Qed.
Lemma lem3863885 {A : Type'} (P : type686 A) : term6 A P.
Proof. exact (@lem3863884 A P). Qed.
Lemma lem3863886 {A : Type'} (P : type686 A) : (term6 A P) = (term7 A P).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem3863888 {_100044 : Type'} (s : _100044 -> Prop) : term12 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3863889 {_100044 : Type'} (s : _100044 -> Prop) : (term12 _100044 s) = (term13 _100044 s).
Proof. exact (eq_refl (term12 _100044 s)). Qed.
Lemma lem3863890 {_100044 : Type'} (s : _100044 -> Prop) : term13 _100044 s.
Proof. exact (EQ_MP (@lem3863889 _100044 s) (@lem3863888 _100044 s)). Qed.
Lemma lem3863891 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term14 _100044 s n.
Proof. exact (@lem3863890 _100044 s n). Qed.
Lemma lem3863892 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term14 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term15 _100044 s n)).
Proof. exact (eq_refl (term14 _100044 s n)). Qed.
Lemma lem3863897 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3863892 _100044 s n) (@lem3863891 _100044 s n)). Qed.
Lemma lem3863898 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term15 A s n).
Proof. exact (@lem3863897 A s n). Qed.
Lemma lem3863899 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (@lem3863898 A s (NUMERAL 0)). Qed.
Lemma lem3863904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3863905 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3863904) (@lem3863899 A s)). Qed.
Lemma lem3863908 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem3863909 {A : Type'} (s : A -> Prop) : ((term16 A s) = (s = (@EMPTY A))) = ((term17 A s) = (s = (@EMPTY A))).
Proof. exact (MK_COMB (@lem3863905 A s) (@lem3863908 A s)). Qed.
Lemma lem3863912 {A : Type'} (s : A -> Prop) : ((term17 A s) = (s = (@EMPTY A))) = ((term16 A s) = (s = (@EMPTY A))).
Proof. exact (SYM (@lem3863909 A s)). Qed.
Lemma lem3863913 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : term17 A s.
Proof. exact (h1). Qed.
Lemma lem3863964 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3863965 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3863970 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3863971 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3863972 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3863971 A) (@lem3863970 A s h1)). Qed.
Lemma lem3863974 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3863965 A) (@lem3863964 A)). Qed.
Lemma lem3863975 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = True.
Proof. exact (TRANS (@lem3863972 A s h1) (@lem3863974 A)). Qed.
Lemma lem3863976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3863977 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term20 A s) = (and True).
Proof. exact (MK_COMB (@lem3863976) (@lem3863975 A s h1)). Qed.
Lemma lem3863981 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3863982 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3863983 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CARD A s) = (@CARD A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3863982 A) (@lem3863981 A s h1)). Qed.
Lemma lem3863985 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3863986 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CARD A s) = (NUMERAL 0).
Proof. exact (TRANS (@lem3863983 A s h1) (@lem3863985 A)). Qed.
Lemma lem3863987 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3863988 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term21 A s) = term22.
Proof. exact (MK_COMB (@lem3863987) (@lem3863986 A s h1)). Qed.
Lemma lem3863989 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3863990 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((@CARD A s) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3863988 A s h1) (@lem3863989)). Qed.
Lemma lem3863992 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3863993 (x : nat) : (x = x) = True.
Proof. exact (@lem3863992 nat x). Qed.
Lemma lem3863994 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3863993 (NUMERAL 0)). Qed.
Lemma lem3863995 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((@CARD A s) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem3863990 A s h1) (@lem3863994)). Qed.
Lemma lem3863996 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term17 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem3863977 A s h1) (@lem3863995 A s h1)). Qed.
Lemma lem3863998 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3863999 : (True /\ True) = True.
Proof. exact (@lem3863998 True). Qed.
Lemma lem3864000 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term17 A s) = True.
Proof. exact (TRANS (@lem3863996 A s h1) (@lem3863999)). Qed.
Lemma lem3864001 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : True = (term17 A s).
Proof. exact (SYM (@lem3864000 A s h1)). Qed.
Lemma lem3864002 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : term17 A s.
Proof. exact (EQ_MP (@lem3864001 A s h1) (@lem0)). Qed.
Lemma lem3864003 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : (@CARD A s) = (NUMERAL 0).
Proof. exact (proj2 (@lem3863913 A s h1)). Qed.
Lemma lem3864004 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : @FINITE A s.
Proof. exact (proj1 (@lem3863913 A s h1)). Qed.
Lemma lem3864006 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (EQ_MP (@lem3863886 A P) (@lem3863885 A P)). Qed.
Lemma lem3864007 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (@lem3864006 A P). Qed.
Lemma lem3864008 {A : Type'} : term23 A.
Proof. exact (@lem3864007 A (term24 A)). Qed.
Lemma lem3864009 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3864010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864011 {A : Type'} : (term27 A) = (term28 A).
Proof. exact (MK_COMB (@lem3864010) (@lem3864009 A)). Qed.
Lemma lem3864012 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem3864013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864014 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3864013) (@lem3864012 A s)). Qed.
Lemma lem3864015 {A : Type'} (x : A) (s : A -> Prop) : (term33 A x s) = (term33 A x s).
Proof. exact (eq_refl (term33 A x s)). Qed.
Lemma lem3864016 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (term35 A x s).
Proof. exact (MK_COMB (@lem3864014 A s) (@lem3864015 A x s)). Qed.
Lemma lem3864017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3864018 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term37 A x s).
Proof. exact (MK_COMB (@lem3864017) (@lem3864016 A x s)). Qed.
Lemma lem3864019 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term39 A x s).
Proof. exact (eq_refl (term38 A x s)). Qed.
Lemma lem3864020 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = (term41 A x s).
Proof. exact (MK_COMB (@lem3864018 A x s) (@lem3864019 A x s)). Qed.
Lemma lem3864021 {A : Type'} (x : A) : (term42 A x) = (term43 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3864020 A x s)). Qed.
Lemma lem3864022 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3864023 {A : Type'} (x : A) : (term44 A x) = (term45 A x).
Proof. exact (MK_COMB (@lem3864022 A) (@lem3864021 A x)). Qed.
Lemma lem3864024 {A : Type'} : (term46 A) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem3864023 A x)). Qed.
Lemma lem3864025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864026 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (MK_COMB (@lem3864025 A) (@lem3864024 A)). Qed.
Lemma lem3864027 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (MK_COMB (@lem3864011 A) (@lem3864026 A)). Qed.
Lemma lem3864028 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3864029 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (MK_COMB (@lem3864028) (@lem3864027 A)). Qed.
Lemma lem3864030 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem3864031 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (eq_refl (term54 A s)). Qed.
Lemma lem3864032 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3864031 A s) (@lem3864030 A s)). Qed.
Lemma lem3864033 {A : Type'} : (term57 A) = (term58 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3864032 A s)). Qed.
Lemma lem3864034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3864035 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (MK_COMB (@lem3864034 A) (@lem3864033 A)). Qed.
Lemma lem3864036 {A : Type'} : (term23 A) = (term61 A).
Proof. exact (MK_COMB (@lem3864029 A) (@lem3864035 A)). Qed.
Lemma lem3864037 {A : Type'} : term61 A.
Proof. exact (EQ_MP (@lem3864036 A) (@lem3864008 A)). Qed.
Lemma lem3864047 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3864048 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3864047 (A -> Prop) x). Qed.
Lemma lem3864049 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3864048 A (@EMPTY A)). Qed.
Lemma lem3864050 {A : Type'} : (term62 A) = (term62 A).
Proof. exact (eq_refl (term62 A)). Qed.
Lemma lem3864051 {A : Type'} : (term26 A) = (term63 A).
Proof. exact (MK_COMB (@lem3864050 A) (@lem3864049 A)). Qed.
Lemma lem3864055 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3864056 {A : Type'} : (term63 A) = True.
Proof. exact (@lem3864055 ((@CARD A (@EMPTY A)) = (NUMERAL 0))). Qed.
Lemma lem3864057 {A : Type'} : (term26 A) = True.
Proof. exact (TRANS (@lem3864051 A) (@lem3864056 A)). Qed.
Lemma lem3864058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864059 {A : Type'} : (term28 A) = (and True).
Proof. exact (MK_COMB (@lem3864058) (@lem3864057 A)). Qed.
Lemma lem3864089 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem3863859 A x s (@lem3863858 A x s)). Qed.
Lemma lem3864090 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem3864089 A x s). Qed.
Lemma lem3864091 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = (term64 A x s).
Proof. exact (eq_refl (term64 A x s)). Qed.
Lemma lem3864092 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term65 A x s).
Proof. exact (MK_COMB (@lem3864091 A x s) (@lem3864090 A x s)). Qed.
Lemma lem3864096 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3864097 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term66 A x s).
Proof. exact (@lem3864096 ((term67 A x s) = (NUMERAL 0))). Qed.
Lemma lem3864100 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term66 A x s).
Proof. exact (TRANS (@lem3864092 A x s) (@lem3864097 A x s)). Qed.
Lemma lem3864101 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term37 A x s).
Proof. exact (eq_refl (term37 A x s)). Qed.
Lemma lem3864102 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term68 A x s).
Proof. exact (MK_COMB (@lem3864101 A x s) (@lem3864100 A x s)). Qed.
Lemma lem3864105 {A : Type'} (x : A) : (term43 A x) = (term69 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3864102 A x s)). Qed.
Lemma lem3864106 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3864107 {A : Type'} (x : A) : (term45 A x) = (term70 A x).
Proof. exact (MK_COMB (@lem3864106 A) (@lem3864105 A x)). Qed.
Lemma lem3864112 {A : Type'} : (term47 A) = (term71 A).
Proof. exact (fun_ext (fun x : A => @lem3864107 A x)). Qed.
Lemma lem3864113 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864114 {A : Type'} : (term49 A) = (term72 A).
Proof. exact (MK_COMB (@lem3864113 A) (@lem3864112 A)). Qed.
Lemma lem3864119 {A : Type'} : (term51 A) = (term73 A).
Proof. exact (MK_COMB (@lem3864059 A) (@lem3864114 A)). Qed.
Lemma lem3864121 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3864122 {A : Type'} : (term73 A) = (term72 A).
Proof. exact (@lem3864121 (term72 A)). Qed.
Lemma lem3864147 {A : Type'} : (term51 A) = (term72 A).
Proof. exact (TRANS (@lem3864119 A) (@lem3864122 A)). Qed.
Lemma lem3864148 {A : Type'} : (term72 A) = (term51 A).
Proof. exact (SYM (@lem3864147 A)). Qed.
Lemma lem3864149 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term35 A x s') : term35 A x s'.
Proof. exact (h1). Qed.
Lemma lem3864150 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term33 A x s') : term33 A x s'.
Proof. exact (h1). Qed.
Lemma lem3864152 {A : Type'} (s' : A -> Prop) (h1 : @FINITE A s') : @FINITE A s'.
Proof. exact (h1). Qed.
Lemma lem3864153 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : term74 A x s'.
Proof. exact (h1). Qed.
Lemma lem3864154 {A : Type'} : term75 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3864155 {A : Type'} (h1 : term75 A) : term75 A.
Proof. exact (h1). Qed.
Lemma lem3864156 {A : Type'} (x : A) (h1 : term75 A) : term76 A x.
Proof. exact (@lem3864155 A h1 x). Qed.
Lemma lem3864157 {A : Type'} (x : A) : (term76 A x) = (term77 A x).
Proof. exact (eq_refl (term76 A x)). Qed.
Lemma lem3864158 {A : Type'} (x : A) (h1 : term75 A) : term77 A x.
Proof. exact (EQ_MP (@lem3864157 A x) (@lem3864156 A x h1)). Qed.
Lemma lem3864159 {A : Type'} (x : A) (s : A -> Prop) (h1 : term75 A) : term78 A x s.
Proof. exact (@lem3864158 A x h1 s). Qed.
Lemma lem3864160 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term79 A x s).
Proof. exact (eq_refl (term78 A x s)). Qed.
Lemma lem3864161 {A : Type'} (x : A) (s : A -> Prop) (h1 : term75 A) : term79 A x s.
Proof. exact (EQ_MP (@lem3864160 A x s) (@lem3864159 A x s h1)). Qed.
Lemma lem3864162 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3864163 {A : Type'} (x : A) (s : A -> Prop) (h1 : term75 A) (h2 : @FINITE A s) : (term67 A x s) = (term80 A x s).
Proof. exact (@lem3864161 A x s h1 (@lem3864162 A s h2)). Qed.
Lemma lem3864164 {A : Type'} (s : A -> Prop) (h1 : term75 A) (h2 : @FINITE A s) : term81 A s.
Proof. exact (fun x : A => @lem3864163 A x s h1 h2). Qed.
Lemma lem3864165 {A : Type'} (s : A -> Prop) (h1 : term75 A) : term82 A s.
Proof. exact (fun h0 : @FINITE A s => @lem3864164 A s h1 h0). Qed.
Lemma lem3864166 {A : Type'} (h1 : term75 A) : term83 A.
Proof. exact (fun s : A -> Prop => @lem3864165 A s h1). Qed.
Lemma lem3864167 {A : Type'} : term84 A.
Proof. exact (fun h0 : term75 A => @lem3864166 A h0). Qed.
Lemma lem3864168 {A : Type'} : term83 A.
Proof. exact (@lem3864167 A (@lem3864154 A)). Qed.
Lemma lem3864169 {A : Type'} (s : A -> Prop) : term85 A s.
Proof. exact (@lem3864168 A s). Qed.
Lemma lem3864170 {A : Type'} (s : A -> Prop) : (term85 A s) = (term82 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem3864173 {A : Type'} (s : A -> Prop) : term82 A s.
Proof. exact (EQ_MP (@lem3864170 A s) (@lem3864169 A s)). Qed.
Lemma lem3864174 {A : Type'} (s : A -> Prop) : term82 A s.
Proof. exact (@lem3864173 A s). Qed.
Lemma lem3864175 {A : Type'} (s' : A -> Prop) : term82 A s'.
Proof. exact (@lem3864174 A s'). Qed.
Lemma lem3864176 {A : Type'} (s' : A -> Prop) (h1 : @FINITE A s') : term81 A s'.
Proof. exact (@lem3864175 A s' (@lem3864152 A s' h1)). Qed.
Lemma lem3864177 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : term86 A s' x.
Proof. exact (@lem3864176 A s' h1 x). Qed.
Lemma lem3864178 {A : Type'} (x : A) (s' : A -> Prop) : (term86 A s' x) = ((term67 A x s') = (term80 A x s')).
Proof. exact (eq_refl (term86 A s' x)). Qed.
Lemma lem3864183 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : (term67 A x s') = (term80 A x s').
Proof. exact (EQ_MP (@lem3864178 A x s') (@lem3864177 A x s' h1)). Qed.
Lemma lem3864184 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : (term67 A x s') = (term80 A x s').
Proof. exact (@lem3864183 A x s' h1). Qed.
Lemma lem3864185 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3864186 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : (term87 A x s') = (term88 A x s').
Proof. exact (MK_COMB (@lem3864185) (@lem3864184 A x s' h1)). Qed.
Lemma lem3864187 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3864188 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : ((term67 A x s') = (NUMERAL 0)) = ((term80 A x s') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3864186 A x s' h1) (@lem3864187)). Qed.
Lemma lem3864191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864192 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : (term66 A x s') = (term89 A x s').
Proof. exact (MK_COMB (@lem3864191) (@lem3864188 A x s' h1)). Qed.
Lemma lem3864193 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') : (term89 A x s') = (term66 A x s').
Proof. exact (SYM (@lem3864192 A x s' h1)). Qed.
Lemma lem3864194 (n : nat) : term90 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem3864195 (n : nat) : (term90 n) = (term91 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem3864196 (n : nat) : term91 n.
Proof. exact (EQ_MP (@lem3864195 n) (@lem3864194 n)). Qed.
Lemma lem3864197 (n : nat) : term92 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem3864216 {A : Type'} (x : A) (s' : A -> Prop) : term93 A x s'.
Proof. exact (@lem82 (@IN A x s')). Qed.
Lemma lem3864223 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (@IN A x s') = False.
Proof. exact (@lem3864216 A x s' (@lem3864153 A x s' h1)). Qed.
Lemma lem3864224 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem3864225 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term94 A x s') = (@COND nat False).
Proof. exact (MK_COMB (@lem3864224) (@lem3864223 A x s' h1)). Qed.
Lemma lem3864226 {A : Type'} (s' : A -> Prop) : (@CARD A s') = (@CARD A s').
Proof. exact (eq_refl (@CARD A s')). Qed.
Lemma lem3864227 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term95 A x s') = (term96 A s').
Proof. exact (MK_COMB (@lem3864225 A x s' h1) (@lem3864226 A s')). Qed.
Lemma lem3864228 {A : Type'} (s' : A -> Prop) : (term97 A s') = (term97 A s').
Proof. exact (eq_refl (term97 A s')). Qed.
Lemma lem3864229 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term80 A x s') = (term98 A s').
Proof. exact (MK_COMB (@lem3864227 A x s' h1) (@lem3864228 A s')). Qed.
Lemma lem3864231 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3864232 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3864231 nat t1 t2). Qed.
Lemma lem3864233 {A : Type'} (s' : A -> Prop) : (term98 A s') = (term97 A s').
Proof. exact (@lem3864232 (@CARD A s') (term97 A s')). Qed.
Lemma lem3864234 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term80 A x s') = (term97 A s').
Proof. exact (TRANS (@lem3864229 A x s' h1) (@lem3864233 A s')). Qed.
Lemma lem3864235 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3864236 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term88 A x s') = (term99 A s').
Proof. exact (MK_COMB (@lem3864235) (@lem3864234 A x s' h1)). Qed.
Lemma lem3864237 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3864238 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : ((term80 A x s') = (NUMERAL 0)) = ((term97 A s') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3864236 A x s' h1) (@lem3864237)). Qed.
Lemma lem3864240 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem3864197 n (@lem3864196 n)). Qed.
Lemma lem3864241 {A : Type'} (s' : A -> Prop) : ((term97 A s') = (NUMERAL 0)) = False.
Proof. exact (@lem3864240 (@CARD A s')). Qed.
Lemma lem3864242 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : ((term80 A x s') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem3864238 A x s' h1) (@lem3864241 A s')). Qed.
Lemma lem3864243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864244 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term89 A x s') = (~ False).
Proof. exact (MK_COMB (@lem3864243) (@lem3864242 A x s' h1)). Qed.
Lemma lem3864246 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3864247 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : (term89 A x s') = True.
Proof. exact (TRANS (@lem3864244 A x s' h1) (@lem3864246)). Qed.
Lemma lem3864248 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : True = (term89 A x s').
Proof. exact (SYM (@lem3864247 A x s' h1)). Qed.
Lemma lem3864249 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') : term89 A x s'.
Proof. exact (EQ_MP (@lem3864248 A x s' h1) (@lem0)). Qed.
Lemma lem3864250 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') (h2 : term74 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864193 A x s' h1) (@lem3864249 A x s' h2)). Qed.
Lemma lem3864251 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term35 A x s') : term33 A x s'.
Proof. exact (proj2 (@lem3864149 A x s' h1)). Qed.
Lemma lem3864253 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term33 A x s') : @FINITE A s'.
Proof. exact (proj2 (@lem3864150 A x s' h1)). Qed.
Lemma lem3864254 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term33 A x s') : term74 A x s'.
Proof. exact (proj1 (@lem3864150 A x s' h1)). Qed.
Lemma lem3864255 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') (h2 : term74 A x s') : (@FINITE A s') = (term66 A x s').
Proof. exact (prop_ext (fun h3 : @FINITE A s' => @lem3864250 A x s' h1 h2) (fun h3 : term66 A x s' => @lem3864152 A s' h1)). Qed.
Lemma lem3864256 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') (h2 : term74 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864255 A x s' h1 h2) (@lem3864152 A s' h1)). Qed.
Lemma lem3864257 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') (h2 : term74 A x s') : (term74 A x s') = (term66 A x s').
Proof. exact (prop_ext (fun h3 : term74 A x s' => @lem3864256 A x s' h1 h2) (fun h3 : term66 A x s' => @lem3864153 A x s' h2)). Qed.
Lemma lem3864258 {A : Type'} (x : A) (s' : A -> Prop) (h1 : @FINITE A s') (h2 : term74 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864257 A x s' h1 h2) (@lem3864153 A x s' h2)). Qed.
Lemma lem3864259 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') (h2 : term33 A x s') : (@FINITE A s') = (term66 A x s').
Proof. exact (prop_ext (fun h3 : @FINITE A s' => @lem3864258 A x s' h3 h1) (fun h3 : term66 A x s' => @lem3864253 A x s' h2)). Qed.
Lemma lem3864260 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term74 A x s') (h2 : term33 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864259 A x s' h1 h2) (@lem3864253 A x s' h2)). Qed.
Lemma lem3864261 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term33 A x s') : (term74 A x s') = (term66 A x s').
Proof. exact (prop_ext (fun h2 : term74 A x s' => @lem3864260 A x s' h2 h1) (fun h2 : term66 A x s' => @lem3864254 A x s' h1)). Qed.
Lemma lem3864262 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term33 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864261 A x s' h1) (@lem3864254 A x s' h1)). Qed.
Lemma lem3864263 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term35 A x s') : (term33 A x s') = (term66 A x s').
Proof. exact (prop_ext (fun h2 : term33 A x s' => @lem3864262 A x s' h2) (fun h2 : term66 A x s' => @lem3864251 A x s' h1)). Qed.
Lemma lem3864264 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term35 A x s') : term66 A x s'.
Proof. exact (EQ_MP (@lem3864263 A x s' h1) (@lem3864251 A x s' h1)). Qed.
Lemma lem3864265 {A : Type'} (x : A) (s' : A -> Prop) : term68 A x s'.
Proof. exact (fun h0 : term35 A x s' => @lem3864264 A x s' h0). Qed.
Lemma lem3864270 {A : Type'} (x : A) : term70 A x.
Proof. exact (fun s' : A -> Prop => @lem3864265 A x s'). Qed.
Lemma lem3864275 {A : Type'} : term72 A.
Proof. exact (fun x : A => @lem3864270 A x). Qed.
Lemma lem3864276 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3864148 A) (@lem3864275 A)). Qed.
Lemma lem3864277 {A : Type'} : term60 A.
Proof. exact (@lem3864037 A (@lem3864276 A)). Qed.
Lemma lem3864278 {A : Type'} (s : A -> Prop) : term100 A s.
Proof. exact (@lem3864277 A s). Qed.
Lemma lem3864279 {A : Type'} (s : A -> Prop) : (term100 A s) = (term56 A s).
Proof. exact (eq_refl (term100 A s)). Qed.
Lemma lem3864280 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (EQ_MP (@lem3864279 A s) (@lem3864278 A s)). Qed.
Lemma lem3864281 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : term30 A s.
Proof. exact (@lem3864280 A s (@lem3864004 A s h1)). Qed.
Lemma lem3864283 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : s = (@EMPTY A).
Proof. exact (@lem3864281 A s h1 (@lem3864003 A s h1)). Qed.
Lemma lem3864284 {A : Type'} (s : A -> Prop) : term101 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem3864002 A s h0). Qed.
Lemma lem3864285 {A : Type'} (s : A -> Prop) : term102 A s.
Proof. exact (fun h0 : term17 A s => @lem3864283 A s h0). Qed.
Lemma lem3864286 {A : Type'} (s : A -> Prop) : term103 A s.
Proof. exact (conj (@lem3864285 A s) (@lem3864284 A s)). Qed.
Lemma lem3864287 {A : Type'} (s : A -> Prop) : (term103 A s) = ((term17 A s) = (s = (@EMPTY A))).
Proof. exact (@lem32 (term17 A s) (s = (@EMPTY A))). Qed.
Lemma lem3864288 {A : Type'} (s : A -> Prop) : (term17 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3864287 A s) (@lem3864286 A s)). Qed.
Lemma lem3864289 {A : Type'} (s : A -> Prop) : (term16 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3863912 A s) (@lem3864288 A s)). Qed.
Lemma lem3864294 {A : Type'} : term104 A.
Proof. exact (fun s : A -> Prop => @lem3864289 A s). Qed.
