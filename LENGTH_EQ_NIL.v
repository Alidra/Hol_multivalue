Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_EQ_NIL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1116925 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1116926 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1116927 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1116926 n) (@lem1116925 n)). Qed.
Lemma lem1116928 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1116941 {A : Type'} (h : A) : term3 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1116942 {A : Type'} (h : A) : (term3 A h) = (term4 A h).
Proof. exact (eq_refl (term3 A h)). Qed.
Lemma lem1116943 {A : Type'} (h : A) : term4 A h.
Proof. exact (EQ_MP (@lem1116942 A h) (@lem1116941 A h)). Qed.
Lemma lem1116944 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (@lem1116943 A h t). Qed.
Lemma lem1116945 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (eq_refl (term5 A h t)). Qed.
Lemma lem1116946 {A : Type'} (h : A) (t : list A) : term6 A h t.
Proof. exact (EQ_MP (@lem1116945 A h t) (@lem1116944 A h t)). Qed.
Lemma lem1116947 {A : Type'} (h : A) (t : list A) : term7 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1116960 {A : Type'} : term8 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1116961 {A : Type'} (h : A) : term9 A h.
Proof. exact (@lem1116960 A h). Qed.
Lemma lem1116962 {A : Type'} (h : A) : (term9 A h) = (term10 A h).
Proof. exact (eq_refl (term9 A h)). Qed.
Lemma lem1116963 {A : Type'} (h : A) : term10 A h.
Proof. exact (EQ_MP (@lem1116962 A h) (@lem1116961 A h)). Qed.
Lemma lem1116964 {A : Type'} (h : A) (t : list A) : term11 A h t.
Proof. exact (@lem1116963 A h t). Qed.
Lemma lem1116965 {A : Type'} (h : A) (t : list A) : (term11 A h t) = ((term12 A h t) = (term13 A t)).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1116969 {A : Type'} (P : type1143 A) : term14 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1116970 {A : Type'} (P : type1143 A) : term14 A P.
Proof. exact (@lem1116969 A P). Qed.
Lemma lem1116971 {A : Type'} : term15 A.
Proof. exact (@lem1116970 A (term16 A)). Qed.
Lemma lem1116972 {A : Type'} : (term17 A) = (((@List.length A (@nil A)) = (NUMERAL 0)) = ((@nil A) = (@nil A))).
Proof. exact (eq_refl (term17 A)). Qed.
Lemma lem1116973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116974 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem1116973) (@lem1116972 A)). Qed.
Lemma lem1116975 {A : Type'} (t : list A) : (term20 A t) = (((@List.length A t) = (NUMERAL 0)) = (t = (@nil A))).
Proof. exact (eq_refl (term20 A t)). Qed.
Lemma lem1116976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116977 {A : Type'} (t : list A) : (term21 A t) = (term22 A t).
Proof. exact (MK_COMB (@lem1116976) (@lem1116975 A t)). Qed.
Lemma lem1116978 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (((term12 A h t) = (NUMERAL 0)) = ((@cons A h t) = (@nil A))).
Proof. exact (eq_refl (term23 A h t)). Qed.
Lemma lem1116979 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term25 A h t).
Proof. exact (MK_COMB (@lem1116977 A t) (@lem1116978 A h t)). Qed.
Lemma lem1116980 {A : Type'} (h : A) : (term26 A h) = (term27 A h).
Proof. exact (fun_ext (fun t : list A => @lem1116979 A h t)). Qed.
Lemma lem1116981 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116982 {A : Type'} (h : A) : (term28 A h) = (term29 A h).
Proof. exact (MK_COMB (@lem1116981 A) (@lem1116980 A h)). Qed.
Lemma lem1116983 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (fun_ext (fun h : A => @lem1116982 A h)). Qed.
Lemma lem1116984 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1116985 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (MK_COMB (@lem1116984 A) (@lem1116983 A)). Qed.
Lemma lem1116986 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem1116974 A) (@lem1116985 A)). Qed.
Lemma lem1116987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116988 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem1116987) (@lem1116986 A)). Qed.
Lemma lem1116989 {A : Type'} (l : list A) : (term20 A l) = (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))).
Proof. exact (eq_refl (term20 A l)). Qed.
Lemma lem1116990 {A : Type'} : (term38 A) = (term16 A).
Proof. exact (fun_ext (fun l : list A => @lem1116989 A l)). Qed.
Lemma lem1116991 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116992 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (MK_COMB (@lem1116991 A) (@lem1116990 A)). Qed.
Lemma lem1116993 {A : Type'} : (term15 A) = (term41 A).
Proof. exact (MK_COMB (@lem1116988 A) (@lem1116992 A)). Qed.
Lemma lem1116994 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem1116993 A) (@lem1116971 A)). Qed.
Lemma lem1117001 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1117002 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1117003 {A : Type'} : (term42 A) = term43.
Proof. exact (MK_COMB (@lem1117002) (@lem1117001 A)). Qed.
Lemma lem1117004 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1117005 {A : Type'} : ((@List.length A (@nil A)) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1117003 A) (@lem1117004)). Qed.
Lemma lem1117007 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1117008 (x : nat) : (x = x) = True.
Proof. exact (@lem1117007 nat x). Qed.
Lemma lem1117009 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1117008 (NUMERAL 0)). Qed.
Lemma lem1117010 {A : Type'} : ((@List.length A (@nil A)) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1117005 A) (@lem1117009)). Qed.
Lemma lem1117011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117012 {A : Type'} : (term44 A) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1117011) (@lem1117010 A)). Qed.
Lemma lem1117014 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1117015 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1117014 (list A) x). Qed.
Lemma lem1117016 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1117015 A (@nil A)). Qed.
Lemma lem1117017 {A : Type'} : (((@List.length A (@nil A)) = (NUMERAL 0)) = ((@nil A) = (@nil A))) = (True = True).
Proof. exact (MK_COMB (@lem1117012 A) (@lem1117016 A)). Qed.
Lemma lem1117019 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1117020 : (True = True) = True.
Proof. exact (@lem1117019 True). Qed.
Lemma lem1117021 {A : Type'} : (((@List.length A (@nil A)) = (NUMERAL 0)) = ((@nil A) = (@nil A))) = True.
Proof. exact (TRANS (@lem1117017 A) (@lem1117020)). Qed.
Lemma lem1117022 {A : Type'} : True = (((@List.length A (@nil A)) = (NUMERAL 0)) = ((@nil A) = (@nil A))).
Proof. exact (SYM (@lem1117021 A)). Qed.
Lemma lem1117023 {A : Type'} : ((@List.length A (@nil A)) = (NUMERAL 0)) = ((@nil A) = (@nil A)).
Proof. exact (EQ_MP (@lem1117022 A) (@lem0)). Qed.
Lemma lem1117029 {A : Type'} (h : A) (t : list A) : (term12 A h t) = (term13 A t).
Proof. exact (EQ_MP (@lem1116965 A h t) (@lem1116964 A h t)). Qed.
Lemma lem1117030 {A : Type'} (h : A) (t : list A) : (term12 A h t) = (term13 A t).
Proof. exact (@lem1117029 A h t). Qed.
Lemma lem1117031 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1117032 {A : Type'} (h : A) (t : list A) : (term45 A h t) = (term46 A t).
Proof. exact (MK_COMB (@lem1117031) (@lem1117030 A h t)). Qed.
Lemma lem1117033 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1117034 {A : Type'} (h : A) (t : list A) : ((term12 A h t) = (NUMERAL 0)) = ((term13 A t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1117032 A h t) (@lem1117033)). Qed.
Lemma lem1117036 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1116928 n (@lem1116927 n)). Qed.
Lemma lem1117037 {A : Type'} (t : list A) : ((term13 A t) = (NUMERAL 0)) = False.
Proof. exact (@lem1117036 (@List.length A t)). Qed.
Lemma lem1117038 {A : Type'} (h : A) (t : list A) : ((term12 A h t) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1117034 A h t) (@lem1117037 A t)). Qed.
Lemma lem1117039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117040 {A : Type'} (h : A) (t : list A) : (term47 A h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1117039) (@lem1117038 A h t)). Qed.
Lemma lem1117042 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1116947 A h t (@lem1116946 A h t)). Qed.
Lemma lem1117043 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1117042 A h t). Qed.
Lemma lem1117044 {A : Type'} (h : A) (t : list A) : (((term12 A h t) = (NUMERAL 0)) = ((@cons A h t) = (@nil A))) = (False = False).
Proof. exact (MK_COMB (@lem1117040 A h t) (@lem1117043 A h t)). Qed.
Lemma lem1117046 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1117047 : (False = False) = (~ False).
Proof. exact (@lem1117046 False). Qed.
Lemma lem1117049 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1117050 : (False = False) = True.
Proof. exact (TRANS (@lem1117047) (@lem1117049)). Qed.
Lemma lem1117051 {A : Type'} (h : A) (t : list A) : (((term12 A h t) = (NUMERAL 0)) = ((@cons A h t) = (@nil A))) = True.
Proof. exact (TRANS (@lem1117044 A h t) (@lem1117050)). Qed.
Lemma lem1117052 {A : Type'} (h : A) (t : list A) : True = (((term12 A h t) = (NUMERAL 0)) = ((@cons A h t) = (@nil A))).
Proof. exact (SYM (@lem1117051 A h t)). Qed.
Lemma lem1117053 {A : Type'} (h : A) (t : list A) : ((term12 A h t) = (NUMERAL 0)) = ((@cons A h t) = (@nil A)).
Proof. exact (EQ_MP (@lem1117052 A h t) (@lem0)). Qed.
Lemma lem1117054 {A : Type'} (h : A) (t : list A) : term25 A h t.
Proof. exact (fun h0 : ((@List.length A t) = (NUMERAL 0)) = (t = (@nil A)) => @lem1117053 A h t). Qed.
Lemma lem1117059 {A : Type'} (h : A) : term29 A h.
Proof. exact (fun t : list A => @lem1117054 A h t). Qed.
Lemma lem1117064 {A : Type'} : term33 A.
Proof. exact (fun h : A => @lem1117059 A h). Qed.
Lemma lem1117065 {A : Type'} : term35 A.
Proof. exact (conj (@lem1117023 A) (@lem1117064 A)). Qed.
Lemma lem1117066 {A : Type'} : term40 A.
Proof. exact (@lem1116994 A (@lem1117065 A)). Qed.
