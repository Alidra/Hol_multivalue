Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_EQ_NIL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1189924 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1189925 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1189926 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1189925 A h) (@lem1189924 A h)). Qed.
Lemma lem1189927 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1189926 A h t). Qed.
Lemma lem1189928 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1189929 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1189928 A h t) (@lem1189927 A h t)). Qed.
Lemma lem1189930 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1189943 {A B : Type'} : term5 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1189944 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem1189943 A B f). Qed.
Lemma lem1189945 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem1189946 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem1189945 A B f) (@lem1189944 A B f)). Qed.
Lemma lem1189947 {A B : Type'} (f : A -> B) (h : A) : term8 A B f h.
Proof. exact (@lem1189946 A B f h). Qed.
Lemma lem1189948 {A B : Type'} (h : A) (f : A -> B) : (term8 A B f h) = (term9 A B h f).
Proof. exact (eq_refl (term8 A B f h)). Qed.
Lemma lem1189949 {A B : Type'} (h : A) (f : A -> B) : term9 A B h f.
Proof. exact (EQ_MP (@lem1189948 A B h f) (@lem1189947 A B f h)). Qed.
Lemma lem1189950 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term10 A B h f t.
Proof. exact (@lem1189949 A B h f t). Qed.
Lemma lem1189951 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term10 A B h f t) = ((term11 A B f h t) = (term12 A B h f t)).
Proof. exact (eq_refl (term10 A B h f t)). Qed.
Lemma lem1189953 {A B : Type'} : term13 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1189954 {A B : Type'} (f : A -> B) : term14 A B f.
Proof. exact (@lem1189953 A B f). Qed.
Lemma lem1189955 {A B : Type'} (f : A -> B) : (term14 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term14 A B f)). Qed.
Lemma lem1189958 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1189959 {_27827 : Type'} (P : type1143 _27827) : term15 _27827 P.
Proof. exact (@lem1189958 _27827 P). Qed.
Lemma lem1189960 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term16 _27823 _27827 f.
Proof. exact (@lem1189959 _27827 (term17 _27823 _27827 f)). Qed.
Lemma lem1189961 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term18 _27823 _27827 f) = (((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27827) = (@nil _27827))).
Proof. exact (eq_refl (term18 _27823 _27827 f)). Qed.
Lemma lem1189962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189963 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term19 _27823 _27827 f) = (term20 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189962) (@lem1189961 _27823 _27827 f)). Qed.
Lemma lem1189964 {_27823 _27827 : Type'} (f : _27827 -> _27823) (t : list _27827) : (term21 _27823 _27827 f t) = (((@List.map _27827 _27823 f t) = (@nil _27823)) = (t = (@nil _27827))).
Proof. exact (eq_refl (term21 _27823 _27827 f t)). Qed.
Lemma lem1189965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189966 {_27823 _27827 : Type'} (f : _27827 -> _27823) (t : list _27827) : (term22 _27823 _27827 f t) = (term23 _27823 _27827 f t).
Proof. exact (MK_COMB (@lem1189965) (@lem1189964 _27823 _27827 f t)). Qed.
Lemma lem1189967 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : (term24 _27823 _27827 f h t) = (((term25 _27823 _27827 f h t) = (@nil _27823)) = ((@cons _27827 h t) = (@nil _27827))).
Proof. exact (eq_refl (term24 _27823 _27827 f h t)). Qed.
Lemma lem1189968 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : (term26 _27823 _27827 f h t) = (term27 _27823 _27827 f h t).
Proof. exact (MK_COMB (@lem1189966 _27823 _27827 f t) (@lem1189967 _27823 _27827 f h t)). Qed.
Lemma lem1189969 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) : (term28 _27823 _27827 f h) = (term29 _27823 _27827 f h).
Proof. exact (fun_ext (fun t : list _27827 => @lem1189968 _27823 _27827 f h t)). Qed.
Lemma lem1189970 {_27827 : Type'} : (@all (list _27827)) = (@all (list _27827)).
Proof. exact (eq_refl (@all (list _27827))). Qed.
Lemma lem1189971 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) : (term30 _27823 _27827 f h) = (term31 _27823 _27827 f h).
Proof. exact (MK_COMB (@lem1189970 _27827) (@lem1189969 _27823 _27827 f h)). Qed.
Lemma lem1189972 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term32 _27823 _27827 f) = (term33 _27823 _27827 f).
Proof. exact (fun_ext (fun h : _27827 => @lem1189971 _27823 _27827 f h)). Qed.
Lemma lem1189973 {_27827 : Type'} : (@all _27827) = (@all _27827).
Proof. exact (eq_refl (@all _27827)). Qed.
Lemma lem1189974 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term34 _27823 _27827 f) = (term35 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189973 _27827) (@lem1189972 _27823 _27827 f)). Qed.
Lemma lem1189975 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term36 _27823 _27827 f) = (term37 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189963 _27823 _27827 f) (@lem1189974 _27823 _27827 f)). Qed.
Lemma lem1189976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189977 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term38 _27823 _27827 f) = (term39 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189976) (@lem1189975 _27823 _27827 f)). Qed.
Lemma lem1189978 {_27823 _27827 : Type'} (f : _27827 -> _27823) (l : list _27827) : (term21 _27823 _27827 f l) = (((@List.map _27827 _27823 f l) = (@nil _27823)) = (l = (@nil _27827))).
Proof. exact (eq_refl (term21 _27823 _27827 f l)). Qed.
Lemma lem1189979 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term40 _27823 _27827 f) = (term17 _27823 _27827 f).
Proof. exact (fun_ext (fun l : list _27827 => @lem1189978 _27823 _27827 f l)). Qed.
Lemma lem1189980 {_27827 : Type'} : (@all (list _27827)) = (@all (list _27827)).
Proof. exact (eq_refl (@all (list _27827))). Qed.
Lemma lem1189981 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term41 _27823 _27827 f) = (term42 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189980 _27827) (@lem1189979 _27823 _27827 f)). Qed.
Lemma lem1189982 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term16 _27823 _27827 f) = (term43 _27823 _27827 f).
Proof. exact (MK_COMB (@lem1189977 _27823 _27827 f) (@lem1189981 _27823 _27827 f)). Qed.
Lemma lem1189983 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term43 _27823 _27827 f.
Proof. exact (EQ_MP (@lem1189982 _27823 _27827 f) (@lem1189960 _27823 _27827 f)). Qed.
Lemma lem1189990 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1189955 A B f) (@lem1189954 A B f)). Qed.
Lemma lem1189991 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823).
Proof. exact (@lem1189990 _27827 _27823 f). Qed.
Lemma lem1189992 {_27823 : Type'} : (@eq (list _27823)) = (@eq (list _27823)).
Proof. exact (eq_refl (@eq (list _27823))). Qed.
Lemma lem1189993 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term44 _27823 _27827 f) = (@eq (list _27823) (@nil _27823)).
Proof. exact (MK_COMB (@lem1189992 _27823) (@lem1189991 _27823 _27827 f)). Qed.
Lemma lem1189994 {_27823 : Type'} : (@nil _27823) = (@nil _27823).
Proof. exact (eq_refl (@nil _27823)). Qed.
Lemma lem1189995 {_27823 _27827 : Type'} (f : _27827 -> _27823) : ((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27823) = (@nil _27823)).
Proof. exact (MK_COMB (@lem1189993 _27823 _27827 f) (@lem1189994 _27823)). Qed.
Lemma lem1189997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1189998 {_27823 : Type'} (x : list _27823) : (x = x) = True.
Proof. exact (@lem1189997 (list _27823) x). Qed.
Lemma lem1189999 {_27823 : Type'} : ((@nil _27823) = (@nil _27823)) = True.
Proof. exact (@lem1189998 _27823 (@nil _27823)). Qed.
Lemma lem1190000 {_27823 _27827 : Type'} (f : _27827 -> _27823) : ((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = True.
Proof. exact (TRANS (@lem1189995 _27823 _27827 f) (@lem1189999 _27823)). Qed.
Lemma lem1190001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1190002 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term45 _27823 _27827 f) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1190001) (@lem1190000 _27823 _27827 f)). Qed.
Lemma lem1190004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1190005 {_27827 : Type'} (x : list _27827) : (x = x) = True.
Proof. exact (@lem1190004 (list _27827) x). Qed.
Lemma lem1190006 {_27827 : Type'} : ((@nil _27827) = (@nil _27827)) = True.
Proof. exact (@lem1190005 _27827 (@nil _27827)). Qed.
Lemma lem1190007 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27827) = (@nil _27827))) = (True = True).
Proof. exact (MK_COMB (@lem1190002 _27823 _27827 f) (@lem1190006 _27827)). Qed.
Lemma lem1190009 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1190010 : (True = True) = True.
Proof. exact (@lem1190009 True). Qed.
Lemma lem1190011 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27827) = (@nil _27827))) = True.
Proof. exact (TRANS (@lem1190007 _27823 _27827 f) (@lem1190010)). Qed.
Lemma lem1190012 {_27823 _27827 : Type'} (f : _27827 -> _27823) : True = (((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27827) = (@nil _27827))).
Proof. exact (SYM (@lem1190011 _27823 _27827 f)). Qed.
Lemma lem1190013 {_27823 _27827 : Type'} (f : _27827 -> _27823) : ((@List.map _27827 _27823 f (@nil _27827)) = (@nil _27823)) = ((@nil _27827) = (@nil _27827)).
Proof. exact (EQ_MP (@lem1190012 _27823 _27827 f) (@lem0)). Qed.
Lemma lem1190019 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term11 A B f h t) = (term12 A B h f t).
Proof. exact (EQ_MP (@lem1189951 A B h f t) (@lem1189950 A B h f t)). Qed.
Lemma lem1190020 {_27823 _27827 : Type'} (h : _27827) (f : _27827 -> _27823) (t : list _27827) : (term25 _27823 _27827 f h t) = (term46 _27823 _27827 h f t).
Proof. exact (@lem1190019 _27827 _27823 h f t). Qed.
Lemma lem1190021 {_27823 : Type'} : (@eq (list _27823)) = (@eq (list _27823)).
Proof. exact (eq_refl (@eq (list _27823))). Qed.
Lemma lem1190022 {_27823 _27827 : Type'} (h : _27827) (f : _27827 -> _27823) (t : list _27827) : (term47 _27823 _27827 f h t) = (term48 _27823 _27827 h f t).
Proof. exact (MK_COMB (@lem1190021 _27823) (@lem1190020 _27823 _27827 h f t)). Qed.
Lemma lem1190023 {_27823 : Type'} : (@nil _27823) = (@nil _27823).
Proof. exact (eq_refl (@nil _27823)). Qed.
Lemma lem1190024 {_27823 _27827 : Type'} (h : _27827) (f : _27827 -> _27823) (t : list _27827) : ((term25 _27823 _27827 f h t) = (@nil _27823)) = ((term46 _27823 _27827 h f t) = (@nil _27823)).
Proof. exact (MK_COMB (@lem1190022 _27823 _27827 h f t) (@lem1190023 _27823)). Qed.
Lemma lem1190026 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1189930 A h t (@lem1189929 A h t)). Qed.
Lemma lem1190027 {_27823 : Type'} (h : _27823) (t : list _27823) : ((@cons _27823 h t) = (@nil _27823)) = False.
Proof. exact (@lem1190026 _27823 h t). Qed.
Lemma lem1190028 {_27823 _27827 : Type'} (h : _27827) (f : _27827 -> _27823) (t : list _27827) : ((term46 _27823 _27827 h f t) = (@nil _27823)) = False.
Proof. exact (@lem1190027 _27823 (f h) (@List.map _27827 _27823 f t)). Qed.
Lemma lem1190029 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : ((term25 _27823 _27827 f h t) = (@nil _27823)) = False.
Proof. exact (TRANS (@lem1190024 _27823 _27827 h f t) (@lem1190028 _27823 _27827 h f t)). Qed.
Lemma lem1190030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1190031 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : (term49 _27823 _27827 f h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1190030) (@lem1190029 _27823 _27827 f h t)). Qed.
Lemma lem1190033 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1189930 A h t (@lem1189929 A h t)). Qed.
Lemma lem1190034 {_27827 : Type'} (h : _27827) (t : list _27827) : ((@cons _27827 h t) = (@nil _27827)) = False.
Proof. exact (@lem1190033 _27827 h t). Qed.
Lemma lem1190035 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : (((term25 _27823 _27827 f h t) = (@nil _27823)) = ((@cons _27827 h t) = (@nil _27827))) = (False = False).
Proof. exact (MK_COMB (@lem1190031 _27823 _27827 f h t) (@lem1190034 _27827 h t)). Qed.
Lemma lem1190037 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1190038 : (False = False) = (~ False).
Proof. exact (@lem1190037 False). Qed.
Lemma lem1190040 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1190041 : (False = False) = True.
Proof. exact (TRANS (@lem1190038) (@lem1190040)). Qed.
Lemma lem1190042 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : (((term25 _27823 _27827 f h t) = (@nil _27823)) = ((@cons _27827 h t) = (@nil _27827))) = True.
Proof. exact (TRANS (@lem1190035 _27823 _27827 f h t) (@lem1190041)). Qed.
Lemma lem1190043 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : True = (((term25 _27823 _27827 f h t) = (@nil _27823)) = ((@cons _27827 h t) = (@nil _27827))).
Proof. exact (SYM (@lem1190042 _27823 _27827 f h t)). Qed.
Lemma lem1190044 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : ((term25 _27823 _27827 f h t) = (@nil _27823)) = ((@cons _27827 h t) = (@nil _27827)).
Proof. exact (EQ_MP (@lem1190043 _27823 _27827 f h t) (@lem0)). Qed.
Lemma lem1190045 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) (t : list _27827) : term27 _27823 _27827 f h t.
Proof. exact (fun h0 : ((@List.map _27827 _27823 f t) = (@nil _27823)) = (t = (@nil _27827)) => @lem1190044 _27823 _27827 f h t). Qed.
Lemma lem1190050 {_27823 _27827 : Type'} (f : _27827 -> _27823) (h : _27827) : term31 _27823 _27827 f h.
Proof. exact (fun t : list _27827 => @lem1190045 _27823 _27827 f h t). Qed.
Lemma lem1190055 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term35 _27823 _27827 f.
Proof. exact (fun h : _27827 => @lem1190050 _27823 _27827 f h). Qed.
Lemma lem1190056 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term37 _27823 _27827 f.
Proof. exact (conj (@lem1190013 _27823 _27827 f) (@lem1190055 _27823 _27827 f)). Qed.
Lemma lem1190057 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term42 _27823 _27827 f.
Proof. exact (@lem1189983 _27823 _27827 f (@lem1190056 _27823 _27827 f)). Qed.
Lemma lem1190062 {_27823 _27827 : Type'} : term50 _27823 _27827.
Proof. exact (fun f : _27827 -> _27823 => @lem1190057 _27823 _27827 f). Qed.
