Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_ID_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1199953 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1199954 {_27941 : Type'} (P : type1143 _27941) : term0 _27941 P.
Proof. exact (@lem1199953 _27941 P). Qed.
Lemma lem1199955 {_27941 : Type'} : term1 _27941.
Proof. exact (@lem1199954 _27941 (term2 _27941)). Qed.
Lemma lem1199956 {_27941 : Type'} : (term3 _27941) = ((term4 _27941) = (@nil _27941)).
Proof. exact (eq_refl (term3 _27941)). Qed.
Lemma lem1199957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1199958 {_27941 : Type'} : (term5 _27941) = (term6 _27941).
Proof. exact (MK_COMB (@lem1199957) (@lem1199956 _27941)). Qed.
Lemma lem1199959 {_27941 : Type'} (t : list _27941) : (term7 _27941 t) = ((term8 _27941 t) = t).
Proof. exact (eq_refl (term7 _27941 t)). Qed.
Lemma lem1199960 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1199961 {_27941 : Type'} (t : list _27941) : (term9 _27941 t) = (term10 _27941 t).
Proof. exact (MK_COMB (@lem1199960) (@lem1199959 _27941 t)). Qed.
Lemma lem1199962 {_27941 : Type'} (h : _27941) (t : list _27941) : (term11 _27941 h t) = ((term12 _27941 h t) = (@cons _27941 h t)).
Proof. exact (eq_refl (term11 _27941 h t)). Qed.
Lemma lem1199963 {_27941 : Type'} (h : _27941) (t : list _27941) : (term13 _27941 h t) = (term14 _27941 h t).
Proof. exact (MK_COMB (@lem1199961 _27941 t) (@lem1199962 _27941 h t)). Qed.
Lemma lem1199964 {_27941 : Type'} (h : _27941) : (term15 _27941 h) = (term16 _27941 h).
Proof. exact (fun_ext (fun t : list _27941 => @lem1199963 _27941 h t)). Qed.
Lemma lem1199965 {_27941 : Type'} : (@all (list _27941)) = (@all (list _27941)).
Proof. exact (eq_refl (@all (list _27941))). Qed.
Lemma lem1199966 {_27941 : Type'} (h : _27941) : (term17 _27941 h) = (term18 _27941 h).
Proof. exact (MK_COMB (@lem1199965 _27941) (@lem1199964 _27941 h)). Qed.
Lemma lem1199967 {_27941 : Type'} : (term19 _27941) = (term20 _27941).
Proof. exact (fun_ext (fun h : _27941 => @lem1199966 _27941 h)). Qed.
Lemma lem1199968 {_27941 : Type'} : (@all _27941) = (@all _27941).
Proof. exact (eq_refl (@all _27941)). Qed.
Lemma lem1199969 {_27941 : Type'} : (term21 _27941) = (term22 _27941).
Proof. exact (MK_COMB (@lem1199968 _27941) (@lem1199967 _27941)). Qed.
Lemma lem1199970 {_27941 : Type'} : (term23 _27941) = (term24 _27941).
Proof. exact (MK_COMB (@lem1199958 _27941) (@lem1199969 _27941)). Qed.
Lemma lem1199971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1199972 {_27941 : Type'} : (term25 _27941) = (term26 _27941).
Proof. exact (MK_COMB (@lem1199971) (@lem1199970 _27941)). Qed.
Lemma lem1199973 {_27941 : Type'} (l : list _27941) : (term7 _27941 l) = ((term8 _27941 l) = l).
Proof. exact (eq_refl (term7 _27941 l)). Qed.
Lemma lem1199974 {_27941 : Type'} : (term27 _27941) = (term2 _27941).
Proof. exact (fun_ext (fun l : list _27941 => @lem1199973 _27941 l)). Qed.
Lemma lem1199975 {_27941 : Type'} : (@all (list _27941)) = (@all (list _27941)).
Proof. exact (eq_refl (@all (list _27941))). Qed.
Lemma lem1199976 {_27941 : Type'} : (term28 _27941) = (term29 _27941).
Proof. exact (MK_COMB (@lem1199975 _27941) (@lem1199974 _27941)). Qed.
Lemma lem1199977 {_27941 : Type'} : (term1 _27941) = (term30 _27941).
Proof. exact (MK_COMB (@lem1199972 _27941) (@lem1199976 _27941)). Qed.
Lemma lem1199978 {_27941 : Type'} : term30 _27941.
Proof. exact (EQ_MP (@lem1199977 _27941) (@lem1199955 _27941)). Qed.
Lemma lem1199990 {A B : Type'} : term31 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1199991 {A B : Type'} (f : A -> B) : term32 A B f.
Proof. exact (@lem1199990 A B f). Qed.
Lemma lem1199992 {A B : Type'} (f : A -> B) : (term32 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term32 A B f)). Qed.
Lemma lem1199997 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1199992 A B f) (@lem1199991 A B f)). Qed.
Lemma lem1199998 {_27941 : Type'} (f : _27941 -> _27941) : (@List.map _27941 _27941 f (@nil _27941)) = (@nil _27941).
Proof. exact (@lem1199997 _27941 _27941 f). Qed.
Lemma lem1199999 {_27941 : Type'} : (term4 _27941) = (@nil _27941).
Proof. exact (@lem1199998 _27941 (term33 _27941)). Qed.
Lemma lem1200000 {_27941 : Type'} : (@eq (list _27941)) = (@eq (list _27941)).
Proof. exact (eq_refl (@eq (list _27941))). Qed.
Lemma lem1200001 {_27941 : Type'} : (term34 _27941) = (@eq (list _27941) (@nil _27941)).
Proof. exact (MK_COMB (@lem1200000 _27941) (@lem1199999 _27941)). Qed.
Lemma lem1200002 {_27941 : Type'} : (@nil _27941) = (@nil _27941).
Proof. exact (eq_refl (@nil _27941)). Qed.
Lemma lem1200003 {_27941 : Type'} : ((term4 _27941) = (@nil _27941)) = ((@nil _27941) = (@nil _27941)).
Proof. exact (MK_COMB (@lem1200001 _27941) (@lem1200002 _27941)). Qed.
Lemma lem1200005 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200006 {_27941 : Type'} (x : list _27941) : (x = x) = True.
Proof. exact (@lem1200005 (list _27941) x). Qed.
Lemma lem1200007 {_27941 : Type'} : ((@nil _27941) = (@nil _27941)) = True.
Proof. exact (@lem1200006 _27941 (@nil _27941)). Qed.
Lemma lem1200008 {_27941 : Type'} : ((term4 _27941) = (@nil _27941)) = True.
Proof. exact (TRANS (@lem1200003 _27941) (@lem1200007 _27941)). Qed.
Lemma lem1200009 {_27941 : Type'} : True = ((term4 _27941) = (@nil _27941)).
Proof. exact (SYM (@lem1200008 _27941)). Qed.
Lemma lem1200010 {_27941 : Type'} : (term4 _27941) = (@nil _27941).
Proof. exact (EQ_MP (@lem1200009 _27941) (@lem0)). Qed.
Lemma lem1200011 {A B : Type'} : term35 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1200012 {A B : Type'} (f : A -> B) : term36 A B f.
Proof. exact (@lem1200011 A B f). Qed.
Lemma lem1200013 {A B : Type'} (f : A -> B) : (term36 A B f) = (term37 A B f).
Proof. exact (eq_refl (term36 A B f)). Qed.
Lemma lem1200014 {A B : Type'} (f : A -> B) : term37 A B f.
Proof. exact (EQ_MP (@lem1200013 A B f) (@lem1200012 A B f)). Qed.
Lemma lem1200015 {A B : Type'} (f : A -> B) (h : A) : term38 A B f h.
Proof. exact (@lem1200014 A B f h). Qed.
Lemma lem1200016 {A B : Type'} (h : A) (f : A -> B) : (term38 A B f h) = (term39 A B h f).
Proof. exact (eq_refl (term38 A B f h)). Qed.
Lemma lem1200017 {A B : Type'} (h : A) (f : A -> B) : term39 A B h f.
Proof. exact (EQ_MP (@lem1200016 A B h f) (@lem1200015 A B f h)). Qed.
Lemma lem1200018 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term40 A B h f t.
Proof. exact (@lem1200017 A B h f t). Qed.
Lemma lem1200019 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term40 A B h f t) = ((term41 A B f h t) = (term42 A B h f t)).
Proof. exact (eq_refl (term40 A B h f t)). Qed.
Lemma lem1200028 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term41 A B f h t) = (term42 A B h f t).
Proof. exact (EQ_MP (@lem1200019 A B h f t) (@lem1200018 A B h f t)). Qed.
Lemma lem1200029 {_27941 : Type'} (h : _27941) (f : _27941 -> _27941) (t : list _27941) : (term43 _27941 f h t) = (term44 _27941 h f t).
Proof. exact (@lem1200028 _27941 _27941 h f t). Qed.
Lemma lem1200030 {_27941 : Type'} (h : _27941) (t : list _27941) : (term12 _27941 h t) = (term45 _27941 h t).
Proof. exact (@lem1200029 _27941 h (term33 _27941) t). Qed.
Lemma lem1200032 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1200033 {_27941 : Type'} (f : _27941 -> _27941) (y : _27941) : (term47 _27941 f y) = (f y).
Proof. exact (@lem1200032 _27941 _27941 f y). Qed.
Lemma lem1200034 {_27941 : Type'} (h : _27941) : (term48 _27941 h) = (term49 _27941 h).
Proof. exact (@lem1200033 _27941 (term33 _27941) h). Qed.
Lemma lem1200035 {_27941 : Type'} (x : _27941) : (term49 _27941 x) = x.
Proof. exact (eq_refl (term49 _27941 x)). Qed.
Lemma lem1200036 {_27941 : Type'} : (term50 _27941) = (term33 _27941).
Proof. exact (fun_ext (fun x : _27941 => @lem1200035 _27941 x)). Qed.
Lemma lem1200037 {_27941 : Type'} (h : _27941) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1200038 {_27941 : Type'} (h : _27941) : (term48 _27941 h) = (term49 _27941 h).
Proof. exact (MK_COMB (@lem1200036 _27941) (@lem1200037 _27941 h)). Qed.
Lemma lem1200039 {_27941 : Type'} : (@eq _27941) = (@eq _27941).
Proof. exact (eq_refl (@eq _27941)). Qed.
Lemma lem1200040 {_27941 : Type'} (h : _27941) : (term51 _27941 h) = (term52 _27941 h).
Proof. exact (MK_COMB (@lem1200039 _27941) (@lem1200038 _27941 h)). Qed.
Lemma lem1200041 {_27941 : Type'} (h : _27941) : (term49 _27941 h) = h.
Proof. exact (eq_refl (term49 _27941 h)). Qed.
Lemma lem1200042 {_27941 : Type'} (h : _27941) : ((term48 _27941 h) = (term49 _27941 h)) = ((term49 _27941 h) = h).
Proof. exact (MK_COMB (@lem1200040 _27941 h) (@lem1200041 _27941 h)). Qed.
Lemma lem1200043 {_27941 : Type'} (h : _27941) : (term49 _27941 h) = h.
Proof. exact (EQ_MP (@lem1200042 _27941 h) (@lem1200034 _27941 h)). Qed.
Lemma lem1200044 {_27941 : Type'} : (@cons _27941) = (@cons _27941).
Proof. exact (eq_refl (@cons _27941)). Qed.
Lemma lem1200045 {_27941 : Type'} (h : _27941) : (term53 _27941 h) = (@cons _27941 h).
Proof. exact (MK_COMB (@lem1200044 _27941) (@lem1200043 _27941 h)). Qed.
Lemma lem1200047 {_27941 : Type'} (t : list _27941) (h1 : (term8 _27941 t) = t) : (term8 _27941 t) = t.
Proof. exact (h1). Qed.
Lemma lem1200048 {_27941 : Type'} (t : list _27941) (h1 : (term8 _27941 t) = t) : (term8 _27941 t) = t.
Proof. exact (@lem1200047 _27941 t h1). Qed.
Lemma lem1200049 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : (term45 _27941 h t) = (@cons _27941 h t).
Proof. exact (MK_COMB (@lem1200045 _27941 h) (@lem1200048 _27941 t h1)). Qed.
Lemma lem1200050 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : (term12 _27941 h t) = (@cons _27941 h t).
Proof. exact (TRANS (@lem1200030 _27941 h t) (@lem1200049 _27941 h t h1)). Qed.
Lemma lem1200051 {_27941 : Type'} : (@eq (list _27941)) = (@eq (list _27941)).
Proof. exact (eq_refl (@eq (list _27941))). Qed.
Lemma lem1200052 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : (term54 _27941 h t) = (term55 _27941 h t).
Proof. exact (MK_COMB (@lem1200051 _27941) (@lem1200050 _27941 h t h1)). Qed.
Lemma lem1200053 {_27941 : Type'} (h : _27941) (t : list _27941) : (@cons _27941 h t) = (@cons _27941 h t).
Proof. exact (eq_refl (@cons _27941 h t)). Qed.
Lemma lem1200054 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : ((term12 _27941 h t) = (@cons _27941 h t)) = ((@cons _27941 h t) = (@cons _27941 h t)).
Proof. exact (MK_COMB (@lem1200052 _27941 h t h1) (@lem1200053 _27941 h t)). Qed.
Lemma lem1200056 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200057 {_27941 : Type'} (x : list _27941) : (x = x) = True.
Proof. exact (@lem1200056 (list _27941) x). Qed.
Lemma lem1200058 {_27941 : Type'} (h : _27941) (t : list _27941) : ((@cons _27941 h t) = (@cons _27941 h t)) = True.
Proof. exact (@lem1200057 _27941 (@cons _27941 h t)). Qed.
Lemma lem1200059 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : ((term12 _27941 h t) = (@cons _27941 h t)) = True.
Proof. exact (TRANS (@lem1200054 _27941 h t h1) (@lem1200058 _27941 h t)). Qed.
Lemma lem1200060 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : True = ((term12 _27941 h t) = (@cons _27941 h t)).
Proof. exact (SYM (@lem1200059 _27941 h t h1)). Qed.
Lemma lem1200061 {_27941 : Type'} (h : _27941) (t : list _27941) (h1 : (term8 _27941 t) = t) : (term12 _27941 h t) = (@cons _27941 h t).
Proof. exact (EQ_MP (@lem1200060 _27941 h t h1) (@lem0)). Qed.
Lemma lem1200062 {_27941 : Type'} (h : _27941) (t : list _27941) : term14 _27941 h t.
Proof. exact (fun h0 : (term8 _27941 t) = t => @lem1200061 _27941 h t h0). Qed.
Lemma lem1200067 {_27941 : Type'} (h : _27941) : term18 _27941 h.
Proof. exact (fun t : list _27941 => @lem1200062 _27941 h t). Qed.
Lemma lem1200072 {_27941 : Type'} : term22 _27941.
Proof. exact (fun h : _27941 => @lem1200067 _27941 h). Qed.
Lemma lem1200073 {_27941 : Type'} : term24 _27941.
Proof. exact (conj (@lem1200010 _27941) (@lem1200072 _27941)). Qed.
Lemma lem1200074 {_27941 : Type'} : term29 _27941.
Proof. exact (@lem1199978 _27941 (@lem1200073 _27941)). Qed.
