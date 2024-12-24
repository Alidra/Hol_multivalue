Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_SING_term_abbrevs.
Require Import thm0_spec.
Require Import thm1095962_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1207938 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1207939 {A : Type'} (h : A) : term1 A h.
Proof. exact (@lem1207938 A h). Qed.
Lemma lem1207940 {A : Type'} (h : A) : (term1 A h) = (term2 A h).
Proof. exact (eq_refl (term1 A h)). Qed.
Lemma lem1207941 {A : Type'} (h : A) : term2 A h.
Proof. exact (EQ_MP (@lem1207940 A h) (@lem1207939 A h)). Qed.
Lemma lem1207942 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (@lem1207941 A h t). Qed.
Lemma lem1207943 {A : Type'} (h : A) (t : list A) : (term3 A h t) = (term4 A h t).
Proof. exact (eq_refl (term3 A h t)). Qed.
Lemma lem1207944 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (EQ_MP (@lem1207943 A h t) (@lem1207942 A h t)). Qed.
Lemma lem1207945 {A : Type'} (h : A) (t : list A) (l : list A) : term5 A h t l.
Proof. exact (@lem1207944 A h t l). Qed.
Lemma lem1207946 {A : Type'} (h : A) (t : list A) (l : list A) : (term5 A h t l) = ((term6 A h t l) = (term7 A h t l)).
Proof. exact (eq_refl (term5 A h t l)). Qed.
Lemma lem1207948 {A : Type'} : term8 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1207949 {A : Type'} (l : list A) : term9 A l.
Proof. exact (@lem1207948 A l). Qed.
Lemma lem1207950 {A : Type'} (l : list A) : (term9 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term9 A l)). Qed.
Lemma lem1207963 {A : Type'} (h : A) (t : list A) (l : list A) : (term6 A h t l) = (term7 A h t l).
Proof. exact (EQ_MP (@lem1207946 A h t l) (@lem1207945 A h t l)). Qed.
Lemma lem1207964 {_28445 : Type'} (h : _28445) (t : list _28445) (l : list _28445) : (term6 _28445 h t l) = (term7 _28445 h t l).
Proof. exact (@lem1207963 _28445 h t l). Qed.
Lemma lem1207965 {_28445 : Type'} (h : _28445) (t : list _28445) : (term10 _28445 h t) = (term11 _28445 h t).
Proof. exact (@lem1207964 _28445 h (@nil _28445) t). Qed.
Lemma lem1207967 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1207950 A l) (@lem1207949 A l)). Qed.
Lemma lem1207968 {_28445 : Type'} (l : list _28445) : (@List.app _28445 (@nil _28445) l) = l.
Proof. exact (@lem1207967 _28445 l). Qed.
Lemma lem1207969 {_28445 : Type'} (t : list _28445) : (@List.app _28445 (@nil _28445) t) = t.
Proof. exact (@lem1207968 _28445 t). Qed.
Lemma lem1207970 {_28445 : Type'} (h : _28445) : (@cons _28445 h) = (@cons _28445 h).
Proof. exact (eq_refl (@cons _28445 h)). Qed.
Lemma lem1207971 {_28445 : Type'} (h : _28445) (t : list _28445) : (term11 _28445 h t) = (@cons _28445 h t).
Proof. exact (MK_COMB (@lem1207970 _28445 h) (@lem1207969 _28445 t)). Qed.
Lemma lem1207972 {_28445 : Type'} (h : _28445) (t : list _28445) : (term10 _28445 h t) = (@cons _28445 h t).
Proof. exact (TRANS (@lem1207965 _28445 h t) (@lem1207971 _28445 h t)). Qed.
Lemma lem1207973 {_28445 : Type'} : (@eq (list _28445)) = (@eq (list _28445)).
Proof. exact (eq_refl (@eq (list _28445))). Qed.
Lemma lem1207974 {_28445 : Type'} (h : _28445) (t : list _28445) : (term12 _28445 h t) = (term13 _28445 h t).
Proof. exact (MK_COMB (@lem1207973 _28445) (@lem1207972 _28445 h t)). Qed.
Lemma lem1207975 {_28445 : Type'} (h : _28445) (t : list _28445) : (@cons _28445 h t) = (@cons _28445 h t).
Proof. exact (eq_refl (@cons _28445 h t)). Qed.
Lemma lem1207976 {_28445 : Type'} (h : _28445) (t : list _28445) : ((term10 _28445 h t) = (@cons _28445 h t)) = ((@cons _28445 h t) = (@cons _28445 h t)).
Proof. exact (MK_COMB (@lem1207974 _28445 h t) (@lem1207975 _28445 h t)). Qed.
Lemma lem1207978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207979 {_28445 : Type'} (x : list _28445) : (x = x) = True.
Proof. exact (@lem1207978 (list _28445) x). Qed.
Lemma lem1207980 {_28445 : Type'} (h : _28445) (t : list _28445) : ((@cons _28445 h t) = (@cons _28445 h t)) = True.
Proof. exact (@lem1207979 _28445 (@cons _28445 h t)). Qed.
Lemma lem1207981 {_28445 : Type'} (h : _28445) (t : list _28445) : ((term10 _28445 h t) = (@cons _28445 h t)) = True.
Proof. exact (TRANS (@lem1207976 _28445 h t) (@lem1207980 _28445 h t)). Qed.
Lemma lem1207982 {_28445 : Type'} (h : _28445) : (term14 _28445 h) = (term15 _28445).
Proof. exact (fun_ext (fun t : list _28445 => @lem1207981 _28445 h t)). Qed.
Lemma lem1207983 {_28445 : Type'} : (@all (list _28445)) = (@all (list _28445)).
Proof. exact (eq_refl (@all (list _28445))). Qed.
Lemma lem1207984 {_28445 : Type'} (h : _28445) : (term16 _28445 h) = (term17 _28445).
Proof. exact (MK_COMB (@lem1207983 _28445) (@lem1207982 _28445 h)). Qed.
Lemma lem1207986 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1207987 {_28445 : Type'} (t : Prop) : (term19 _28445 t) = t.
Proof. exact (@lem1207986 (list _28445) t). Qed.
Lemma lem1207988 {_28445 : Type'} : (term17 _28445) = True.
Proof. exact (@lem1207987 _28445 True). Qed.
Lemma lem1207989 {_28445 : Type'} (h : _28445) : (term16 _28445 h) = True.
Proof. exact (TRANS (@lem1207984 _28445 h) (@lem1207988 _28445)). Qed.
Lemma lem1207990 {_28445 : Type'} : (term20 _28445) = (term21 _28445).
Proof. exact (fun_ext (fun h : _28445 => @lem1207989 _28445 h)). Qed.
Lemma lem1207991 {_28445 : Type'} : (@all _28445) = (@all _28445).
Proof. exact (eq_refl (@all _28445)). Qed.
Lemma lem1207992 {_28445 : Type'} : (term22 _28445) = (term23 _28445).
Proof. exact (MK_COMB (@lem1207991 _28445) (@lem1207990 _28445)). Qed.
Lemma lem1207994 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1207995 {_28445 : Type'} (t : Prop) : (term18 _28445 t) = t.
Proof. exact (@lem1207994 _28445 t). Qed.
Lemma lem1207996 {_28445 : Type'} : (term23 _28445) = True.
Proof. exact (@lem1207995 _28445 True). Qed.
Lemma lem1207997 {_28445 : Type'} : (term22 _28445) = True.
Proof. exact (TRANS (@lem1207992 _28445) (@lem1207996 _28445)). Qed.
Lemma lem1207998 {_28445 : Type'} : True = (term22 _28445).
Proof. exact (SYM (@lem1207997 _28445)). Qed.
Lemma lem1207999 {_28445 : Type'} : term22 _28445.
Proof. exact (EQ_MP (@lem1207998 _28445) (@lem0)). Qed.
