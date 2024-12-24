Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITLIST_EXTRA_term_abbrevs.
Require Import ITLIST_APPEND_spec.
Require Import thm0_spec.
Require Import thm1102427_spec.
Require Import thm1102428_spec.
Require Import thm1102439_spec.
Require Import thm1102440_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1129524 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : term0 _26617 _26627 f.
Proof. exact (@lem1129521 _26617 _26627 f). Qed.
Lemma lem1129525 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : (term0 _26617 _26627 f) = (term1 _26617 _26627 f).
Proof. exact (eq_refl (term0 _26617 _26627 f)). Qed.
Lemma lem1129526 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : term1 _26617 _26627 f.
Proof. exact (EQ_MP (@lem1129525 _26617 _26627 f) (@lem1129524 _26617 _26627 f)). Qed.
Lemma lem1129527 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term2 _26617 _26627 f a.
Proof. exact (@lem1129526 _26617 _26627 f a). Qed.
Lemma lem1129528 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term2 _26617 _26627 f a) = (term3 _26617 _26627 f a).
Proof. exact (eq_refl (term2 _26617 _26627 f a)). Qed.
Lemma lem1129529 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term3 _26617 _26627 f a.
Proof. exact (EQ_MP (@lem1129528 _26617 _26627 f a) (@lem1129527 _26617 _26627 f a)). Qed.
Lemma lem1129530 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) (l1 : list _26627) : term4 _26617 _26627 f a l1.
Proof. exact (@lem1129529 _26617 _26627 f a l1). Qed.
Lemma lem1129531 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term4 _26617 _26627 f a l1) = (term5 _26617 _26627 l1 f a).
Proof. exact (eq_refl (term4 _26617 _26627 f a l1)). Qed.
Lemma lem1129532 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (a : _26617) : term5 _26617 _26627 l1 f a.
Proof. exact (EQ_MP (@lem1129531 _26617 _26627 l1 f a) (@lem1129530 _26617 _26627 f a l1)). Qed.
Lemma lem1129533 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (a : _26617) (l2 : list _26627) : term6 _26617 _26627 l1 f a l2.
Proof. exact (@lem1129532 _26617 _26627 l1 f a l2). Qed.
Lemma lem1129534 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term6 _26617 _26627 l1 f a l2) = ((term7 _26617 _26627 f l1 l2 a) = (term8 _26617 _26627 l1 f l2 a)).
Proof. exact (eq_refl (term6 _26617 _26627 l1 f a l2)). Qed.
Lemma lem1129543 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term7 _26617 _26627 f l1 l2 a) = (term8 _26617 _26627 l1 f l2 a).
Proof. exact (EQ_MP (@lem1129534 _26617 _26627 l1 f l2 a) (@lem1129533 _26617 _26627 l1 f a l2)). Qed.
Lemma lem1129544 {_26663 _26664 : Type'} (l1 : list _26664) (f : type1467 _26663 _26664) (l2 : list _26664) (a : _26663) : (term7 _26663 _26664 f l1 l2 a) = (term8 _26663 _26664 l1 f l2 a).
Proof. exact (@lem1129543 _26663 _26664 l1 f l2 a). Qed.
Lemma lem1129545 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term9 _26663 _26664 f l a b) = (term10 _26663 _26664 l f a b).
Proof. exact (@lem1129544 _26663 _26664 l f (@cons _26664 a (@nil _26664)) b). Qed.
Lemma lem1129547 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term11 _25350 _25351 f h t b) = (term12 _25350 _25351 h f t b).
Proof. exact (EQ_MP (@lem1102440 _25350 _25351 h f t b) (@lem1102439 _25350 _25351 h f t b)). Qed.
Lemma lem1129548 {_26663 _26664 : Type'} (h : _26664) (f : type1467 _26663 _26664) (t : list _26664) (b : _26663) : (term11 _26663 _26664 f h t b) = (term12 _26663 _26664 h f t b).
Proof. exact (@lem1129547 _26663 _26664 h f t b). Qed.
Lemma lem1129549 {_26663 _26664 : Type'} (a : _26664) (f : type1467 _26663 _26664) (b : _26663) : (term13 _26663 _26664 f a b) = (term14 _26663 _26664 a f b).
Proof. exact (@lem1129548 _26663 _26664 a f (@nil _26664) b). Qed.
Lemma lem1129551 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : (@ITLIST _25350 _25351 f (@nil _25351) b) = b.
Proof. exact (EQ_MP (@lem1102428 _25350 _25351 f b) (@lem1102427 _25350 _25351 f b)). Qed.
Lemma lem1129552 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (b : _26663) : (@ITLIST _26663 _26664 f (@nil _26664) b) = b.
Proof. exact (@lem1129551 _26663 _26664 f b). Qed.
Lemma lem1129553 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem1129554 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term14 _26663 _26664 a f b) = (f a b).
Proof. exact (MK_COMB (@lem1129553 _26663 _26664 f a) (@lem1129552 _26663 _26664 f b)). Qed.
Lemma lem1129555 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term13 _26663 _26664 f a b) = (f a b).
Proof. exact (TRANS (@lem1129549 _26663 _26664 a f b) (@lem1129554 _26663 _26664 f a b)). Qed.
Lemma lem1129556 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (l : list _26664) : (@ITLIST _26663 _26664 f l) = (@ITLIST _26663 _26664 f l).
Proof. exact (eq_refl (@ITLIST _26663 _26664 f l)). Qed.
Lemma lem1129557 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term10 _26663 _26664 l f a b) = (term15 _26663 _26664 l f a b).
Proof. exact (MK_COMB (@lem1129556 _26663 _26664 f l) (@lem1129555 _26663 _26664 f a b)). Qed.
Lemma lem1129558 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term9 _26663 _26664 f l a b) = (term15 _26663 _26664 l f a b).
Proof. exact (TRANS (@lem1129545 _26663 _26664 l f a b) (@lem1129557 _26663 _26664 l f a b)). Qed.
Lemma lem1129559 {_26663 : Type'} : (@eq _26663) = (@eq _26663).
Proof. exact (eq_refl (@eq _26663)). Qed.
Lemma lem1129560 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term16 _26663 _26664 f l a b) = (term17 _26663 _26664 l f a b).
Proof. exact (MK_COMB (@lem1129559 _26663) (@lem1129558 _26663 _26664 l f a b)). Qed.
Lemma lem1129561 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term15 _26663 _26664 l f a b) = (term15 _26663 _26664 l f a b).
Proof. exact (eq_refl (term15 _26663 _26664 l f a b)). Qed.
Lemma lem1129562 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : ((term9 _26663 _26664 f l a b) = (term15 _26663 _26664 l f a b)) = ((term15 _26663 _26664 l f a b) = (term15 _26663 _26664 l f a b)).
Proof. exact (MK_COMB (@lem1129560 _26663 _26664 l f a b) (@lem1129561 _26663 _26664 l f a b)). Qed.
Lemma lem1129564 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1129565 {_26663 : Type'} (x : _26663) : (x = x) = True.
Proof. exact (@lem1129564 _26663 x). Qed.
Lemma lem1129566 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : ((term15 _26663 _26664 l f a b) = (term15 _26663 _26664 l f a b)) = True.
Proof. exact (@lem1129565 _26663 (term15 _26663 _26664 l f a b)). Qed.
Lemma lem1129567 {_26663 _26664 : Type'} (l : list _26664) (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : ((term9 _26663 _26664 f l a b) = (term15 _26663 _26664 l f a b)) = True.
Proof. exact (TRANS (@lem1129562 _26663 _26664 l f a b) (@lem1129566 _26663 _26664 l f a b)). Qed.
Lemma lem1129568 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term18 _26663 _26664 f a b) = (term19 _26664).
Proof. exact (fun_ext (fun l : list _26664 => @lem1129567 _26663 _26664 l f a b)). Qed.
Lemma lem1129569 {_26664 : Type'} : (@all (list _26664)) = (@all (list _26664)).
Proof. exact (eq_refl (@all (list _26664))). Qed.
Lemma lem1129570 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term20 _26663 _26664 f a b) = (term21 _26664).
Proof. exact (MK_COMB (@lem1129569 _26664) (@lem1129568 _26663 _26664 f a b)). Qed.
Lemma lem1129572 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129573 {_26664 : Type'} (t : Prop) : (term23 _26664 t) = t.
Proof. exact (@lem1129572 (list _26664) t). Qed.
Lemma lem1129574 {_26664 : Type'} : (term21 _26664) = True.
Proof. exact (@lem1129573 _26664 True). Qed.
Lemma lem1129575 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : (term20 _26663 _26664 f a b) = True.
Proof. exact (TRANS (@lem1129570 _26663 _26664 f a b) (@lem1129574 _26664)). Qed.
Lemma lem1129576 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : True = (term20 _26663 _26664 f a b).
Proof. exact (SYM (@lem1129575 _26663 _26664 f a b)). Qed.
Lemma lem1129577 {_26663 _26664 : Type'} (f : type1467 _26663 _26664) (a : _26664) (b : _26663) : term20 _26663 _26664 f a b.
Proof. exact (EQ_MP (@lem1129576 _26663 _26664 f a b) (@lem0)). Qed.
