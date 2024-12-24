Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_DIFF_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_DIFF_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4361538 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4361539 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4361540 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4361539 _103718 _103721 x) (@lem4361538 _103718 _103721 x)). Qed.
Lemma lem4361541 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4361540 _103718 _103721 x y). Qed.
Lemma lem4361542 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4361543 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4361542 _103718 _103721 x y) (@lem4361541 _103718 _103721 x y)). Qed.
Lemma lem4361544 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4361543 _103718 _103721 x y s). Qed.
Lemma lem4361545 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4361546 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4361545 _103718 _103721 x s y) (@lem4361544 _103718 _103721 x y s)). Qed.
Lemma lem4361547 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4361546 _103718 _103721 x s y t). Qed.
Lemma lem4361548 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4361550 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem4361551 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem4361552 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem4361551 A s) (@lem4361550 A s)). Qed.
Lemma lem4361553 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem4361552 A s t). Qed.
Lemma lem4361554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem4361555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem4361554 A s t) (@lem4361553 A s t)). Qed.
Lemma lem4361556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem4361555 A s t x). Qed.
Lemma lem4361557 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem4361559 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term16 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4361560 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = ((term17 _5106 _5107 P) = (term18 _5106 _5107 P)).
Proof. exact (eq_refl (term16 _5106 _5107 P)). Qed.
Lemma lem4361562 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4361563 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4361564 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem4361563 A s) (@lem4361562 A s)). Qed.
Lemma lem4361565 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem4361564 A s t). Qed.
Lemma lem4361566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((s = t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem4361591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4361566 A s t) (@lem4361565 A s t)). Qed.
Lemma lem4361592 {_104591 _104592 : Type'} (s : type1210 _104591 _104592) (t : type1210 _104591 _104592) : (s = t) = (term23 _104591 _104592 s t).
Proof. exact (@lem4361591 (prod _104591 _104592) s t). Qed.
Lemma lem4361593 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : ((term24 _104591 _104592 s t u) = (term25 _104591 _104592 t s u)) = (term26 _104591 _104592 t s u).
Proof. exact (@lem4361592 _104591 _104592 (term24 _104591 _104592 s t u) (term25 _104591 _104592 t s u)). Qed.
Lemma lem4361599 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4361560 _5106 _5107 P) (@lem4361559 _5106 _5107 P)). Qed.
Lemma lem4361600 {_104591 _104592 : Type'} (P : type1210 _104591 _104592) : (term27 _104591 _104592 P) = (term28 _104591 _104592 P).
Proof. exact (@lem4361599 _104592 _104591 P). Qed.
Lemma lem4361601 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term29 _104591 _104592 t s u) = (term30 _104591 _104592 t s u).
Proof. exact (@lem4361600 _104591 _104592 (term31 _104591 _104592 t s u)). Qed.
Lemma lem4361602 {_104591 _104592 : Type'} (x : prod _104591 _104592) (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term32 _104591 _104592 t s u x) = ((term33 _104591 _104592 x s t u) = (term34 _104591 _104592 x t s u)).
Proof. exact (eq_refl (term32 _104591 _104592 t s u x)). Qed.
Lemma lem4361603 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term35 _104591 _104592 t s u) = (term31 _104591 _104592 t s u).
Proof. exact (fun_ext (fun x : prod _104591 _104592 => @lem4361602 _104591 _104592 x t s u)). Qed.
Lemma lem4361604 {_104591 _104592 : Type'} : (@all (prod _104591 _104592)) = (@all (prod _104591 _104592)).
Proof. exact (eq_refl (@all (prod _104591 _104592))). Qed.
Lemma lem4361605 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term29 _104591 _104592 t s u) = (term26 _104591 _104592 t s u).
Proof. exact (MK_COMB (@lem4361604 _104591 _104592) (@lem4361603 _104591 _104592 t s u)). Qed.
Lemma lem4361606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361607 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term36 _104591 _104592 t s u) = (term37 _104591 _104592 t s u).
Proof. exact (MK_COMB (@lem4361606) (@lem4361605 _104591 _104592 t s u)). Qed.
Lemma lem4361608 {_104591 _104592 : Type'} (p1 : _104591) (p2 : _104592) (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term38 _104591 _104592 t s u p1 p2) = ((term39 _104591 _104592 p1 p2 s t u) = (term40 _104591 _104592 p1 p2 t s u)).
Proof. exact (eq_refl (term38 _104591 _104592 t s u p1 p2)). Qed.
Lemma lem4361609 {_104591 _104592 : Type'} (p1 : _104591) (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term41 _104591 _104592 t s u p1) = (term42 _104591 _104592 p1 t s u).
Proof. exact (fun_ext (fun p2 : _104592 => @lem4361608 _104591 _104592 p1 p2 t s u)). Qed.
Lemma lem4361610 {_104592 : Type'} : (@all _104592) = (@all _104592).
Proof. exact (eq_refl (@all _104592)). Qed.
Lemma lem4361611 {_104591 _104592 : Type'} (p1 : _104591) (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term43 _104591 _104592 t s u p1) = (term44 _104591 _104592 p1 t s u).
Proof. exact (MK_COMB (@lem4361610 _104592) (@lem4361609 _104591 _104592 p1 t s u)). Qed.
Lemma lem4361612 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term45 _104591 _104592 t s u) = (term46 _104591 _104592 t s u).
Proof. exact (fun_ext (fun p1 : _104591 => @lem4361611 _104591 _104592 p1 t s u)). Qed.
Lemma lem4361613 {_104591 : Type'} : (@all _104591) = (@all _104591).
Proof. exact (eq_refl (@all _104591)). Qed.
Lemma lem4361614 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term30 _104591 _104592 t s u) = (term47 _104591 _104592 t s u).
Proof. exact (MK_COMB (@lem4361613 _104591) (@lem4361612 _104591 _104592 t s u)). Qed.
Lemma lem4361615 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : ((term29 _104591 _104592 t s u) = (term30 _104591 _104592 t s u)) = ((term26 _104591 _104592 t s u) = (term47 _104591 _104592 t s u)).
Proof. exact (MK_COMB (@lem4361607 _104591 _104592 t s u) (@lem4361614 _104591 _104592 t s u)). Qed.
Lemma lem4361616 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term26 _104591 _104592 t s u) = (term47 _104591 _104592 t s u).
Proof. exact (EQ_MP (@lem4361615 _104591 _104592 t s u) (@lem4361601 _104591 _104592 t s u)). Qed.
Lemma lem4361623 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : ((term24 _104591 _104592 s t u) = (term25 _104591 _104592 t s u)) = (term47 _104591 _104592 t s u).
Proof. exact (TRANS (@lem4361593 _104591 _104592 t s u) (@lem4361616 _104591 _104592 t s u)). Qed.
Lemma lem4361635 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361636 {_104591 _104592 : Type'} (x : _104591) (s : _104591 -> Prop) (y : _104592) (t : _104592 -> Prop) : (term7 _104591 _104592 x y s t) = (term8 _104591 _104592 x s y t).
Proof. exact (@lem4361635 _104591 _104592 x s y t). Qed.
Lemma lem4361637 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (t : _104592 -> Prop) (u : _104592 -> Prop) : (term39 _104591 _104592 p1 p2 s t u) = (term48 _104591 _104592 p1 s p2 t u).
Proof. exact (@lem4361636 _104591 _104592 p1 s p2 (@DIFF _104592 t u)). Qed.
Lemma lem4361641 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4361557 A s x t) (@lem4361556 A s t x)). Qed.
Lemma lem4361642 {_104592 : Type'} (s : _104592 -> Prop) (x : _104592) (t : _104592 -> Prop) : (term14 _104592 x s t) = (term15 _104592 s x t).
Proof. exact (@lem4361641 _104592 s x t). Qed.
Lemma lem4361643 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term14 _104592 p2 t u) = (term15 _104592 t p2 u).
Proof. exact (@lem4361642 _104592 t p2 u). Qed.
Lemma lem4361646 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) : (term49 _104591 p1 s) = (term49 _104591 p1 s).
Proof. exact (eq_refl (term49 _104591 p1 s)). Qed.
Lemma lem4361647 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term48 _104591 _104592 p1 s p2 t u) = (term50 _104591 _104592 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4361646 _104591 p1 s) (@lem4361643 _104592 t p2 u)). Qed.
Lemma lem4361650 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term39 _104591 _104592 p1 p2 s t u) = (term50 _104591 _104592 p1 s t p2 u).
Proof. exact (TRANS (@lem4361637 _104591 _104592 p1 s p2 t u) (@lem4361647 _104591 _104592 p1 s t p2 u)). Qed.
Lemma lem4361651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361652 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term51 _104591 _104592 p1 p2 s t u) = (term52 _104591 _104592 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4361651) (@lem4361650 _104591 _104592 p1 s t p2 u)). Qed.
Lemma lem4361654 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4361557 A s x t) (@lem4361556 A s t x)). Qed.
Lemma lem4361655 {_104591 _104592 : Type'} (s : type1210 _104591 _104592) (x : prod _104591 _104592) (t : type1210 _104591 _104592) : (term53 _104591 _104592 x s t) = (term54 _104591 _104592 s x t).
Proof. exact (@lem4361654 (prod _104591 _104592) s x t). Qed.
Lemma lem4361656 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (p2 : _104592) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term40 _104591 _104592 p1 p2 t s u) = (term55 _104591 _104592 t p1 p2 s u).
Proof. exact (@lem4361655 _104591 _104592 (@CROSS _104592 _104591 s t) (@pair _104591 _104592 p1 p2) (@CROSS _104592 _104591 s u)). Qed.
Lemma lem4361660 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361661 {_104591 _104592 : Type'} (x : _104591) (s : _104591 -> Prop) (y : _104592) (t : _104592 -> Prop) : (term7 _104591 _104592 x y s t) = (term8 _104591 _104592 x s y t).
Proof. exact (@lem4361660 _104591 _104592 x s y t). Qed.
Lemma lem4361662 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (t : _104592 -> Prop) : (term7 _104591 _104592 p1 p2 s t) = (term8 _104591 _104592 p1 s p2 t).
Proof. exact (@lem4361661 _104591 _104592 p1 s p2 t). Qed.
Lemma lem4361665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361666 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (t : _104592 -> Prop) : (term56 _104591 _104592 p1 p2 s t) = (term57 _104591 _104592 p1 s p2 t).
Proof. exact (MK_COMB (@lem4361665) (@lem4361662 _104591 _104592 p1 s p2 t)). Qed.
Lemma lem4361668 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361669 {_104591 _104592 : Type'} (x : _104591) (s : _104591 -> Prop) (y : _104592) (t : _104592 -> Prop) : (term7 _104591 _104592 x y s t) = (term8 _104591 _104592 x s y t).
Proof. exact (@lem4361668 _104591 _104592 x s y t). Qed.
Lemma lem4361670 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term7 _104591 _104592 p1 p2 s u) = (term8 _104591 _104592 p1 s p2 u).
Proof. exact (@lem4361669 _104591 _104592 p1 s p2 u). Qed.
Lemma lem4361673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4361674 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term58 _104591 _104592 p1 p2 s u) = (term59 _104591 _104592 p1 s p2 u).
Proof. exact (MK_COMB (@lem4361673) (@lem4361670 _104591 _104592 p1 s p2 u)). Qed.
Lemma lem4361675 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term55 _104591 _104592 t p1 p2 s u) = (term60 _104591 _104592 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4361666 _104591 _104592 p1 s p2 t) (@lem4361674 _104591 _104592 p1 s p2 u)). Qed.
Lemma lem4361678 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term40 _104591 _104592 p1 p2 t s u) = (term60 _104591 _104592 t p1 s p2 u).
Proof. exact (TRANS (@lem4361656 _104591 _104592 t p1 p2 s u) (@lem4361675 _104591 _104592 t p1 s p2 u)). Qed.
Lemma lem4361679 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term39 _104591 _104592 p1 p2 s t u) = (term40 _104591 _104592 p1 p2 t s u)) = ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)).
Proof. exact (MK_COMB (@lem4361652 _104591 _104592 p1 s t p2 u) (@lem4361678 _104591 _104592 t p1 s p2 u)). Qed.
Lemma lem4361684 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term42 _104591 _104592 p1 t s u) = (term61 _104591 _104592 t p1 s u).
Proof. exact (fun_ext (fun p2 : _104592 => @lem4361679 _104591 _104592 t p1 s p2 u)). Qed.
Lemma lem4361685 {_104592 : Type'} : (@all _104592) = (@all _104592).
Proof. exact (eq_refl (@all _104592)). Qed.
Lemma lem4361686 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term44 _104591 _104592 p1 t s u) = (term62 _104591 _104592 t p1 s u).
Proof. exact (MK_COMB (@lem4361685 _104592) (@lem4361684 _104591 _104592 t p1 s u)). Qed.
Lemma lem4361693 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term46 _104591 _104592 t s u) = (term63 _104591 _104592 t s u).
Proof. exact (fun_ext (fun p1 : _104591 => @lem4361686 _104591 _104592 t p1 s u)). Qed.
Lemma lem4361694 {_104591 : Type'} : (@all _104591) = (@all _104591).
Proof. exact (eq_refl (@all _104591)). Qed.
Lemma lem4361695 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : (term47 _104591 _104592 t s u) = (term64 _104591 _104592 t s u).
Proof. exact (MK_COMB (@lem4361694 _104591) (@lem4361693 _104591 _104592 t s u)). Qed.
Lemma lem4361702 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : ((term24 _104591 _104592 s t u) = (term25 _104591 _104592 t s u)) = (term64 _104591 _104592 t s u).
Proof. exact (TRANS (@lem4361623 _104591 _104592 t s u) (@lem4361695 _104591 _104592 t s u)). Qed.
Lemma lem4361703 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) : (term65 _104591 _104592 t s) = (term66 _104591 _104592 t s).
Proof. exact (fun_ext (fun u : _104592 -> Prop => @lem4361702 _104591 _104592 t s u)). Qed.
Lemma lem4361704 {_104592 : Type'} : (@all (_104592 -> Prop)) = (@all (_104592 -> Prop)).
Proof. exact (eq_refl (@all (_104592 -> Prop))). Qed.
Lemma lem4361705 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) : (term67 _104591 _104592 t s) = (term68 _104591 _104592 t s).
Proof. exact (MK_COMB (@lem4361704 _104592) (@lem4361703 _104591 _104592 t s)). Qed.
Lemma lem4361712 {_104591 _104592 : Type'} (s : _104591 -> Prop) : (term69 _104591 _104592 s) = (term70 _104591 _104592 s).
Proof. exact (fun_ext (fun t : _104592 -> Prop => @lem4361705 _104591 _104592 t s)). Qed.
Lemma lem4361713 {_104592 : Type'} : (@all (_104592 -> Prop)) = (@all (_104592 -> Prop)).
Proof. exact (eq_refl (@all (_104592 -> Prop))). Qed.
Lemma lem4361714 {_104591 _104592 : Type'} (s : _104591 -> Prop) : (term71 _104591 _104592 s) = (term72 _104591 _104592 s).
Proof. exact (MK_COMB (@lem4361713 _104592) (@lem4361712 _104591 _104592 s)). Qed.
Lemma lem4361721 {_104591 _104592 : Type'} : (term73 _104591 _104592) = (term74 _104591 _104592).
Proof. exact (fun_ext (fun s : _104591 -> Prop => @lem4361714 _104591 _104592 s)). Qed.
Lemma lem4361722 {_104591 : Type'} : (@all (_104591 -> Prop)) = (@all (_104591 -> Prop)).
Proof. exact (eq_refl (@all (_104591 -> Prop))). Qed.
Lemma lem4361723 {_104591 _104592 : Type'} : (term75 _104591 _104592) = (term76 _104591 _104592).
Proof. exact (MK_COMB (@lem4361722 _104591) (@lem4361721 _104591 _104592)). Qed.
Lemma lem4361730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361731 {_104591 _104592 : Type'} : (term77 _104591 _104592) = (term78 _104591 _104592).
Proof. exact (MK_COMB (@lem4361730) (@lem4361723 _104591 _104592)). Qed.
Lemma lem4361753 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4361566 A s t) (@lem4361565 A s t)). Qed.
Lemma lem4361754 {_104624 _104625 : Type'} (s : type1210 _104624 _104625) (t : type1210 _104624 _104625) : (s = t) = (term23 _104624 _104625 s t).
Proof. exact (@lem4361753 (prod _104624 _104625) s t). Qed.
Lemma lem4361755 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : ((term79 _104624 _104625 s t u) = (term80 _104624 _104625 s t u)) = (term81 _104624 _104625 s t u).
Proof. exact (@lem4361754 _104624 _104625 (term79 _104624 _104625 s t u) (term80 _104624 _104625 s t u)). Qed.
Lemma lem4361761 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4361560 _5106 _5107 P) (@lem4361559 _5106 _5107 P)). Qed.
Lemma lem4361762 {_104624 _104625 : Type'} (P : type1210 _104624 _104625) : (term27 _104624 _104625 P) = (term28 _104624 _104625 P).
Proof. exact (@lem4361761 _104625 _104624 P). Qed.
Lemma lem4361763 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term82 _104624 _104625 s t u) = (term83 _104624 _104625 s t u).
Proof. exact (@lem4361762 _104624 _104625 (term84 _104624 _104625 s t u)). Qed.
Lemma lem4361764 {_104624 _104625 : Type'} (x : prod _104624 _104625) (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term85 _104624 _104625 s t u x) = ((term86 _104624 _104625 x s t u) = (term87 _104624 _104625 x s t u)).
Proof. exact (eq_refl (term85 _104624 _104625 s t u x)). Qed.
Lemma lem4361765 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term88 _104624 _104625 s t u) = (term84 _104624 _104625 s t u).
Proof. exact (fun_ext (fun x : prod _104624 _104625 => @lem4361764 _104624 _104625 x s t u)). Qed.
Lemma lem4361766 {_104624 _104625 : Type'} : (@all (prod _104624 _104625)) = (@all (prod _104624 _104625)).
Proof. exact (eq_refl (@all (prod _104624 _104625))). Qed.
Lemma lem4361767 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term82 _104624 _104625 s t u) = (term81 _104624 _104625 s t u).
Proof. exact (MK_COMB (@lem4361766 _104624 _104625) (@lem4361765 _104624 _104625 s t u)). Qed.
Lemma lem4361768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361769 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term89 _104624 _104625 s t u) = (term90 _104624 _104625 s t u).
Proof. exact (MK_COMB (@lem4361768) (@lem4361767 _104624 _104625 s t u)). Qed.
Lemma lem4361770 {_104624 _104625 : Type'} (p1 : _104624) (p2 : _104625) (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term91 _104624 _104625 s t u p1 p2) = ((term92 _104624 _104625 p1 p2 s t u) = (term93 _104624 _104625 p1 p2 s t u)).
Proof. exact (eq_refl (term91 _104624 _104625 s t u p1 p2)). Qed.
Lemma lem4361771 {_104624 _104625 : Type'} (p1 : _104624) (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term94 _104624 _104625 s t u p1) = (term95 _104624 _104625 p1 s t u).
Proof. exact (fun_ext (fun p2 : _104625 => @lem4361770 _104624 _104625 p1 p2 s t u)). Qed.
Lemma lem4361772 {_104625 : Type'} : (@all _104625) = (@all _104625).
Proof. exact (eq_refl (@all _104625)). Qed.
Lemma lem4361773 {_104624 _104625 : Type'} (p1 : _104624) (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term96 _104624 _104625 s t u p1) = (term97 _104624 _104625 p1 s t u).
Proof. exact (MK_COMB (@lem4361772 _104625) (@lem4361771 _104624 _104625 p1 s t u)). Qed.
Lemma lem4361774 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term98 _104624 _104625 s t u) = (term99 _104624 _104625 s t u).
Proof. exact (fun_ext (fun p1 : _104624 => @lem4361773 _104624 _104625 p1 s t u)). Qed.
Lemma lem4361775 {_104624 : Type'} : (@all _104624) = (@all _104624).
Proof. exact (eq_refl (@all _104624)). Qed.
Lemma lem4361776 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term83 _104624 _104625 s t u) = (term100 _104624 _104625 s t u).
Proof. exact (MK_COMB (@lem4361775 _104624) (@lem4361774 _104624 _104625 s t u)). Qed.
Lemma lem4361777 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : ((term82 _104624 _104625 s t u) = (term83 _104624 _104625 s t u)) = ((term81 _104624 _104625 s t u) = (term100 _104624 _104625 s t u)).
Proof. exact (MK_COMB (@lem4361769 _104624 _104625 s t u) (@lem4361776 _104624 _104625 s t u)). Qed.
Lemma lem4361778 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term81 _104624 _104625 s t u) = (term100 _104624 _104625 s t u).
Proof. exact (EQ_MP (@lem4361777 _104624 _104625 s t u) (@lem4361763 _104624 _104625 s t u)). Qed.
Lemma lem4361785 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : ((term79 _104624 _104625 s t u) = (term80 _104624 _104625 s t u)) = (term100 _104624 _104625 s t u).
Proof. exact (TRANS (@lem4361755 _104624 _104625 s t u) (@lem4361778 _104624 _104625 s t u)). Qed.
Lemma lem4361797 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361798 {_104624 _104625 : Type'} (x : _104624) (s : _104624 -> Prop) (y : _104625) (t : _104625 -> Prop) : (term7 _104624 _104625 x y s t) = (term8 _104624 _104625 x s y t).
Proof. exact (@lem4361797 _104624 _104625 x s y t). Qed.
Lemma lem4361799 {_104624 _104625 : Type'} (p1 : _104624) (s : _104624 -> Prop) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term92 _104624 _104625 p1 p2 s t u) = (term101 _104624 _104625 p1 s t p2 u).
Proof. exact (@lem4361798 _104624 _104625 p1 (@DIFF _104624 s t) p2 u). Qed.
Lemma lem4361803 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4361557 A s x t) (@lem4361556 A s t x)). Qed.
Lemma lem4361804 {_104624 : Type'} (s : _104624 -> Prop) (x : _104624) (t : _104624 -> Prop) : (term14 _104624 x s t) = (term15 _104624 s x t).
Proof. exact (@lem4361803 _104624 s x t). Qed.
Lemma lem4361805 {_104624 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) : (term14 _104624 p1 s t) = (term15 _104624 s p1 t).
Proof. exact (@lem4361804 _104624 s p1 t). Qed.
Lemma lem4361808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361809 {_104624 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) : (term102 _104624 p1 s t) = (term103 _104624 s p1 t).
Proof. exact (MK_COMB (@lem4361808) (@lem4361805 _104624 s p1 t)). Qed.
Lemma lem4361810 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (@IN _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (eq_refl (@IN _104625 p2 u)). Qed.
Lemma lem4361811 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term101 _104624 _104625 p1 s t p2 u) = (term104 _104624 _104625 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361809 _104624 s p1 t) (@lem4361810 _104625 p2 u)). Qed.
Lemma lem4361814 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term92 _104624 _104625 p1 p2 s t u) = (term104 _104624 _104625 s p1 t p2 u).
Proof. exact (TRANS (@lem4361799 _104624 _104625 p1 s t p2 u) (@lem4361811 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4361815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361816 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term105 _104624 _104625 p1 p2 s t u) = (term106 _104624 _104625 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361815) (@lem4361814 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4361818 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4361557 A s x t) (@lem4361556 A s t x)). Qed.
Lemma lem4361819 {_104624 _104625 : Type'} (s : type1210 _104624 _104625) (x : prod _104624 _104625) (t : type1210 _104624 _104625) : (term53 _104624 _104625 x s t) = (term54 _104624 _104625 s x t).
Proof. exact (@lem4361818 (prod _104624 _104625) s x t). Qed.
Lemma lem4361820 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (p2 : _104625) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term93 _104624 _104625 p1 p2 s t u) = (term107 _104624 _104625 s p1 p2 t u).
Proof. exact (@lem4361819 _104624 _104625 (@CROSS _104625 _104624 s u) (@pair _104624 _104625 p1 p2) (@CROSS _104625 _104624 t u)). Qed.
Lemma lem4361824 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361825 {_104624 _104625 : Type'} (x : _104624) (s : _104624 -> Prop) (y : _104625) (t : _104625 -> Prop) : (term7 _104624 _104625 x y s t) = (term8 _104624 _104625 x s y t).
Proof. exact (@lem4361824 _104624 _104625 x s y t). Qed.
Lemma lem4361826 {_104624 _104625 : Type'} (p1 : _104624) (s : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term7 _104624 _104625 p1 p2 s u) = (term8 _104624 _104625 p1 s p2 u).
Proof. exact (@lem4361825 _104624 _104625 p1 s p2 u). Qed.
Lemma lem4361829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361830 {_104624 _104625 : Type'} (p1 : _104624) (s : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term56 _104624 _104625 p1 p2 s u) = (term57 _104624 _104625 p1 s p2 u).
Proof. exact (MK_COMB (@lem4361829) (@lem4361826 _104624 _104625 p1 s p2 u)). Qed.
Lemma lem4361832 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4361548 _103718 _103721 x s y t) (@lem4361547 _103718 _103721 x s y t)). Qed.
Lemma lem4361833 {_104624 _104625 : Type'} (x : _104624) (s : _104624 -> Prop) (y : _104625) (t : _104625 -> Prop) : (term7 _104624 _104625 x y s t) = (term8 _104624 _104625 x s y t).
Proof. exact (@lem4361832 _104624 _104625 x s y t). Qed.
Lemma lem4361834 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term7 _104624 _104625 p1 p2 t u) = (term8 _104624 _104625 p1 t p2 u).
Proof. exact (@lem4361833 _104624 _104625 p1 t p2 u). Qed.
Lemma lem4361837 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4361838 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term58 _104624 _104625 p1 p2 t u) = (term59 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361837) (@lem4361834 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4361839 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term107 _104624 _104625 s p1 p2 t u) = (term108 _104624 _104625 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361830 _104624 _104625 p1 s p2 u) (@lem4361838 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4361842 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term93 _104624 _104625 p1 p2 s t u) = (term108 _104624 _104625 s p1 t p2 u).
Proof. exact (TRANS (@lem4361820 _104624 _104625 s p1 p2 t u) (@lem4361839 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4361843 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term92 _104624 _104625 p1 p2 s t u) = (term93 _104624 _104625 p1 p2 s t u)) = ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)).
Proof. exact (MK_COMB (@lem4361816 _104624 _104625 s p1 t p2 u) (@lem4361842 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4361848 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term95 _104624 _104625 p1 s t u) = (term109 _104624 _104625 s p1 t u).
Proof. exact (fun_ext (fun p2 : _104625 => @lem4361843 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4361849 {_104625 : Type'} : (@all _104625) = (@all _104625).
Proof. exact (eq_refl (@all _104625)). Qed.
Lemma lem4361850 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term97 _104624 _104625 p1 s t u) = (term110 _104624 _104625 s p1 t u).
Proof. exact (MK_COMB (@lem4361849 _104625) (@lem4361848 _104624 _104625 s p1 t u)). Qed.
Lemma lem4361857 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term99 _104624 _104625 s t u) = (term111 _104624 _104625 s t u).
Proof. exact (fun_ext (fun p1 : _104624 => @lem4361850 _104624 _104625 s p1 t u)). Qed.
Lemma lem4361858 {_104624 : Type'} : (@all _104624) = (@all _104624).
Proof. exact (eq_refl (@all _104624)). Qed.
Lemma lem4361859 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : (term100 _104624 _104625 s t u) = (term112 _104624 _104625 s t u).
Proof. exact (MK_COMB (@lem4361858 _104624) (@lem4361857 _104624 _104625 s t u)). Qed.
Lemma lem4361866 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : ((term79 _104624 _104625 s t u) = (term80 _104624 _104625 s t u)) = (term112 _104624 _104625 s t u).
Proof. exact (TRANS (@lem4361785 _104624 _104625 s t u) (@lem4361859 _104624 _104625 s t u)). Qed.
Lemma lem4361867 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) : (term113 _104624 _104625 s t) = (term114 _104624 _104625 s t).
Proof. exact (fun_ext (fun u : _104625 -> Prop => @lem4361866 _104624 _104625 s t u)). Qed.
Lemma lem4361868 {_104625 : Type'} : (@all (_104625 -> Prop)) = (@all (_104625 -> Prop)).
Proof. exact (eq_refl (@all (_104625 -> Prop))). Qed.
Lemma lem4361869 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) : (term115 _104624 _104625 s t) = (term116 _104624 _104625 s t).
Proof. exact (MK_COMB (@lem4361868 _104625) (@lem4361867 _104624 _104625 s t)). Qed.
Lemma lem4361876 {_104624 _104625 : Type'} (s : _104624 -> Prop) : (term117 _104624 _104625 s) = (term118 _104624 _104625 s).
Proof. exact (fun_ext (fun t : _104624 -> Prop => @lem4361869 _104624 _104625 s t)). Qed.
Lemma lem4361877 {_104624 : Type'} : (@all (_104624 -> Prop)) = (@all (_104624 -> Prop)).
Proof. exact (eq_refl (@all (_104624 -> Prop))). Qed.
Lemma lem4361878 {_104624 _104625 : Type'} (s : _104624 -> Prop) : (term119 _104624 _104625 s) = (term120 _104624 _104625 s).
Proof. exact (MK_COMB (@lem4361877 _104624) (@lem4361876 _104624 _104625 s)). Qed.
Lemma lem4361885 {_104624 _104625 : Type'} : (term121 _104624 _104625) = (term122 _104624 _104625).
Proof. exact (fun_ext (fun s : _104624 -> Prop => @lem4361878 _104624 _104625 s)). Qed.
Lemma lem4361886 {_104624 : Type'} : (@all (_104624 -> Prop)) = (@all (_104624 -> Prop)).
Proof. exact (eq_refl (@all (_104624 -> Prop))). Qed.
Lemma lem4361887 {_104624 _104625 : Type'} : (term123 _104624 _104625) = (term124 _104624 _104625).
Proof. exact (MK_COMB (@lem4361886 _104624) (@lem4361885 _104624 _104625)). Qed.
Lemma lem4361894 {_104591 _104592 _104624 _104625 : Type'} : (term125 _104591 _104592 _104624 _104625) = (term126 _104591 _104592 _104624 _104625).
Proof. exact (MK_COMB (@lem4361731 _104591 _104592) (@lem4361887 _104624 _104625)). Qed.
Lemma lem4361897 {_104591 _104592 _104624 _104625 : Type'} : (term126 _104591 _104592 _104624 _104625) = (term125 _104591 _104592 _104624 _104625).
Proof. exact (SYM (@lem4361894 _104591 _104592 _104624 _104625)). Qed.
Lemma lem4361912 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) : term127 _104591 p1 s.
Proof. exact (@lem9851 (@IN _104591 p1 s)). Qed.
Lemma lem4361913 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) : (term127 _104591 p1 s) = (term128 _104591 p1 s).
Proof. exact (eq_refl (term127 _104591 p1 s)). Qed.
Lemma lem4361914 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) : term128 _104591 p1 s.
Proof. exact (EQ_MP (@lem4361913 _104591 p1 s) (@lem4361912 _104591 p1 s)). Qed.
Lemma lem4361915 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = True) : (@IN _104591 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4361916 {_104591 : Type'} (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = False) : (@IN _104591 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4361931 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term129 _104592 t p2 u) = (term129 _104592 t p2 u).
Proof. exact (eq_refl (term129 _104592 t p2 u)). Qed.
Lemma lem4361932 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = True) : (term130 _104591 _104592 t p2 u p1 s) = (term131 _104592 t p2 u).
Proof. exact (MK_COMB (@lem4361931 _104592 t p2 u) (@lem4361915 _104591 p1 s h1)). Qed.
Lemma lem4361933 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term131 _104592 t p2 u) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)).
Proof. exact (eq_refl (term131 _104592 t p2 u)). Qed.
Lemma lem4361934 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) : (term134 _104591 _104592 t p2 u p1 s) = (term134 _104591 _104592 t p2 u p1 s).
Proof. exact (eq_refl (term134 _104591 _104592 t p2 u p1 s)). Qed.
Lemma lem4361935 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = (term131 _104592 t p2 u)) = ((term130 _104591 _104592 t p2 u p1 s) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u))).
Proof. exact (MK_COMB (@lem4361934 _104591 _104592 t p2 u p1 s) (@lem4361933 _104592 t p2 u)). Qed.
Lemma lem4361936 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term130 _104591 _104592 t p2 u p1 s) = ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)).
Proof. exact (eq_refl (term130 _104591 _104592 t p2 u p1 s)). Qed.
Lemma lem4361937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361938 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term134 _104591 _104592 t p2 u p1 s) = (term135 _104591 _104592 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4361937) (@lem4361936 _104591 _104592 t p1 s p2 u)). Qed.
Lemma lem4361939 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)).
Proof. exact (eq_refl ((term132 _104592 t p2 u) = (term133 _104592 t p2 u))). Qed.
Lemma lem4361940 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u))) = (((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u))).
Proof. exact (MK_COMB (@lem4361938 _104591 _104592 t p1 s p2 u) (@lem4361939 _104592 t p2 u)). Qed.
Lemma lem4361941 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = (term131 _104592 t p2 u)) = (((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u))).
Proof. exact (TRANS (@lem4361935 _104591 _104592 p1 s t p2 u) (@lem4361940 _104591 _104592 p1 s t p2 u)). Qed.
Lemma lem4361942 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = True) : ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)).
Proof. exact (EQ_MP (@lem4361941 _104591 _104592 p1 s t p2 u) (@lem4361932 _104591 _104592 t p2 u p1 s h1)). Qed.
Lemma lem4361943 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = True) : ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)) = ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)).
Proof. exact (SYM (@lem4361942 _104591 _104592 t p2 u p1 s h1)). Qed.
Lemma lem4361944 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term129 _104592 t p2 u) = (term129 _104592 t p2 u).
Proof. exact (eq_refl (term129 _104592 t p2 u)). Qed.
Lemma lem4361945 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = False) : (term130 _104591 _104592 t p2 u p1 s) = (term136 _104592 t p2 u).
Proof. exact (MK_COMB (@lem4361944 _104592 t p2 u) (@lem4361916 _104591 p1 s h1)). Qed.
Lemma lem4361946 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term136 _104592 t p2 u) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)).
Proof. exact (eq_refl (term136 _104592 t p2 u)). Qed.
Lemma lem4361947 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) : (term134 _104591 _104592 t p2 u p1 s) = (term134 _104591 _104592 t p2 u p1 s).
Proof. exact (eq_refl (term134 _104591 _104592 t p2 u p1 s)). Qed.
Lemma lem4361948 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = (term136 _104592 t p2 u)) = ((term130 _104591 _104592 t p2 u p1 s) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u))).
Proof. exact (MK_COMB (@lem4361947 _104591 _104592 t p2 u p1 s) (@lem4361946 _104592 t p2 u)). Qed.
Lemma lem4361949 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term130 _104591 _104592 t p2 u p1 s) = ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)).
Proof. exact (eq_refl (term130 _104591 _104592 t p2 u p1 s)). Qed.
Lemma lem4361950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361951 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term134 _104591 _104592 t p2 u p1 s) = (term135 _104591 _104592 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4361950) (@lem4361949 _104591 _104592 t p1 s p2 u)). Qed.
Lemma lem4361952 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)).
Proof. exact (eq_refl ((term137 _104592 t p2 u) = (term138 _104592 t p2 u))). Qed.
Lemma lem4361953 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u))) = (((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u))).
Proof. exact (MK_COMB (@lem4361951 _104591 _104592 t p1 s p2 u) (@lem4361952 _104592 t p2 u)). Qed.
Lemma lem4361954 {_104591 _104592 : Type'} (p1 : _104591) (s : _104591 -> Prop) (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term130 _104591 _104592 t p2 u p1 s) = (term136 _104592 t p2 u)) = (((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u))).
Proof. exact (TRANS (@lem4361948 _104591 _104592 p1 s t p2 u) (@lem4361953 _104591 _104592 p1 s t p2 u)). Qed.
Lemma lem4361955 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = False) : ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)) = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)).
Proof. exact (EQ_MP (@lem4361954 _104591 _104592 p1 s t p2 u) (@lem4361945 _104591 _104592 t p2 u p1 s h1)). Qed.
Lemma lem4361956 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = False) : ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)) = ((term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u)).
Proof. exact (SYM (@lem4361955 _104591 _104592 t p2 u p1 s h1)). Qed.
Lemma lem4361960 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361961 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term132 _104592 t p2 u) = (term15 _104592 t p2 u).
Proof. exact (@lem4361960 (term15 _104592 t p2 u)). Qed.
Lemma lem4361964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361965 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term139 _104592 t p2 u) = (term140 _104592 t p2 u).
Proof. exact (MK_COMB (@lem4361964) (@lem4361961 _104592 t p2 u)). Qed.
Lemma lem4361969 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361970 {_104592 : Type'} (p2 : _104592) (t : _104592 -> Prop) : (term141 _104592 p2 t) = (@IN _104592 p2 t).
Proof. exact (@lem4361969 (@IN _104592 p2 t)). Qed.
Lemma lem4361971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361972 {_104592 : Type'} (p2 : _104592) (t : _104592 -> Prop) : (term142 _104592 p2 t) = (term49 _104592 p2 t).
Proof. exact (MK_COMB (@lem4361971) (@lem4361970 _104592 p2 t)). Qed.
Lemma lem4361974 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361975 {_104592 : Type'} (p2 : _104592) (u : _104592 -> Prop) : (term141 _104592 p2 u) = (@IN _104592 p2 u).
Proof. exact (@lem4361974 (@IN _104592 p2 u)). Qed.
Lemma lem4361976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4361977 {_104592 : Type'} (p2 : _104592) (u : _104592 -> Prop) : (term143 _104592 p2 u) = (term144 _104592 p2 u).
Proof. exact (MK_COMB (@lem4361976) (@lem4361975 _104592 p2 u)). Qed.
Lemma lem4361978 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term133 _104592 t p2 u) = (term15 _104592 t p2 u).
Proof. exact (MK_COMB (@lem4361972 _104592 p2 t) (@lem4361977 _104592 p2 u)). Qed.
Lemma lem4361981 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)) = ((term15 _104592 t p2 u) = (term15 _104592 t p2 u)).
Proof. exact (MK_COMB (@lem4361965 _104592 t p2 u) (@lem4361978 _104592 t p2 u)). Qed.
Lemma lem4361983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4361984 (x : Prop) : (x = x) = True.
Proof. exact (@lem4361983 Prop x). Qed.
Lemma lem4361985 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term15 _104592 t p2 u) = (term15 _104592 t p2 u)) = True.
Proof. exact (@lem4361984 (term15 _104592 t p2 u)). Qed.
Lemma lem4361986 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)) = True.
Proof. exact (TRANS (@lem4361981 _104592 t p2 u) (@lem4361985 _104592 t p2 u)). Qed.
Lemma lem4361987 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : True = ((term132 _104592 t p2 u) = (term133 _104592 t p2 u)).
Proof. exact (SYM (@lem4361986 _104592 t p2 u)). Qed.
Lemma lem4361988 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term132 _104592 t p2 u) = (term133 _104592 t p2 u).
Proof. exact (EQ_MP (@lem4361987 _104592 t p2 u) (@lem0)). Qed.
Lemma lem4361992 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4361993 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term137 _104592 t p2 u) = False.
Proof. exact (@lem4361992 (term15 _104592 t p2 u)). Qed.
Lemma lem4361994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361995 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term145 _104592 t p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4361994) (@lem4361993 _104592 t p2 u)). Qed.
Lemma lem4361999 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362000 {_104592 : Type'} (p2 : _104592) (t : _104592 -> Prop) : (term146 _104592 p2 t) = False.
Proof. exact (@lem4361999 (@IN _104592 p2 t)). Qed.
Lemma lem4362001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362002 {_104592 : Type'} (p2 : _104592) (t : _104592 -> Prop) : (term147 _104592 p2 t) = (and False).
Proof. exact (MK_COMB (@lem4362001) (@lem4362000 _104592 p2 t)). Qed.
Lemma lem4362004 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362005 {_104592 : Type'} (p2 : _104592) (u : _104592 -> Prop) : (term146 _104592 p2 u) = False.
Proof. exact (@lem4362004 (@IN _104592 p2 u)). Qed.
Lemma lem4362006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4362007 {_104592 : Type'} (p2 : _104592) (u : _104592 -> Prop) : (term148 _104592 p2 u) = (~ False).
Proof. exact (MK_COMB (@lem4362006) (@lem4362005 _104592 p2 u)). Qed.
Lemma lem4362009 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362010 {_104592 : Type'} (p2 : _104592) (u : _104592 -> Prop) : (term148 _104592 p2 u) = True.
Proof. exact (TRANS (@lem4362007 _104592 p2 u) (@lem4362009)). Qed.
Lemma lem4362011 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term138 _104592 t p2 u) = (False /\ True).
Proof. exact (MK_COMB (@lem4362002 _104592 p2 t) (@lem4362010 _104592 p2 u)). Qed.
Lemma lem4362013 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362014 : (False /\ True) = False.
Proof. exact (@lem4362013 True). Qed.
Lemma lem4362015 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term138 _104592 t p2 u) = False.
Proof. exact (TRANS (@lem4362011 _104592 t p2 u) (@lem4362014)). Qed.
Lemma lem4362016 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4361995 _104592 t p2 u) (@lem4362015 _104592 t p2 u)). Qed.
Lemma lem4362018 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4362019 : (False = False) = (~ False).
Proof. exact (@lem4362018 False). Qed.
Lemma lem4362021 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362022 : (False = False) = True.
Proof. exact (TRANS (@lem4362019) (@lem4362021)). Qed.
Lemma lem4362023 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)) = True.
Proof. exact (TRANS (@lem4362016 _104592 t p2 u) (@lem4362022)). Qed.
Lemma lem4362024 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : True = ((term137 _104592 t p2 u) = (term138 _104592 t p2 u)).
Proof. exact (SYM (@lem4362023 _104592 t p2 u)). Qed.
Lemma lem4362025 {_104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term137 _104592 t p2 u) = (term138 _104592 t p2 u).
Proof. exact (EQ_MP (@lem4362024 _104592 t p2 u) (@lem0)). Qed.
Lemma lem4362026 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = False) : (term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4361956 _104591 _104592 t p2 u p1 s h1) (@lem4362025 _104592 t p2 u)). Qed.
Lemma lem4362027 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p2 : _104592) (u : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (h1 : (@IN _104591 p1 s) = True) : (term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4361943 _104591 _104592 t p2 u p1 s h1) (@lem4361988 _104592 t p2 u)). Qed.
Lemma lem4362030 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (p2 : _104592) (u : _104592 -> Prop) : (term50 _104591 _104592 p1 s t p2 u) = (term60 _104591 _104592 t p1 s p2 u).
Proof. exact (or_elim (@lem4361914 _104591 p1 s) (fun h0 : (@IN _104591 p1 s) = True => @lem4362027 _104591 _104592 t p2 u p1 s h0) (fun h0 : (@IN _104591 p1 s) = False => @lem4362026 _104591 _104592 t p2 u p1 s h0)). Qed.
Lemma lem4362045 {_104624 : Type'} (p1 : _104624) (s : _104624 -> Prop) : term127 _104624 p1 s.
Proof. exact (@lem9851 (@IN _104624 p1 s)). Qed.
Lemma lem4362046 {_104624 : Type'} (p1 : _104624) (s : _104624 -> Prop) : (term127 _104624 p1 s) = (term128 _104624 p1 s).
Proof. exact (eq_refl (term127 _104624 p1 s)). Qed.
Lemma lem4362047 {_104624 : Type'} (p1 : _104624) (s : _104624 -> Prop) : term128 _104624 p1 s.
Proof. exact (EQ_MP (@lem4362046 _104624 p1 s) (@lem4362045 _104624 p1 s)). Qed.
Lemma lem4362048 {_104624 : Type'} (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = True) : (@IN _104624 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4362049 {_104624 : Type'} (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = False) : (@IN _104624 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4362064 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term149 _104624 _104625 p1 t p2 u) = (term149 _104624 _104625 p1 t p2 u).
Proof. exact (eq_refl (term149 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362065 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = True) : (term150 _104624 _104625 t p2 u p1 s) = (term151 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362064 _104624 _104625 p1 t p2 u) (@lem4362048 _104624 p1 s h1)). Qed.
Lemma lem4362066 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term151 _104624 _104625 p1 t p2 u) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl (term151 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362067 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) : (term154 _104624 _104625 t p2 u p1 s) = (term154 _104624 _104625 t p2 u p1 s).
Proof. exact (eq_refl (term154 _104624 _104625 t p2 u p1 s)). Qed.
Lemma lem4362068 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = (term151 _104624 _104625 p1 t p2 u)) = ((term150 _104624 _104625 t p2 u p1 s) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4362067 _104624 _104625 t p2 u p1 s) (@lem4362066 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362069 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term150 _104624 _104625 t p2 u p1 s) = ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)).
Proof. exact (eq_refl (term150 _104624 _104625 t p2 u p1 s)). Qed.
Lemma lem4362070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362071 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term154 _104624 _104625 t p2 u p1 s) = (term155 _104624 _104625 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4362070) (@lem4362069 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4362072 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u))). Qed.
Lemma lem4362073 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u))) = (((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4362071 _104624 _104625 s p1 t p2 u) (@lem4362072 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362074 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = (term151 _104624 _104625 p1 t p2 u)) = (((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u))).
Proof. exact (TRANS (@lem4362068 _104624 _104625 s p1 t p2 u) (@lem4362073 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4362075 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = True) : ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4362074 _104624 _104625 s p1 t p2 u) (@lem4362065 _104624 _104625 t p2 u p1 s h1)). Qed.
Lemma lem4362076 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = True) : ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)) = ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)).
Proof. exact (SYM (@lem4362075 _104624 _104625 t p2 u p1 s h1)). Qed.
Lemma lem4362077 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term149 _104624 _104625 p1 t p2 u) = (term149 _104624 _104625 p1 t p2 u).
Proof. exact (eq_refl (term149 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362078 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = False) : (term150 _104624 _104625 t p2 u p1 s) = (term156 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362077 _104624 _104625 p1 t p2 u) (@lem4362049 _104624 p1 s h1)). Qed.
Lemma lem4362079 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term156 _104624 _104625 p1 t p2 u) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl (term156 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362080 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) : (term154 _104624 _104625 t p2 u p1 s) = (term154 _104624 _104625 t p2 u p1 s).
Proof. exact (eq_refl (term154 _104624 _104625 t p2 u p1 s)). Qed.
Lemma lem4362081 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = (term156 _104624 _104625 p1 t p2 u)) = ((term150 _104624 _104625 t p2 u p1 s) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4362080 _104624 _104625 t p2 u p1 s) (@lem4362079 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362082 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term150 _104624 _104625 t p2 u p1 s) = ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)).
Proof. exact (eq_refl (term150 _104624 _104625 t p2 u p1 s)). Qed.
Lemma lem4362083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362084 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term154 _104624 _104625 t p2 u p1 s) = (term155 _104624 _104625 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4362083) (@lem4362082 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4362085 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u))). Qed.
Lemma lem4362086 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u))) = (((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4362084 _104624 _104625 s p1 t p2 u) (@lem4362085 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362087 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term150 _104624 _104625 t p2 u p1 s) = (term156 _104624 _104625 p1 t p2 u)) = (((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u))).
Proof. exact (TRANS (@lem4362081 _104624 _104625 s p1 t p2 u) (@lem4362086 _104624 _104625 s p1 t p2 u)). Qed.
Lemma lem4362088 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = False) : ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)) = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4362087 _104624 _104625 s p1 t p2 u) (@lem4362078 _104624 _104625 t p2 u p1 s h1)). Qed.
Lemma lem4362089 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = False) : ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)) = ((term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u)).
Proof. exact (SYM (@lem4362088 _104624 _104625 t p2 u p1 s h1)). Qed.
Lemma lem4362095 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362096 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : (term159 _104624 p1 t) = (term144 _104624 p1 t).
Proof. exact (@lem4362095 (term144 _104624 p1 t)). Qed.
Lemma lem4362097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362098 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : (term160 _104624 p1 t) = (term161 _104624 p1 t).
Proof. exact (MK_COMB (@lem4362097) (@lem4362096 _104624 p1 t)). Qed.
Lemma lem4362099 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (@IN _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (eq_refl (@IN _104625 p2 u)). Qed.
Lemma lem4362100 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term152 _104624 _104625 p1 t p2 u) = (term162 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362098 _104624 p1 t) (@lem4362099 _104625 p2 u)). Qed.
Lemma lem4362103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362104 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term163 _104624 _104625 p1 t p2 u) = (term164 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362103) (@lem4362100 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362108 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362109 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term141 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (@lem4362108 (@IN _104625 p2 u)). Qed.
Lemma lem4362110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362111 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term142 _104625 p2 u) = (term49 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362110) (@lem4362109 _104625 p2 u)). Qed.
Lemma lem4362114 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term59 _104624 _104625 p1 t p2 u) = (term59 _104624 _104625 p1 t p2 u).
Proof. exact (eq_refl (term59 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362115 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term153 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362111 _104625 p2 u) (@lem4362114 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362118 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)) = ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)).
Proof. exact (MK_COMB (@lem4362104 _104624 _104625 p1 t p2 u) (@lem4362115 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362121 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u)).
Proof. exact (SYM (@lem4362118 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362122 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : term127 _104624 p1 t.
Proof. exact (@lem9851 (@IN _104624 p1 t)). Qed.
Lemma lem4362123 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : (term127 _104624 p1 t) = (term128 _104624 p1 t).
Proof. exact (eq_refl (term127 _104624 p1 t)). Qed.
Lemma lem4362124 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : term128 _104624 p1 t.
Proof. exact (EQ_MP (@lem4362123 _104624 p1 t) (@lem4362122 _104624 p1 t)). Qed.
Lemma lem4362125 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = True) : (@IN _104624 p1 t) = True.
Proof. exact (h1). Qed.
Lemma lem4362126 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = False) : (@IN _104624 p1 t) = False.
Proof. exact (h1). Qed.
Lemma lem4362137 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term166 _104625 p2 u) = (term166 _104625 p2 u).
Proof. exact (eq_refl (term166 _104625 p2 u)). Qed.
Lemma lem4362138 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = True) : (term167 _104624 _104625 p2 u p1 t) = (term168 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362137 _104625 p2 u) (@lem4362125 _104624 p1 t h1)). Qed.
Lemma lem4362139 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term168 _104625 p2 u) = ((term169 _104625 p2 u) = (term170 _104625 p2 u)).
Proof. exact (eq_refl (term168 _104625 p2 u)). Qed.
Lemma lem4362140 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) : (term171 _104624 _104625 p2 u p1 t) = (term171 _104624 _104625 p2 u p1 t).
Proof. exact (eq_refl (term171 _104624 _104625 p2 u p1 t)). Qed.
Lemma lem4362141 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = (term168 _104625 p2 u)) = ((term167 _104624 _104625 p2 u p1 t) = ((term169 _104625 p2 u) = (term170 _104625 p2 u))).
Proof. exact (MK_COMB (@lem4362140 _104624 _104625 p2 u p1 t) (@lem4362139 _104625 p2 u)). Qed.
Lemma lem4362142 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term167 _104624 _104625 p2 u p1 t) = ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl (term167 _104624 _104625 p2 u p1 t)). Qed.
Lemma lem4362143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362144 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term171 _104624 _104625 p2 u p1 t) = (term172 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362143) (@lem4362142 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362145 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term169 _104625 p2 u) = (term170 _104625 p2 u)) = ((term169 _104625 p2 u) = (term170 _104625 p2 u)).
Proof. exact (eq_refl ((term169 _104625 p2 u) = (term170 _104625 p2 u))). Qed.
Lemma lem4362146 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = ((term169 _104625 p2 u) = (term170 _104625 p2 u))) = (((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term169 _104625 p2 u) = (term170 _104625 p2 u))).
Proof. exact (MK_COMB (@lem4362144 _104624 _104625 p1 t p2 u) (@lem4362145 _104625 p2 u)). Qed.
Lemma lem4362147 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = (term168 _104625 p2 u)) = (((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term169 _104625 p2 u) = (term170 _104625 p2 u))).
Proof. exact (TRANS (@lem4362141 _104624 _104625 p1 t p2 u) (@lem4362146 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362148 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = True) : ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term169 _104625 p2 u) = (term170 _104625 p2 u)).
Proof. exact (EQ_MP (@lem4362147 _104624 _104625 p1 t p2 u) (@lem4362138 _104624 _104625 p2 u p1 t h1)). Qed.
Lemma lem4362149 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = True) : ((term169 _104625 p2 u) = (term170 _104625 p2 u)) = ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)).
Proof. exact (SYM (@lem4362148 _104624 _104625 p2 u p1 t h1)). Qed.
Lemma lem4362150 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term166 _104625 p2 u) = (term166 _104625 p2 u).
Proof. exact (eq_refl (term166 _104625 p2 u)). Qed.
Lemma lem4362151 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = False) : (term167 _104624 _104625 p2 u p1 t) = (term173 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362150 _104625 p2 u) (@lem4362126 _104624 p1 t h1)). Qed.
Lemma lem4362152 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term173 _104625 p2 u) = ((term174 _104625 p2 u) = (term175 _104625 p2 u)).
Proof. exact (eq_refl (term173 _104625 p2 u)). Qed.
Lemma lem4362153 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) : (term171 _104624 _104625 p2 u p1 t) = (term171 _104624 _104625 p2 u p1 t).
Proof. exact (eq_refl (term171 _104624 _104625 p2 u p1 t)). Qed.
Lemma lem4362154 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = (term173 _104625 p2 u)) = ((term167 _104624 _104625 p2 u p1 t) = ((term174 _104625 p2 u) = (term175 _104625 p2 u))).
Proof. exact (MK_COMB (@lem4362153 _104624 _104625 p2 u p1 t) (@lem4362152 _104625 p2 u)). Qed.
Lemma lem4362155 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term167 _104624 _104625 p2 u p1 t) = ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)).
Proof. exact (eq_refl (term167 _104624 _104625 p2 u p1 t)). Qed.
Lemma lem4362156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362157 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term171 _104624 _104625 p2 u p1 t) = (term172 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362156) (@lem4362155 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362158 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term174 _104625 p2 u) = (term175 _104625 p2 u)) = ((term174 _104625 p2 u) = (term175 _104625 p2 u)).
Proof. exact (eq_refl ((term174 _104625 p2 u) = (term175 _104625 p2 u))). Qed.
Lemma lem4362159 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = ((term174 _104625 p2 u) = (term175 _104625 p2 u))) = (((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term174 _104625 p2 u) = (term175 _104625 p2 u))).
Proof. exact (MK_COMB (@lem4362157 _104624 _104625 p1 t p2 u) (@lem4362158 _104625 p2 u)). Qed.
Lemma lem4362160 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term167 _104624 _104625 p2 u p1 t) = (term173 _104625 p2 u)) = (((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term174 _104625 p2 u) = (term175 _104625 p2 u))).
Proof. exact (TRANS (@lem4362154 _104624 _104625 p1 t p2 u) (@lem4362159 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362161 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = False) : ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)) = ((term174 _104625 p2 u) = (term175 _104625 p2 u)).
Proof. exact (EQ_MP (@lem4362160 _104624 _104625 p1 t p2 u) (@lem4362151 _104624 _104625 p2 u p1 t h1)). Qed.
Lemma lem4362162 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = False) : ((term174 _104625 p2 u) = (term175 _104625 p2 u)) = ((term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u)).
Proof. exact (SYM (@lem4362161 _104624 _104625 p2 u p1 t h1)). Qed.
Lemma lem4362168 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4362169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362170 : term176 = (and False).
Proof. exact (MK_COMB (@lem4362169) (@lem4362168)). Qed.
Lemma lem4362171 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (@IN _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (eq_refl (@IN _104625 p2 u)). Qed.
Lemma lem4362172 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term169 _104625 p2 u) = (term146 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362170) (@lem4362171 _104625 p2 u)). Qed.
Lemma lem4362174 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362175 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term146 _104625 p2 u) = False.
Proof. exact (@lem4362174 (@IN _104625 p2 u)). Qed.
Lemma lem4362176 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term169 _104625 p2 u) = False.
Proof. exact (TRANS (@lem4362172 _104625 p2 u) (@lem4362175 _104625 p2 u)). Qed.
Lemma lem4362177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362178 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term177 _104625 p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4362177) (@lem4362176 _104625 p2 u)). Qed.
Lemma lem4362182 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362183 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term141 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (@lem4362182 (@IN _104625 p2 u)). Qed.
Lemma lem4362184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4362185 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term143 _104625 p2 u) = (term144 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362184) (@lem4362183 _104625 p2 u)). Qed.
Lemma lem4362186 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term49 _104625 p2 u) = (term49 _104625 p2 u).
Proof. exact (eq_refl (term49 _104625 p2 u)). Qed.
Lemma lem4362187 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term170 _104625 p2 u) = (term178 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362186 _104625 p2 u) (@lem4362185 _104625 p2 u)). Qed.
Lemma lem4362190 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term169 _104625 p2 u) = (term170 _104625 p2 u)) = (False = (term178 _104625 p2 u)).
Proof. exact (MK_COMB (@lem4362178 _104625 p2 u) (@lem4362187 _104625 p2 u)). Qed.
Lemma lem4362192 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4362193 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (False = (term178 _104625 p2 u)) = (term179 _104625 p2 u).
Proof. exact (@lem4362192 (term178 _104625 p2 u)). Qed.
Lemma lem4362196 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term169 _104625 p2 u) = (term170 _104625 p2 u)) = (term179 _104625 p2 u).
Proof. exact (TRANS (@lem4362190 _104625 p2 u) (@lem4362193 _104625 p2 u)). Qed.
Lemma lem4362197 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term179 _104625 p2 u) = ((term169 _104625 p2 u) = (term170 _104625 p2 u)).
Proof. exact (SYM (@lem4362196 _104625 p2 u)). Qed.
Lemma lem4362198 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : term127 _104625 p2 u.
Proof. exact (@lem9851 (@IN _104625 p2 u)). Qed.
Lemma lem4362199 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term127 _104625 p2 u) = (term128 _104625 p2 u).
Proof. exact (eq_refl (term127 _104625 p2 u)). Qed.
Lemma lem4362200 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : term128 _104625 p2 u.
Proof. exact (EQ_MP (@lem4362199 _104625 p2 u) (@lem4362198 _104625 p2 u)). Qed.
Lemma lem4362201 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = True) : (@IN _104625 p2 u) = True.
Proof. exact (h1). Qed.
Lemma lem4362202 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = False) : (@IN _104625 p2 u) = False.
Proof. exact (h1). Qed.
Lemma lem4362207 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4362208 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = True) : (term181 _104625 p2 u) = term182.
Proof. exact (MK_COMB (@lem4362207) (@lem4362201 _104625 p2 u h1)). Qed.
Lemma lem4362209 : term182 = term183.
Proof. exact (eq_refl term182). Qed.
Lemma lem4362210 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term184 _104625 p2 u) = (term184 _104625 p2 u).
Proof. exact (eq_refl (term184 _104625 p2 u)). Qed.
Lemma lem4362211 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term182) = ((term181 _104625 p2 u) = term183).
Proof. exact (MK_COMB (@lem4362210 _104625 p2 u) (@lem4362209)). Qed.
Lemma lem4362212 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term181 _104625 p2 u) = (term179 _104625 p2 u).
Proof. exact (eq_refl (term181 _104625 p2 u)). Qed.
Lemma lem4362213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362214 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term184 _104625 p2 u) = (term185 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362213) (@lem4362212 _104625 p2 u)). Qed.
Lemma lem4362215 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem4362216 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term183) = ((term179 _104625 p2 u) = term183).
Proof. exact (MK_COMB (@lem4362214 _104625 p2 u) (@lem4362215)). Qed.
Lemma lem4362217 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term182) = ((term179 _104625 p2 u) = term183).
Proof. exact (TRANS (@lem4362211 _104625 p2 u) (@lem4362216 _104625 p2 u)). Qed.
Lemma lem4362218 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = True) : (term179 _104625 p2 u) = term183.
Proof. exact (EQ_MP (@lem4362217 _104625 p2 u) (@lem4362208 _104625 p2 u h1)). Qed.
Lemma lem4362219 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = True) : term183 = (term179 _104625 p2 u).
Proof. exact (SYM (@lem4362218 _104625 p2 u h1)). Qed.
Lemma lem4362220 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4362221 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = False) : (term181 _104625 p2 u) = term186.
Proof. exact (MK_COMB (@lem4362220) (@lem4362202 _104625 p2 u h1)). Qed.
Lemma lem4362222 : term186 = term187.
Proof. exact (eq_refl term186). Qed.
Lemma lem4362223 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term184 _104625 p2 u) = (term184 _104625 p2 u).
Proof. exact (eq_refl (term184 _104625 p2 u)). Qed.
Lemma lem4362224 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term186) = ((term181 _104625 p2 u) = term187).
Proof. exact (MK_COMB (@lem4362223 _104625 p2 u) (@lem4362222)). Qed.
Lemma lem4362225 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term181 _104625 p2 u) = (term179 _104625 p2 u).
Proof. exact (eq_refl (term181 _104625 p2 u)). Qed.
Lemma lem4362226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362227 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term184 _104625 p2 u) = (term185 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362226) (@lem4362225 _104625 p2 u)). Qed.
Lemma lem4362228 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem4362229 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term187) = ((term179 _104625 p2 u) = term187).
Proof. exact (MK_COMB (@lem4362227 _104625 p2 u) (@lem4362228)). Qed.
Lemma lem4362230 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term181 _104625 p2 u) = term186) = ((term179 _104625 p2 u) = term187).
Proof. exact (TRANS (@lem4362224 _104625 p2 u) (@lem4362229 _104625 p2 u)). Qed.
Lemma lem4362231 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = False) : (term179 _104625 p2 u) = term187.
Proof. exact (EQ_MP (@lem4362230 _104625 p2 u) (@lem4362221 _104625 p2 u h1)). Qed.
Lemma lem4362232 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = False) : term187 = (term179 _104625 p2 u).
Proof. exact (SYM (@lem4362231 _104625 p2 u h1)). Qed.
Lemma lem4362234 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362235 : term188 = (~ True).
Proof. exact (@lem4362234 (~ True)). Qed.
Lemma lem4362237 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4362238 : term188 = False.
Proof. exact (TRANS (@lem4362235) (@lem4362237)). Qed.
Lemma lem4362239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4362240 : term183 = (~ False).
Proof. exact (MK_COMB (@lem4362239) (@lem4362238)). Qed.
Lemma lem4362242 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362243 : term183 = True.
Proof. exact (TRANS (@lem4362240) (@lem4362242)). Qed.
Lemma lem4362244 : True = term183.
Proof. exact (SYM (@lem4362243)). Qed.
Lemma lem4362245 : term183.
Proof. exact (EQ_MP (@lem4362244) (@lem0)). Qed.
Lemma lem4362247 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362248 : term189 = False.
Proof. exact (@lem4362247 (~ False)). Qed.
Lemma lem4362249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4362250 : term187 = (~ False).
Proof. exact (MK_COMB (@lem4362249) (@lem4362248)). Qed.
Lemma lem4362252 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362253 : term187 = True.
Proof. exact (TRANS (@lem4362250) (@lem4362252)). Qed.
Lemma lem4362254 : True = term187.
Proof. exact (SYM (@lem4362253)). Qed.
Lemma lem4362255 : term187.
Proof. exact (EQ_MP (@lem4362254) (@lem0)). Qed.
Lemma lem4362256 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = False) : term179 _104625 p2 u.
Proof. exact (EQ_MP (@lem4362232 _104625 p2 u h1) (@lem4362255)). Qed.
Lemma lem4362257 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (h1 : (@IN _104625 p2 u) = True) : term179 _104625 p2 u.
Proof. exact (EQ_MP (@lem4362219 _104625 p2 u h1) (@lem4362245)). Qed.
Lemma lem4362259 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : term179 _104625 p2 u.
Proof. exact (or_elim (@lem4362200 _104625 p2 u) (fun h0 : (@IN _104625 p2 u) = True => @lem4362257 _104625 p2 u h0) (fun h0 : (@IN _104625 p2 u) = False => @lem4362256 _104625 p2 u h0)). Qed.
Lemma lem4362260 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term169 _104625 p2 u) = (term170 _104625 p2 u).
Proof. exact (EQ_MP (@lem4362197 _104625 p2 u) (@lem4362259 _104625 p2 u)). Qed.
Lemma lem4362266 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362268 : term190 = (and True).
Proof. exact (MK_COMB (@lem4362267) (@lem4362266)). Qed.
Lemma lem4362269 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (@IN _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (eq_refl (@IN _104625 p2 u)). Qed.
Lemma lem4362270 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term174 _104625 p2 u) = (term141 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362268) (@lem4362269 _104625 p2 u)). Qed.
Lemma lem4362272 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362273 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term141 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (@lem4362272 (@IN _104625 p2 u)). Qed.
Lemma lem4362274 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term174 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (TRANS (@lem4362270 _104625 p2 u) (@lem4362273 _104625 p2 u)). Qed.
Lemma lem4362275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362276 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term191 _104625 p2 u) = (term192 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362275) (@lem4362274 _104625 p2 u)). Qed.
Lemma lem4362280 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362281 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term146 _104625 p2 u) = False.
Proof. exact (@lem4362280 (@IN _104625 p2 u)). Qed.
Lemma lem4362282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4362283 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term148 _104625 p2 u) = (~ False).
Proof. exact (MK_COMB (@lem4362282) (@lem4362281 _104625 p2 u)). Qed.
Lemma lem4362285 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362286 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term148 _104625 p2 u) = True.
Proof. exact (TRANS (@lem4362283 _104625 p2 u) (@lem4362285)). Qed.
Lemma lem4362287 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term49 _104625 p2 u) = (term49 _104625 p2 u).
Proof. exact (eq_refl (term49 _104625 p2 u)). Qed.
Lemma lem4362288 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term175 _104625 p2 u) = (term193 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362287 _104625 p2 u) (@lem4362286 _104625 p2 u)). Qed.
Lemma lem4362290 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4362291 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term193 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (@lem4362290 (@IN _104625 p2 u)). Qed.
Lemma lem4362292 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term175 _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (TRANS (@lem4362288 _104625 p2 u) (@lem4362291 _104625 p2 u)). Qed.
Lemma lem4362293 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term174 _104625 p2 u) = (term175 _104625 p2 u)) = ((@IN _104625 p2 u) = (@IN _104625 p2 u)).
Proof. exact (MK_COMB (@lem4362276 _104625 p2 u) (@lem4362292 _104625 p2 u)). Qed.
Lemma lem4362295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4362296 (x : Prop) : (x = x) = True.
Proof. exact (@lem4362295 Prop x). Qed.
Lemma lem4362297 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((@IN _104625 p2 u) = (@IN _104625 p2 u)) = True.
Proof. exact (@lem4362296 (@IN _104625 p2 u)). Qed.
Lemma lem4362298 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : ((term174 _104625 p2 u) = (term175 _104625 p2 u)) = True.
Proof. exact (TRANS (@lem4362293 _104625 p2 u) (@lem4362297 _104625 p2 u)). Qed.
Lemma lem4362299 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : True = ((term174 _104625 p2 u) = (term175 _104625 p2 u)).
Proof. exact (SYM (@lem4362298 _104625 p2 u)). Qed.
Lemma lem4362300 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term174 _104625 p2 u) = (term175 _104625 p2 u).
Proof. exact (EQ_MP (@lem4362299 _104625 p2 u) (@lem0)). Qed.
Lemma lem4362301 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = False) : (term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u).
Proof. exact (EQ_MP (@lem4362162 _104624 _104625 p2 u p1 t h1) (@lem4362300 _104625 p2 u)). Qed.
Lemma lem4362302 {_104624 _104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (h1 : (@IN _104624 p1 t) = True) : (term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u).
Proof. exact (EQ_MP (@lem4362149 _104624 _104625 p2 u p1 t h1) (@lem4362260 _104625 p2 u)). Qed.
Lemma lem4362304 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term162 _104624 _104625 p1 t p2 u) = (term165 _104624 _104625 p1 t p2 u).
Proof. exact (or_elim (@lem4362124 _104624 p1 t) (fun h0 : (@IN _104624 p1 t) = True => @lem4362302 _104624 _104625 p2 u p1 t h0) (fun h0 : (@IN _104624 p1 t) = False => @lem4362301 _104624 _104625 p2 u p1 t h0)). Qed.
Lemma lem4362305 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term152 _104624 _104625 p1 t p2 u) = (term153 _104624 _104625 p1 t p2 u).
Proof. exact (EQ_MP (@lem4362121 _104624 _104625 p1 t p2 u) (@lem4362304 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362311 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362312 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : (term194 _104624 p1 t) = False.
Proof. exact (@lem4362311 (term144 _104624 p1 t)). Qed.
Lemma lem4362313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362314 {_104624 : Type'} (p1 : _104624) (t : _104624 -> Prop) : (term195 _104624 p1 t) = (and False).
Proof. exact (MK_COMB (@lem4362313) (@lem4362312 _104624 p1 t)). Qed.
Lemma lem4362315 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (@IN _104625 p2 u) = (@IN _104625 p2 u).
Proof. exact (eq_refl (@IN _104625 p2 u)). Qed.
Lemma lem4362316 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term157 _104624 _104625 p1 t p2 u) = (term146 _104625 p2 u).
Proof. exact (MK_COMB (@lem4362314 _104624 p1 t) (@lem4362315 _104625 p2 u)). Qed.
Lemma lem4362318 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362319 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term146 _104625 p2 u) = False.
Proof. exact (@lem4362318 (@IN _104625 p2 u)). Qed.
Lemma lem4362320 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term157 _104624 _104625 p1 t p2 u) = False.
Proof. exact (TRANS (@lem4362316 _104624 _104625 p1 t p2 u) (@lem4362319 _104625 p2 u)). Qed.
Lemma lem4362321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362322 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term196 _104624 _104625 p1 t p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4362321) (@lem4362320 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362326 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362327 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term146 _104625 p2 u) = False.
Proof. exact (@lem4362326 (@IN _104625 p2 u)). Qed.
Lemma lem4362328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362329 {_104625 : Type'} (p2 : _104625) (u : _104625 -> Prop) : (term147 _104625 p2 u) = (and False).
Proof. exact (MK_COMB (@lem4362328) (@lem4362327 _104625 p2 u)). Qed.
Lemma lem4362332 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term59 _104624 _104625 p1 t p2 u) = (term59 _104624 _104625 p1 t p2 u).
Proof. exact (eq_refl (term59 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362333 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term158 _104624 _104625 p1 t p2 u) = (term197 _104624 _104625 p1 t p2 u).
Proof. exact (MK_COMB (@lem4362329 _104625 p2 u) (@lem4362332 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362335 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362336 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term197 _104624 _104625 p1 t p2 u) = False.
Proof. exact (@lem4362335 (term59 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362337 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term158 _104624 _104625 p1 t p2 u) = False.
Proof. exact (TRANS (@lem4362333 _104624 _104625 p1 t p2 u) (@lem4362336 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362338 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4362322 _104624 _104625 p1 t p2 u) (@lem4362337 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362340 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4362341 : (False = False) = (~ False).
Proof. exact (@lem4362340 False). Qed.
Lemma lem4362343 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362344 : (False = False) = True.
Proof. exact (TRANS (@lem4362341) (@lem4362343)). Qed.
Lemma lem4362345 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)) = True.
Proof. exact (TRANS (@lem4362338 _104624 _104625 p1 t p2 u) (@lem4362344)). Qed.
Lemma lem4362346 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : True = ((term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u)).
Proof. exact (SYM (@lem4362345 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362347 {_104624 _104625 : Type'} (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term157 _104624 _104625 p1 t p2 u) = (term158 _104624 _104625 p1 t p2 u).
Proof. exact (EQ_MP (@lem4362346 _104624 _104625 p1 t p2 u) (@lem0)). Qed.
Lemma lem4362348 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = False) : (term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4362089 _104624 _104625 t p2 u p1 s h1) (@lem4362347 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362349 {_104624 _104625 : Type'} (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) (p1 : _104624) (s : _104624 -> Prop) (h1 : (@IN _104624 p1 s) = True) : (term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4362076 _104624 _104625 t p2 u p1 s h1) (@lem4362305 _104624 _104625 p1 t p2 u)). Qed.
Lemma lem4362352 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (p2 : _104625) (u : _104625 -> Prop) : (term104 _104624 _104625 s p1 t p2 u) = (term108 _104624 _104625 s p1 t p2 u).
Proof. exact (or_elim (@lem4362047 _104624 p1 s) (fun h0 : (@IN _104624 p1 s) = True => @lem4362349 _104624 _104625 t p2 u p1 s h0) (fun h0 : (@IN _104624 p1 s) = False => @lem4362348 _104624 _104625 t p2 u p1 s h0)). Qed.
Lemma lem4362357 {_104624 _104625 : Type'} (s : _104624 -> Prop) (p1 : _104624) (t : _104624 -> Prop) (u : _104625 -> Prop) : term110 _104624 _104625 s p1 t u.
Proof. exact (fun p2 : _104625 => @lem4362352 _104624 _104625 s p1 t p2 u). Qed.
Lemma lem4362362 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) (u : _104625 -> Prop) : term112 _104624 _104625 s t u.
Proof. exact (fun p1 : _104624 => @lem4362357 _104624 _104625 s p1 t u). Qed.
Lemma lem4362367 {_104624 _104625 : Type'} (s : _104624 -> Prop) (t : _104624 -> Prop) : term116 _104624 _104625 s t.
Proof. exact (fun u : _104625 -> Prop => @lem4362362 _104624 _104625 s t u). Qed.
Lemma lem4362372 {_104624 _104625 : Type'} (s : _104624 -> Prop) : term120 _104624 _104625 s.
Proof. exact (fun t : _104624 -> Prop => @lem4362367 _104624 _104625 s t). Qed.
Lemma lem4362377 {_104624 _104625 : Type'} : term124 _104624 _104625.
Proof. exact (fun s : _104624 -> Prop => @lem4362372 _104624 _104625 s). Qed.
Lemma lem4362382 {_104591 _104592 : Type'} (t : _104592 -> Prop) (p1 : _104591) (s : _104591 -> Prop) (u : _104592 -> Prop) : term62 _104591 _104592 t p1 s u.
Proof. exact (fun p2 : _104592 => @lem4362030 _104591 _104592 t p1 s p2 u). Qed.
Lemma lem4362387 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) (u : _104592 -> Prop) : term64 _104591 _104592 t s u.
Proof. exact (fun p1 : _104591 => @lem4362382 _104591 _104592 t p1 s u). Qed.
Lemma lem4362392 {_104591 _104592 : Type'} (t : _104592 -> Prop) (s : _104591 -> Prop) : term68 _104591 _104592 t s.
Proof. exact (fun u : _104592 -> Prop => @lem4362387 _104591 _104592 t s u). Qed.
Lemma lem4362397 {_104591 _104592 : Type'} (s : _104591 -> Prop) : term72 _104591 _104592 s.
Proof. exact (fun t : _104592 -> Prop => @lem4362392 _104591 _104592 t s). Qed.
Lemma lem4362402 {_104591 _104592 : Type'} : term76 _104591 _104592.
Proof. exact (fun s : _104591 -> Prop => @lem4362397 _104591 _104592 s). Qed.
Lemma lem4362403 {_104591 _104592 _104624 _104625 : Type'} : term126 _104591 _104592 _104624 _104625.
Proof. exact (conj (@lem4362402 _104591 _104592) (@lem4362377 _104624 _104625)). Qed.
Lemma lem4362404 {_104591 _104592 _104624 _104625 : Type'} : term125 _104591 _104592 _104624 _104625.
Proof. exact (EQ_MP (@lem4361897 _104591 _104592 _104624 _104625) (@lem4362403 _104591 _104592 _104624 _104625)). Qed.
