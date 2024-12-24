Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299672_term_abbrevs.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem2299583 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem2299584 (_474 : int) (_475 : Prop) (b : Prop) (x : int) (y : int) (_477 : int) : (term2 b x y _475 _474 _477) = (term3 _474 _475 b x y _477).
Proof. exact (@lem2299583 _474 _475 (term4 b x y) _477). Qed.
Lemma lem2299585 (b : Prop) (x : int) (y : int) : (term5 b x y) = (term6 b x y).
Proof. exact (@lem2299584 x b b x y y). Qed.
Lemma lem2299586 (b : Prop) (x : int) (y : int) : (term7 b x y) = ((real_of_int y) = (term8 b x y)).
Proof. exact (eq_refl (term7 b x y)). Qed.
Lemma lem2299587 (b : Prop) : (term9 b) = (term9 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem2299588 (b : Prop) (x : int) (y : int) : (term10 b x y) = (term11 b x y).
Proof. exact (MK_COMB (@lem2299587 b) (@lem2299586 b x y)). Qed.
Lemma lem2299589 (b : Prop) (x : int) (y : int) : (term12 b y x) = ((real_of_int x) = (term8 b x y)).
Proof. exact (eq_refl (term12 b y x)). Qed.
Lemma lem2299590 (b : Prop) : (imp b) = (imp b).
Proof. exact (eq_refl (imp b)). Qed.
Lemma lem2299591 (b : Prop) (x : int) (y : int) : (term13 b y x) = (term14 b x y).
Proof. exact (MK_COMB (@lem2299590 b) (@lem2299589 b x y)). Qed.
Lemma lem2299592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2299593 (b : Prop) (x : int) (y : int) : (term15 b y x) = (term16 b x y).
Proof. exact (MK_COMB (@lem2299592) (@lem2299591 b x y)). Qed.
Lemma lem2299594 (b : Prop) (x : int) (y : int) : (term6 b x y) = (term17 b x y).
Proof. exact (MK_COMB (@lem2299593 b x y) (@lem2299588 b x y)). Qed.
Lemma lem2299595 (b : Prop) (x : int) (y : int) : (term5 b x y) = ((term18 b x y) = (term8 b x y)).
Proof. exact (eq_refl (term5 b x y)). Qed.
Lemma lem2299596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2299597 (b : Prop) (x : int) (y : int) : (term19 b x y) = (term20 b x y).
Proof. exact (MK_COMB (@lem2299596) (@lem2299595 b x y)). Qed.
Lemma lem2299598 (b : Prop) (x : int) (y : int) : ((term5 b x y) = (term6 b x y)) = (((term18 b x y) = (term8 b x y)) = (term17 b x y)).
Proof. exact (MK_COMB (@lem2299597 b x y) (@lem2299594 b x y)). Qed.
Lemma lem2299599 (b : Prop) (x : int) (y : int) : ((term18 b x y) = (term8 b x y)) = (term17 b x y).
Proof. exact (EQ_MP (@lem2299598 b x y) (@lem2299585 b x y)). Qed.
Lemma lem2299600 (b : Prop) (x : int) (y : int) : (term17 b x y) = ((term18 b x y) = (term8 b x y)).
Proof. exact (SYM (@lem2299599 b x y)). Qed.
Lemma lem2299601 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem2299602 (b : Prop) : b = (b = True).
Proof. exact (@lem7 b). Qed.
Lemma lem2299603 (b : Prop) (h1 : b) : b = True.
Proof. exact (EQ_MP (@lem2299602 b) (@lem2299601 b h1)). Qed.
Lemma lem2299604 (x : int) (y : int) : (term21 x y) = (term21 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem2299605 (x : int) (y : int) (b : Prop) (h1 : b) : (term22 x y b) = (term23 x y).
Proof. exact (MK_COMB (@lem2299604 x y) (@lem2299603 b h1)). Qed.
Lemma lem2299606 (x : int) (y : int) : (term23 x y) = ((real_of_int x) = (term24 x y)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem2299607 (x : int) (y : int) (b : Prop) : (term25 x y b) = (term25 x y b).
Proof. exact (eq_refl (term25 x y b)). Qed.
Lemma lem2299608 (b : Prop) (x : int) (y : int) : ((term22 x y b) = (term23 x y)) = ((term22 x y b) = ((real_of_int x) = (term24 x y))).
Proof. exact (MK_COMB (@lem2299607 x y b) (@lem2299606 x y)). Qed.
Lemma lem2299609 (b : Prop) (x : int) (y : int) : (term22 x y b) = ((real_of_int x) = (term8 b x y)).
Proof. exact (eq_refl (term22 x y b)). Qed.
Lemma lem2299610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2299611 (b : Prop) (x : int) (y : int) : (term25 x y b) = (term26 b x y).
Proof. exact (MK_COMB (@lem2299610) (@lem2299609 b x y)). Qed.
Lemma lem2299612 (x : int) (y : int) : ((real_of_int x) = (term24 x y)) = ((real_of_int x) = (term24 x y)).
Proof. exact (eq_refl ((real_of_int x) = (term24 x y))). Qed.
Lemma lem2299613 (b : Prop) (x : int) (y : int) : ((term22 x y b) = ((real_of_int x) = (term24 x y))) = (((real_of_int x) = (term8 b x y)) = ((real_of_int x) = (term24 x y))).
Proof. exact (MK_COMB (@lem2299611 b x y) (@lem2299612 x y)). Qed.
Lemma lem2299614 (b : Prop) (x : int) (y : int) : ((term22 x y b) = (term23 x y)) = (((real_of_int x) = (term8 b x y)) = ((real_of_int x) = (term24 x y))).
Proof. exact (TRANS (@lem2299608 b x y) (@lem2299613 b x y)). Qed.
Lemma lem2299615 (x : int) (y : int) (b : Prop) (h1 : b) : ((real_of_int x) = (term8 b x y)) = ((real_of_int x) = (term24 x y)).
Proof. exact (EQ_MP (@lem2299614 b x y) (@lem2299605 x y b h1)). Qed.
Lemma lem2299616 (x : int) (y : int) (b : Prop) (h1 : b) : ((real_of_int x) = (term24 x y)) = ((real_of_int x) = (term8 b x y)).
Proof. exact (SYM (@lem2299615 x y b h1)). Qed.
Lemma lem2299617 (b : Prop) (h1 : ~ b) : ~ b.
Proof. exact (h1). Qed.
Lemma lem2299618 (b : Prop) : term27 b.
Proof. exact (@lem82 b). Qed.
Lemma lem2299619 (b : Prop) (h1 : ~ b) : b = False.
Proof. exact (@lem2299618 b (@lem2299617 b h1)). Qed.
Lemma lem2299620 (x : int) (y : int) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem2299621 (x : int) (y : int) (b : Prop) (h1 : ~ b) : (term29 x y b) = (term30 x y).
Proof. exact (MK_COMB (@lem2299620 x y) (@lem2299619 b h1)). Qed.
Lemma lem2299622 (x : int) (y : int) : (term30 x y) = ((real_of_int y) = (term31 x y)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem2299623 (x : int) (y : int) (b : Prop) : (term32 x y b) = (term32 x y b).
Proof. exact (eq_refl (term32 x y b)). Qed.
Lemma lem2299624 (b : Prop) (x : int) (y : int) : ((term29 x y b) = (term30 x y)) = ((term29 x y b) = ((real_of_int y) = (term31 x y))).
Proof. exact (MK_COMB (@lem2299623 x y b) (@lem2299622 x y)). Qed.
Lemma lem2299625 (b : Prop) (x : int) (y : int) : (term29 x y b) = ((real_of_int y) = (term8 b x y)).
Proof. exact (eq_refl (term29 x y b)). Qed.
Lemma lem2299626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2299627 (b : Prop) (x : int) (y : int) : (term32 x y b) = (term33 b x y).
Proof. exact (MK_COMB (@lem2299626) (@lem2299625 b x y)). Qed.
Lemma lem2299628 (x : int) (y : int) : ((real_of_int y) = (term31 x y)) = ((real_of_int y) = (term31 x y)).
Proof. exact (eq_refl ((real_of_int y) = (term31 x y))). Qed.
Lemma lem2299629 (b : Prop) (x : int) (y : int) : ((term29 x y b) = ((real_of_int y) = (term31 x y))) = (((real_of_int y) = (term8 b x y)) = ((real_of_int y) = (term31 x y))).
Proof. exact (MK_COMB (@lem2299627 b x y) (@lem2299628 x y)). Qed.
Lemma lem2299630 (b : Prop) (x : int) (y : int) : ((term29 x y b) = (term30 x y)) = (((real_of_int y) = (term8 b x y)) = ((real_of_int y) = (term31 x y))).
Proof. exact (TRANS (@lem2299624 b x y) (@lem2299629 b x y)). Qed.
Lemma lem2299631 (x : int) (y : int) (b : Prop) (h1 : ~ b) : ((real_of_int y) = (term8 b x y)) = ((real_of_int y) = (term31 x y)).
Proof. exact (EQ_MP (@lem2299630 b x y) (@lem2299621 x y b h1)). Qed.
Lemma lem2299632 (x : int) (y : int) (b : Prop) (h1 : ~ b) : ((real_of_int y) = (term31 x y)) = ((real_of_int y) = (term8 b x y)).
Proof. exact (SYM (@lem2299631 x y b h1)). Qed.
Lemma lem2299636 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2299637 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem2299636 real t2 t1). Qed.
Lemma lem2299638 (y : int) (x : int) : (term24 x y) = (real_of_int x).
Proof. exact (@lem2299637 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2299639 (x : int) : (term34 x) = (term34 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem2299640 (y : int) (x : int) : ((real_of_int x) = (term24 x y)) = ((real_of_int x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2299639 x) (@lem2299638 y x)). Qed.
Lemma lem2299642 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2299643 (x : real) : (x = x) = True.
Proof. exact (@lem2299642 real x). Qed.
Lemma lem2299644 (x : int) : ((real_of_int x) = (real_of_int x)) = True.
Proof. exact (@lem2299643 (real_of_int x)). Qed.
Lemma lem2299645 (x : int) (y : int) : ((real_of_int x) = (term24 x y)) = True.
Proof. exact (TRANS (@lem2299640 y x) (@lem2299644 x)). Qed.
Lemma lem2299646 (x : int) (y : int) : True = ((real_of_int x) = (term24 x y)).
Proof. exact (SYM (@lem2299645 x y)). Qed.
Lemma lem2299647 (x : int) (y : int) : (real_of_int x) = (term24 x y).
Proof. exact (EQ_MP (@lem2299646 x y) (@lem0)). Qed.
Lemma lem2299651 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2299652 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem2299651 real t1 t2). Qed.
Lemma lem2299653 (x : int) (y : int) : (term31 x y) = (real_of_int y).
Proof. exact (@lem2299652 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2299654 (y : int) : (term34 y) = (term34 y).
Proof. exact (eq_refl (term34 y)). Qed.
Lemma lem2299655 (x : int) (y : int) : ((real_of_int y) = (term31 x y)) = ((real_of_int y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2299654 y) (@lem2299653 x y)). Qed.
Lemma lem2299657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2299658 (x : real) : (x = x) = True.
Proof. exact (@lem2299657 real x). Qed.
Lemma lem2299659 (y : int) : ((real_of_int y) = (real_of_int y)) = True.
Proof. exact (@lem2299658 (real_of_int y)). Qed.
Lemma lem2299660 (x : int) (y : int) : ((real_of_int y) = (term31 x y)) = True.
Proof. exact (TRANS (@lem2299655 x y) (@lem2299659 y)). Qed.
Lemma lem2299661 (x : int) (y : int) : True = ((real_of_int y) = (term31 x y)).
Proof. exact (SYM (@lem2299660 x y)). Qed.
Lemma lem2299662 (x : int) (y : int) : (real_of_int y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299661 x y) (@lem0)). Qed.
Lemma lem2299663 (x : int) (y : int) (b : Prop) (h1 : ~ b) : (real_of_int y) = (term8 b x y).
Proof. exact (EQ_MP (@lem2299632 x y b h1) (@lem2299662 x y)). Qed.
Lemma lem2299664 (x : int) (y : int) (b : Prop) (h1 : ~ b) : (~ b) = ((real_of_int y) = (term8 b x y)).
Proof. exact (prop_ext (fun h2 : ~ b => @lem2299663 x y b h1) (fun h2 : (real_of_int y) = (term8 b x y) => @lem2299617 b h1)). Qed.
Lemma lem2299665 (x : int) (y : int) (b : Prop) (h1 : ~ b) : (real_of_int y) = (term8 b x y).
Proof. exact (EQ_MP (@lem2299664 x y b h1) (@lem2299617 b h1)). Qed.
Lemma lem2299666 (b : Prop) (x : int) (y : int) : term11 b x y.
Proof. exact (fun h0 : ~ b => @lem2299665 x y b h0). Qed.
Lemma lem2299667 (x : int) (y : int) (b : Prop) (h1 : b) : (real_of_int x) = (term8 b x y).
Proof. exact (EQ_MP (@lem2299616 x y b h1) (@lem2299647 x y)). Qed.
Lemma lem2299668 (x : int) (y : int) (b : Prop) (h1 : b) : b = ((real_of_int x) = (term8 b x y)).
Proof. exact (prop_ext (fun h2 : b => @lem2299667 x y b h1) (fun h2 : (real_of_int x) = (term8 b x y) => @lem2299601 b h1)). Qed.
Lemma lem2299669 (x : int) (y : int) (b : Prop) (h1 : b) : (real_of_int x) = (term8 b x y).
Proof. exact (EQ_MP (@lem2299668 x y b h1) (@lem2299601 b h1)). Qed.
Lemma lem2299670 (b : Prop) (x : int) (y : int) : term14 b x y.
Proof. exact (fun h0 : b => @lem2299669 x y b h0). Qed.
Lemma lem2299671 (b : Prop) (x : int) (y : int) : term17 b x y.
Proof. exact (conj (@lem2299670 b x y) (@lem2299666 b x y)). Qed.
Lemma lem2299672 (b : Prop) (x : int) (y : int) : (term18 b x y) = (term8 b x y).
Proof. exact (EQ_MP (@lem2299600 b x y) (@lem2299671 b x y)). Qed.
