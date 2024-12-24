Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLOSED_term_abbrevs.
Require Import ITERATE_CLOSED_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import sum_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7197664 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (h1). Qed.
Lemma lem7197665 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (SYM (@lem7197664 _131408 h1)). Qed.
Lemma lem7197666 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (h1). Qed.
Lemma lem7197667 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (SYM (@lem7197666 _131408 h1)). Qed.
Lemma lem7197668 {_131408 : Type'} : ((@sum _131408) = (@iterate real _131408 real_add)) = ((@iterate real _131408 real_add) = (@sum _131408)).
Proof. exact (prop_ext (fun h1 : (@sum _131408) = (@iterate real _131408 real_add) => @lem7197665 _131408 h1) (fun h1 : (@iterate real _131408 real_add) = (@sum _131408) => @lem7197667 _131408 h1)). Qed.
Lemma lem7197670 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5782566 A B op). Qed.
Lemma lem7197671 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem7197674 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem7197671 A B op) (@lem7197670 A B op)). Qed.
Lemma lem7197675 {A : Type'} (op : type1627) : term2 A op.
Proof. exact (@lem7197674 A real op). Qed.
Lemma lem7197676 {A : Type'} : term3 A.
Proof. exact (@lem7197675 A real_add). Qed.
Lemma lem7197677 {A : Type'} : term4 A.
Proof. exact (@lem7197676 A (@lem7067132)). Qed.
Lemma lem7197678 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term5 A s P f.
Proof. exact (h1). Qed.
Lemma lem7197679 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term6 A s P f.
Proof. exact (h1). Qed.
Lemma lem7197680 (P : real -> Prop) (h1 : term7 P) : term7 P.
Proof. exact (h1). Qed.
Lemma lem7197681 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term8 A s P f.
Proof. exact (h1). Qed.
Lemma lem7197682 (P : real -> Prop) (h1 : term9 P) : term9 P.
Proof. exact (h1). Qed.
Lemma lem7197683 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7197684 {A : Type'} (P : real -> Prop) (h1 : term4 A) : term10 A P.
Proof. exact (@lem7197683 A h1 P). Qed.
Lemma lem7197685 {A : Type'} (P : real -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem7197686 {A : Type'} (P : real -> Prop) (h1 : term4 A) : term11 A P.
Proof. exact (EQ_MP (@lem7197685 A P) (@lem7197684 A P h1)). Qed.
Lemma lem7197687 (P : real -> Prop) : (term7 P) = ((term7 P) = True).
Proof. exact (@lem7 (term7 P)). Qed.
Lemma lem7197689 (x : real) (P : real -> Prop) (h1 : term9 P) : term12 P x.
Proof. exact (@lem7197682 P h1 x). Qed.
Lemma lem7197690 (P : real -> Prop) (x : real) : (term12 P x) = (term13 P x).
Proof. exact (eq_refl (term12 P x)). Qed.
Lemma lem7197691 (x : real) (P : real -> Prop) (h1 : term9 P) : term13 P x.
Proof. exact (EQ_MP (@lem7197690 P x) (@lem7197689 x P h1)). Qed.
Lemma lem7197692 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : term14 P x y.
Proof. exact (@lem7197691 x P h1 y). Qed.
Lemma lem7197693 (P : real -> Prop) (x : real) (y : real) : (term14 P x y) = (term15 P x y).
Proof. exact (eq_refl (term14 P x y)). Qed.
Lemma lem7197694 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : term15 P x y.
Proof. exact (EQ_MP (@lem7197693 P x y) (@lem7197692 x y P h1)). Qed.
Lemma lem7197695 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : term16 x P y.
Proof. exact (h1). Qed.
Lemma lem7197696 (x : real) (P : real -> Prop) (y : real) (h1 : term9 P) (h2 : term16 x P y) : term17 P x y.
Proof. exact (@lem7197694 x y P h1 (@lem7197695 x P y h2)). Qed.
Lemma lem7197697 (P : real -> Prop) (x : real) (y : real) : (term17 P x y) = ((term17 P x y) = True).
Proof. exact (@lem7 (term17 P x y)). Qed.
Lemma lem7197698 (x : real) (P : real -> Prop) (y : real) (h1 : term9 P) (h2 : term16 x P y) : (term17 P x y) = True.
Proof. exact (EQ_MP (@lem7197697 P x y) (@lem7197696 x P y h1 h2)). Qed.
Lemma lem7197704 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term18 A s P f a.
Proof. exact (@lem7197681 A s P f h1 a). Qed.
Lemma lem7197705 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (a : A) : (term18 A s P f a) = (term19 A s P f a).
Proof. exact (eq_refl (term18 A s P f a)). Qed.
Lemma lem7197706 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term19 A s P f a.
Proof. exact (EQ_MP (@lem7197705 A s P f a) (@lem7197704 A a s P f h1)). Qed.
Lemma lem7197707 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem7197708 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) (s : A -> Prop) (h1 : term8 A s P f) (h2 : @IN A a s) : term20 A P f a.
Proof. exact (@lem7197706 A a s P f h1 (@lem7197707 A a s h2)). Qed.
Lemma lem7197709 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) : (term20 A P f a) = ((term20 A P f a) = True).
Proof. exact (@lem7 (term20 A P f a)). Qed.
Lemma lem7197710 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) (s : A -> Prop) (h1 : term8 A s P f) (h2 : @IN A a s) : (term20 A P f a) = True.
Proof. exact (EQ_MP (@lem7197709 A P f a) (@lem7197708 A P f a s h1 h2)). Qed.
Lemma lem7197719 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7197720 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7197719 p q p' q'). Qed.
Lemma lem7197721 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7197720 p q p'). Qed.
Lemma lem7197722 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : term24 A P s f.
Proof. exact (@lem7197721 (term11 A P) (term25 A P s f)). Qed.
Lemma lem7197723 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : term26 A P s f p'.
Proof. exact (@lem7197722 A P s f p'). Qed.
Lemma lem7197724 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : (term26 A P s f p') = (term27 A P s f p').
Proof. exact (eq_refl (term26 A P s f p')). Qed.
Lemma lem7197725 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : term27 A P s f p'.
Proof. exact (EQ_MP (@lem7197724 A P s f p') (@lem7197723 A P s f p')). Qed.
Lemma lem7197726 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term28 A P s f p' q'.
Proof. exact (@lem7197725 A P s f p' q'). Qed.
Lemma lem7197727 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term28 A P s f p' q') = (term29 A P s f p' q').
Proof. exact (eq_refl (term28 A P s f p' q')). Qed.
Lemma lem7197728 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term29 A P s f p' q'.
Proof. exact (EQ_MP (@lem7197727 A P s f p' q') (@lem7197726 A P s f p' q')). Qed.
Lemma lem7197732 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7197733 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7197732 p q p' q'). Qed.
Lemma lem7197734 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7197733 p q p'). Qed.
Lemma lem7197735 {A : Type'} (P : real -> Prop) : term30 A P.
Proof. exact (@lem7197734 (term31 P) (term32 A P)). Qed.
Lemma lem7197736 {A : Type'} (P : real -> Prop) (p' : Prop) : term33 A P p'.
Proof. exact (@lem7197735 A P p'). Qed.
Lemma lem7197737 {A : Type'} (P : real -> Prop) (p' : Prop) : (term33 A P p') = (term34 A P p').
Proof. exact (eq_refl (term33 A P p')). Qed.
Lemma lem7197738 {A : Type'} (P : real -> Prop) (p' : Prop) : term34 A P p'.
Proof. exact (EQ_MP (@lem7197737 A P p') (@lem7197736 A P p')). Qed.
Lemma lem7197739 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : term35 A P p' q'.
Proof. exact (@lem7197738 A P p' q'). Qed.
Lemma lem7197740 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : (term35 A P p' q') = (term36 A P p' q').
Proof. exact (eq_refl (term35 A P p' q')). Qed.
Lemma lem7197741 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : term36 A P p' q'.
Proof. exact (EQ_MP (@lem7197740 A P p' q') (@lem7197739 A P p' q')). Qed.
Lemma lem7197745 : (@neutral real real_add) = term37.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7197746 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7197747 (P : real -> Prop) : (term38 P) = (term7 P).
Proof. exact (MK_COMB (@lem7197746 P) (@lem7197745)). Qed.
Lemma lem7197749 (P : real -> Prop) (h1 : term7 P) : (term7 P) = True.
Proof. exact (EQ_MP (@lem7197687 P) (@lem7197680 P h1)). Qed.
Lemma lem7197750 (P : real -> Prop) (h1 : term7 P) : (term38 P) = True.
Proof. exact (TRANS (@lem7197747 P) (@lem7197749 P h1)). Qed.
Lemma lem7197751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7197752 (P : real -> Prop) (h1 : term7 P) : (term39 P) = (and True).
Proof. exact (MK_COMB (@lem7197751) (@lem7197750 P h1)). Qed.
Lemma lem7197764 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7197765 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7197764 p q p' q'). Qed.
Lemma lem7197766 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7197765 p q p'). Qed.
Lemma lem7197767 (P : real -> Prop) (x : real) (y : real) : term40 P x y.
Proof. exact (@lem7197766 (term16 x P y) (term17 P x y)). Qed.
Lemma lem7197768 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : term41 P x y p'.
Proof. exact (@lem7197767 P x y p'). Qed.
Lemma lem7197769 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : (term41 P x y p') = (term42 P x y p').
Proof. exact (eq_refl (term41 P x y p')). Qed.
Lemma lem7197770 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : term42 P x y p'.
Proof. exact (EQ_MP (@lem7197769 P x y p') (@lem7197768 P x y p')). Qed.
Lemma lem7197771 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term43 P x y p' q'.
Proof. exact (@lem7197770 P x y p' q'). Qed.
Lemma lem7197772 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term43 P x y p' q') = (term44 P x y p' q').
Proof. exact (eq_refl (term43 P x y p' q')). Qed.
Lemma lem7197773 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term44 P x y p' q'.
Proof. exact (EQ_MP (@lem7197772 P x y p' q') (@lem7197771 P x y p' q')). Qed.
Lemma lem7197776 (x : real) (P : real -> Prop) (y : real) : (term16 x P y) = (term16 x P y).
Proof. exact (eq_refl (term16 x P y)). Qed.
Lemma lem7197777 (x : real) (P : real -> Prop) (y : real) (q' : Prop) : term45 x P y q'.
Proof. exact (@lem7197773 P x y (term16 x P y) q'). Qed.
Lemma lem7197778 (x : real) (P : real -> Prop) (y : real) (q' : Prop) : term46 x P y q'.
Proof. exact (@lem7197777 x P y q' (@lem7197776 x P y)). Qed.
Lemma lem7197779 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : term16 x P y.
Proof. exact (h1). Qed.
Lemma lem7197780 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : P y.
Proof. exact (proj2 (@lem7197779 x P y h1)). Qed.
Lemma lem7197781 (P : real -> Prop) (y : real) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem7197783 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : P x.
Proof. exact (proj1 (@lem7197779 x P y h1)). Qed.
Lemma lem7197784 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7197787 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : term47 P x y.
Proof. exact (fun h0 : term16 x P y => @lem7197698 x P y h1 h0). Qed.
Lemma lem7197791 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : (P x) = True.
Proof. exact (EQ_MP (@lem7197784 P x) (@lem7197783 x P y h1)). Qed.
Lemma lem7197792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7197793 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : (term48 P x) = (and True).
Proof. exact (MK_COMB (@lem7197792) (@lem7197791 x P y h1)). Qed.
Lemma lem7197795 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : (P y) = True.
Proof. exact (EQ_MP (@lem7197781 P y) (@lem7197780 x P y h1)). Qed.
Lemma lem7197796 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : (term16 x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem7197793 x P y h1) (@lem7197795 x P y h1)). Qed.
Lemma lem7197798 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7197799 : (True /\ True) = True.
Proof. exact (@lem7197798 True). Qed.
Lemma lem7197800 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : (term16 x P y) = True.
Proof. exact (TRANS (@lem7197796 x P y h1) (@lem7197799)). Qed.
Lemma lem7197801 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : True = (term16 x P y).
Proof. exact (SYM (@lem7197800 x P y h1)). Qed.
Lemma lem7197802 (x : real) (P : real -> Prop) (y : real) (h1 : term16 x P y) : term16 x P y.
Proof. exact (EQ_MP (@lem7197801 x P y h1) (@lem0)). Qed.
Lemma lem7197803 (x : real) (P : real -> Prop) (y : real) (h1 : term9 P) (h2 : term16 x P y) : (term17 P x y) = True.
Proof. exact (@lem7197787 x y P h1 (@lem7197802 x P y h2)). Qed.
Lemma lem7197804 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : term47 P x y.
Proof. exact (fun h0 : term16 x P y => @lem7197803 x P y h1 h0). Qed.
Lemma lem7197805 (x : real) (P : real -> Prop) (y : real) : term49 x P y.
Proof. exact (@lem7197778 x P y True). Qed.
Lemma lem7197806 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : (term15 P x y) = (term50 x P y).
Proof. exact (@lem7197805 x P y (@lem7197804 x y P h1)). Qed.
Lemma lem7197808 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7197809 (x : real) (P : real -> Prop) (y : real) : (term50 x P y) = True.
Proof. exact (@lem7197808 (term16 x P y)). Qed.
Lemma lem7197810 (x : real) (y : real) (P : real -> Prop) (h1 : term9 P) : (term15 P x y) = True.
Proof. exact (TRANS (@lem7197806 x y P h1) (@lem7197809 x P y)). Qed.
Lemma lem7197811 (x : real) (P : real -> Prop) (h1 : term9 P) : (term51 P x) = term52.
Proof. exact (fun_ext (fun y : real => @lem7197810 x y P h1)). Qed.
Lemma lem7197812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197813 (x : real) (P : real -> Prop) (h1 : term9 P) : (term13 P x) = term53.
Proof. exact (MK_COMB (@lem7197812) (@lem7197811 x P h1)). Qed.
Lemma lem7197815 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7197816 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7197815 real t). Qed.
Lemma lem7197817 : term53 = True.
Proof. exact (@lem7197816 True). Qed.
Lemma lem7197818 (x : real) (P : real -> Prop) (h1 : term9 P) : (term13 P x) = True.
Proof. exact (TRANS (@lem7197813 x P h1) (@lem7197817)). Qed.
Lemma lem7197819 (P : real -> Prop) (h1 : term9 P) : (term56 P) = term52.
Proof. exact (fun_ext (fun x : real => @lem7197818 x P h1)). Qed.
Lemma lem7197820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197821 (P : real -> Prop) (h1 : term9 P) : (term9 P) = term53.
Proof. exact (MK_COMB (@lem7197820) (@lem7197819 P h1)). Qed.
Lemma lem7197823 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7197824 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7197823 real t). Qed.
Lemma lem7197825 : term53 = True.
Proof. exact (@lem7197824 True). Qed.
Lemma lem7197826 (P : real -> Prop) (h1 : term9 P) : (term9 P) = True.
Proof. exact (TRANS (@lem7197821 P h1) (@lem7197825)). Qed.
Lemma lem7197827 (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : (term31 P) = (True /\ True).
Proof. exact (MK_COMB (@lem7197752 P h2) (@lem7197826 P h1)). Qed.
Lemma lem7197829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7197830 : (True /\ True) = True.
Proof. exact (@lem7197829 True). Qed.
Lemma lem7197831 (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : (term31 P) = True.
Proof. exact (TRANS (@lem7197827 P h1 h2) (@lem7197830)). Qed.
Lemma lem7197832 {A : Type'} (P : real -> Prop) (q' : Prop) : term57 A P q'.
Proof. exact (@lem7197741 A P True q'). Qed.
Lemma lem7197833 {A : Type'} (q' : Prop) (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : term58 A P q'.
Proof. exact (@lem7197832 A P q' (@lem7197831 P h1 h2)). Qed.
Lemma lem7197977 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7197978 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7197977 p q p' q'). Qed.
Lemma lem7197979 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7197978 p q p'). Qed.
Lemma lem7197980 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) : term59 A P _96483 f.
Proof. exact (@lem7197979 (term60 A _96483 P f) (term61 A P _96483 f)). Qed.
Lemma lem7197981 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) : term62 A P _96483 f p'.
Proof. exact (@lem7197980 A P _96483 f p'). Qed.
Lemma lem7197982 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) : (term62 A P _96483 f p') = (term63 A P _96483 f p').
Proof. exact (eq_refl (term62 A P _96483 f p')). Qed.
Lemma lem7197983 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) : term63 A P _96483 f p'.
Proof. exact (EQ_MP (@lem7197982 A P _96483 f p') (@lem7197981 A P _96483 f p')). Qed.
Lemma lem7197984 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term64 A P _96483 f p' q'.
Proof. exact (@lem7197983 A P _96483 f p' q'). Qed.
Lemma lem7197985 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term64 A P _96483 f p' q') = (term65 A P _96483 f p' q').
Proof. exact (eq_refl (term64 A P _96483 f p' q')). Qed.
Lemma lem7197986 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term65 A P _96483 f p' q'.
Proof. exact (EQ_MP (@lem7197985 A P _96483 f p' q') (@lem7197984 A P _96483 f p' q')). Qed.
Lemma lem7197994 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7197995 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7197994 p q p' q'). Qed.
Lemma lem7197996 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7197995 p q p'). Qed.
Lemma lem7197997 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : term66 A _96483 P f x.
Proof. exact (@lem7197996 (term67 A _96483 f x) (term20 A P f x)). Qed.
Lemma lem7197998 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term68 A _96483 P f x p'.
Proof. exact (@lem7197997 A _96483 P f x p'). Qed.
Lemma lem7197999 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term68 A _96483 P f x p') = (term69 A _96483 P f x p').
Proof. exact (eq_refl (term68 A _96483 P f x p')). Qed.
Lemma lem7198000 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term69 A _96483 P f x p'.
Proof. exact (EQ_MP (@lem7197999 A _96483 P f x p') (@lem7197998 A _96483 P f x p')). Qed.
Lemma lem7198001 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term70 A _96483 P f x p' q'.
Proof. exact (@lem7198000 A _96483 P f x p' q'). Qed.
Lemma lem7198002 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term70 A _96483 P f x p' q') = (term71 A _96483 P f x p' q').
Proof. exact (eq_refl (term70 A _96483 P f x p' q')). Qed.
Lemma lem7198003 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term71 A _96483 P f x p' q'.
Proof. exact (EQ_MP (@lem7198002 A _96483 P f x p' q') (@lem7198001 A _96483 P f x p' q')). Qed.
Lemma lem7198009 : (@neutral real real_add) = term37.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7198010 {A : Type'} (f : A -> real) (x : A) : (term72 A f x) = (term72 A f x).
Proof. exact (eq_refl (term72 A f x)). Qed.
Lemma lem7198011 {A : Type'} (f : A -> real) (x : A) : ((f x) = (@neutral real real_add)) = ((f x) = term37).
Proof. exact (MK_COMB (@lem7198010 A f x) (@lem7198009)). Qed.
Lemma lem7198014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7198015 {A : Type'} (f : A -> real) (x : A) : (term73 A f x) = (term74 A f x).
Proof. exact (MK_COMB (@lem7198014) (@lem7198011 A f x)). Qed.
Lemma lem7198018 {A : Type'} (x : A) (_96483 : A -> Prop) : (term75 A x _96483) = (term75 A x _96483).
Proof. exact (eq_refl (term75 A x _96483)). Qed.
Lemma lem7198019 {A : Type'} (_96483 : A -> Prop) (f : A -> real) (x : A) : (term67 A _96483 f x) = (term76 A _96483 f x).
Proof. exact (MK_COMB (@lem7198018 A x _96483) (@lem7198015 A f x)). Qed.
Lemma lem7198024 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term77 A P _96483 f x q'.
Proof. exact (@lem7198003 A _96483 P f x (term76 A _96483 f x) q'). Qed.
Lemma lem7198025 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term78 A P _96483 f x q'.
Proof. exact (@lem7198024 A P _96483 f x q' (@lem7198019 A _96483 f x)). Qed.
Lemma lem7198050 {A : Type'} (P : real -> Prop) (f : A -> real) (x : A) : (term20 A P f x) = (term20 A P f x).
Proof. exact (eq_refl (term20 A P f x)). Qed.
Lemma lem7198051 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : term79 A _96483 P f x.
Proof. exact (fun h0 : term76 A _96483 f x => @lem7198050 A P f x). Qed.
Lemma lem7198052 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : term80 A _96483 P f x.
Proof. exact (@lem7198025 A P _96483 f x (term20 A P f x)). Qed.
Lemma lem7198053 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : (term81 A _96483 P f x) = (term82 A _96483 P f x).
Proof. exact (@lem7198052 A _96483 P f x (@lem7198051 A _96483 P f x)). Qed.
Lemma lem7198112 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) : (term83 A _96483 P f) = (term84 A _96483 P f).
Proof. exact (fun_ext (fun x : A => @lem7198053 A _96483 P f x)). Qed.
Lemma lem7198171 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7198172 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) : (term60 A _96483 P f) = (term85 A _96483 P f).
Proof. exact (MK_COMB (@lem7198171 A) (@lem7198112 A _96483 P f)). Qed.
Lemma lem7198235 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (q' : Prop) : term86 A _96483 P f q'.
Proof. exact (@lem7197986 A P _96483 f (term85 A _96483 P f) q'). Qed.
Lemma lem7198236 {A : Type'} (_96483 : A -> Prop) (P : real -> Prop) (f : A -> real) (q' : Prop) : term87 A _96483 P f q'.
Proof. exact (@lem7198235 A _96483 P f q' (@lem7198172 A _96483 P f)). Qed.
Lemma lem7198251 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7197668 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7198252 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7198251 A). Qed.
Lemma lem7198253 {A : Type'} (_96483 : A -> Prop) : _96483 = _96483.
Proof. exact (eq_refl _96483). Qed.
Lemma lem7198254 {A : Type'} (_96483 : A -> Prop) : (@iterate real A real_add _96483) = (@sum A _96483).
Proof. exact (MK_COMB (@lem7198252 A) (@lem7198253 A _96483)). Qed.
Lemma lem7198255 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7198256 {A : Type'} (_96483 : A -> Prop) (f : A -> real) : (@iterate real A real_add _96483 f) = (@sum A _96483 f).
Proof. exact (MK_COMB (@lem7198254 A _96483) (@lem7198255 A f)). Qed.
Lemma lem7198257 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7198258 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) : (term61 A P _96483 f) = (term25 A P _96483 f).
Proof. exact (MK_COMB (@lem7198257 P) (@lem7198256 A _96483 f)). Qed.
Lemma lem7198259 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) : term88 A P _96483 f.
Proof. exact (fun h0 : term85 A _96483 P f => @lem7198258 A P _96483 f). Qed.
Lemma lem7198260 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) : term89 A P _96483 f.
Proof. exact (@lem7198236 A _96483 P f (term25 A P _96483 f)). Qed.
Lemma lem7198261 {A : Type'} (P : real -> Prop) (_96483 : A -> Prop) (f : A -> real) : (term90 A P _96483 f) = (term91 A P _96483 f).
Proof. exact (@lem7198260 A P _96483 f (@lem7198259 A P _96483 f)). Qed.
Lemma lem7198421 {A : Type'} (P : real -> Prop) (f : A -> real) : (term92 A P f) = (term93 A P f).
Proof. exact (fun_ext (fun _96483 : A -> Prop => @lem7198261 A P _96483 f)). Qed.
Lemma lem7198683 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7198684 {A : Type'} (P : real -> Prop) (f : A -> real) : (term94 A P f) = (term95 A P f).
Proof. exact (MK_COMB (@lem7198683 A) (@lem7198421 A P f)). Qed.
Lemma lem7198950 {A : Type'} (P : real -> Prop) : (term96 A P) = (term97 A P).
Proof. exact (fun_ext (fun f : A -> real => @lem7198684 A P f)). Qed.
Lemma lem7199216 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7199217 {A : Type'} (P : real -> Prop) : (term32 A P) = (term98 A P).
Proof. exact (MK_COMB (@lem7199216 A) (@lem7198950 A P)). Qed.
Lemma lem7199487 {A : Type'} (P : real -> Prop) : term99 A P.
Proof. exact (fun h0 : True => @lem7199217 A P). Qed.
Lemma lem7199488 {A : Type'} (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : term100 A P.
Proof. exact (@lem7197833 A (term98 A P) P h1 h2). Qed.
Lemma lem7199489 {A : Type'} (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : (term11 A P) = (term101 A P).
Proof. exact (@lem7199488 A P h1 h2 (@lem7199487 A P)). Qed.
Lemma lem7199491 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7199492 {A : Type'} (P : real -> Prop) : (term101 A P) = (term98 A P).
Proof. exact (@lem7199491 (term98 A P)). Qed.
Lemma lem7199752 {A : Type'} (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : (term11 A P) = (term98 A P).
Proof. exact (TRANS (@lem7199489 A P h1 h2) (@lem7199492 A P)). Qed.
Lemma lem7199753 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (q' : Prop) : term102 A s f P q'.
Proof. exact (@lem7197728 A P s f (term98 A P) q'). Qed.
Lemma lem7199754 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : term103 A s f P q'.
Proof. exact (@lem7199753 A s f P q' (@lem7199752 A P h1 h2)). Qed.
Lemma lem7199755 {A : Type'} (P : real -> Prop) (h1 : term98 A P) : term98 A P.
Proof. exact (h1). Qed.
Lemma lem7199756 {A : Type'} (f : A -> real) (P : real -> Prop) (h1 : term98 A P) : term104 A P f.
Proof. exact (@lem7199755 A P h1 f). Qed.
Lemma lem7199757 {A : Type'} (P : real -> Prop) (f : A -> real) : (term104 A P f) = (term95 A P f).
Proof. exact (eq_refl (term104 A P f)). Qed.
Lemma lem7199758 {A : Type'} (f : A -> real) (P : real -> Prop) (h1 : term98 A P) : term95 A P f.
Proof. exact (EQ_MP (@lem7199757 A P f) (@lem7199756 A f P h1)). Qed.
Lemma lem7199759 {A : Type'} (f : A -> real) (s : A -> Prop) (P : real -> Prop) (h1 : term98 A P) : term105 A P f s.
Proof. exact (@lem7199758 A f P h1 s). Qed.
Lemma lem7199760 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : (term105 A P f s) = (term91 A P s f).
Proof. exact (eq_refl (term105 A P f s)). Qed.
Lemma lem7199761 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term98 A P) : term91 A P s f.
Proof. exact (EQ_MP (@lem7199760 A P s f) (@lem7199759 A f s P h1)). Qed.
Lemma lem7199762 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term85 A s P f) : term85 A s P f.
Proof. exact (h1). Qed.
Lemma lem7199763 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term85 A s P f) (h2 : term98 A P) : term25 A P s f.
Proof. exact (@lem7199761 A s f P h2 (@lem7199762 A s P f h1)). Qed.
Lemma lem7199764 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : (term25 A P s f) = ((term25 A P s f) = True).
Proof. exact (@lem7 (term25 A P s f)). Qed.
Lemma lem7199765 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term85 A s P f) (h2 : term98 A P) : (term25 A P s f) = True.
Proof. exact (EQ_MP (@lem7199764 A P s f) (@lem7199763 A s f P h1 h2)). Qed.
Lemma lem7199772 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term98 A P) : term106 A P s f.
Proof. exact (fun h0 : term85 A s P f => @lem7199765 A s f P h0 h1). Qed.
Lemma lem7199773 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term98 A P) : term106 A P s f.
Proof. exact (@lem7199772 A s f P h1). Qed.
Lemma lem7199781 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7199782 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7199781 p q p' q'). Qed.
Lemma lem7199783 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7199782 p q p'). Qed.
Lemma lem7199784 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : term107 A s P f x.
Proof. exact (@lem7199783 (term76 A s f x) (term20 A P f x)). Qed.
Lemma lem7199785 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term108 A s P f x p'.
Proof. exact (@lem7199784 A s P f x p'). Qed.
Lemma lem7199786 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term108 A s P f x p') = (term109 A s P f x p').
Proof. exact (eq_refl (term108 A s P f x p')). Qed.
Lemma lem7199787 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term109 A s P f x p'.
Proof. exact (EQ_MP (@lem7199786 A s P f x p') (@lem7199785 A s P f x p')). Qed.
Lemma lem7199788 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term110 A s P f x p' q'.
Proof. exact (@lem7199787 A s P f x p' q'). Qed.
Lemma lem7199789 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term110 A s P f x p' q') = (term111 A s P f x p' q').
Proof. exact (eq_refl (term110 A s P f x p' q')). Qed.
Lemma lem7199790 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term111 A s P f x p' q'.
Proof. exact (EQ_MP (@lem7199789 A s P f x p' q') (@lem7199788 A s P f x p' q')). Qed.
Lemma lem7199795 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term76 A s f x) = (term76 A s f x).
Proof. exact (eq_refl (term76 A s f x)). Qed.
Lemma lem7199796 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term112 A P s f x q'.
Proof. exact (@lem7199790 A s P f x (term76 A s f x) q'). Qed.
Lemma lem7199797 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term113 A P s f x q'.
Proof. exact (@lem7199796 A P s f x q' (@lem7199795 A s f x)). Qed.
Lemma lem7199798 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term76 A s f x) : term76 A s f x.
Proof. exact (h1). Qed.
Lemma lem7199813 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term76 A s f x) : @IN A x s.
Proof. exact (proj1 (@lem7199798 A s f x h1)). Qed.
Lemma lem7199814 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7199817 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term114 A s P f a.
Proof. exact (fun h0 : @IN A a s => @lem7197710 A P f a s h1 h0). Qed.
Lemma lem7199818 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term114 A s P f a.
Proof. exact (@lem7199817 A a s P f h1). Qed.
Lemma lem7199819 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term114 A s P f x.
Proof. exact (@lem7199818 A x s P f h1). Qed.
Lemma lem7199821 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term76 A s f x) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7199814 A x s) (@lem7199813 A s f x h1)). Qed.
Lemma lem7199822 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term76 A s f x) : True = (@IN A x s).
Proof. exact (SYM (@lem7199821 A s f x h1)). Qed.
Lemma lem7199823 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term76 A s f x) : @IN A x s.
Proof. exact (EQ_MP (@lem7199822 A s f x h1) (@lem0)). Qed.
Lemma lem7199824 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term8 A s P f) (h2 : term76 A s f x) : (term20 A P f x) = True.
Proof. exact (@lem7199819 A x s P f h1 (@lem7199823 A s f x h2)). Qed.
Lemma lem7199825 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term115 A s P f x.
Proof. exact (fun h0 : term76 A s f x => @lem7199824 A P s f x h1 h0). Qed.
Lemma lem7199826 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (x : A) : term116 A P s f x.
Proof. exact (@lem7199797 A P s f x True). Qed.
Lemma lem7199827 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : (term82 A s P f x) = (term117 A s f x).
Proof. exact (@lem7199826 A P s f x (@lem7199825 A x s P f h1)). Qed.
Lemma lem7199829 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7199830 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term117 A s f x) = True.
Proof. exact (@lem7199829 (term76 A s f x)). Qed.
Lemma lem7199831 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : (term82 A s P f x) = True.
Proof. exact (TRANS (@lem7199827 A x s P f h1) (@lem7199830 A s f x)). Qed.
Lemma lem7199832 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : (term84 A s P f) = (term118 A).
Proof. exact (fun_ext (fun x : A => @lem7199831 A x s P f h1)). Qed.
Lemma lem7199833 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7199834 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : (term85 A s P f) = (term119 A).
Proof. exact (MK_COMB (@lem7199833 A) (@lem7199832 A s P f h1)). Qed.
Lemma lem7199836 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7199837 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (@lem7199836 A t). Qed.
Lemma lem7199838 {A : Type'} : (term119 A) = True.
Proof. exact (@lem7199837 A True). Qed.
Lemma lem7199839 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : (term85 A s P f) = True.
Proof. exact (TRANS (@lem7199834 A s P f h1) (@lem7199838 A)). Qed.
Lemma lem7199840 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : True = (term85 A s P f).
Proof. exact (SYM (@lem7199839 A s P f h1)). Qed.
Lemma lem7199841 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term85 A s P f.
Proof. exact (EQ_MP (@lem7199840 A s P f h1) (@lem0)). Qed.
Lemma lem7199842 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term98 A P) : (term25 A P s f) = True.
Proof. exact (@lem7199773 A s f P h2 (@lem7199841 A s P f h1)). Qed.
Lemma lem7199843 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term8 A s P f) : term120 A P s f.
Proof. exact (fun h0 : term98 A P => @lem7199842 A s f P h1 h0). Qed.
Lemma lem7199844 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term9 P) (h2 : term7 P) : term121 A s f P.
Proof. exact (@lem7199754 A s f True P h1 h2). Qed.
Lemma lem7199845 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term122 A P s f) = (term123 A P).
Proof. exact (@lem7199844 A s f P h2 h3 (@lem7199843 A s P f h1)). Qed.
Lemma lem7199847 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7199848 {A : Type'} (P : real -> Prop) : (term123 A P) = True.
Proof. exact (@lem7199847 (term98 A P)). Qed.
Lemma lem7199849 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term122 A P s f) = True.
Proof. exact (TRANS (@lem7199845 A s f P h1 h2 h3) (@lem7199848 A P)). Qed.
Lemma lem7199850 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : True = (term122 A P s f).
Proof. exact (SYM (@lem7199849 A s f P h1 h2 h3)). Qed.
Lemma lem7199851 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term122 A P s f.
Proof. exact (EQ_MP (@lem7199850 A s f P h1 h2 h3) (@lem0)). Qed.
Lemma lem7199852 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term4 A) (h3 : term9 P) (h4 : term7 P) : term25 A P s f.
Proof. exact (@lem7199851 A s f P h1 h3 h4 (@lem7197686 A P h2)). Qed.
Lemma lem7199853 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term124 A P s f.
Proof. exact (fun h0 : term4 A => @lem7199852 A s f P h1 h0 h2 h3). Qed.
Lemma lem7199854 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (@lem7199853 A s f P h1 h2 h3 (@lem7197677 A)). Qed.
Lemma lem7199855 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term6 A s P f.
Proof. exact (proj2 (@lem7197678 A s P f h1)). Qed.
Lemma lem7199856 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term7 P.
Proof. exact (proj1 (@lem7197678 A s P f h1)). Qed.
Lemma lem7199857 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term8 A s P f.
Proof. exact (proj2 (@lem7197679 A s P f h1)). Qed.
Lemma lem7199858 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term9 P.
Proof. exact (proj1 (@lem7197679 A s P f h1)). Qed.
Lemma lem7199859 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term8 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s P f => @lem7199854 A s f P h1 h2 h3) (fun h4 : term25 A P s f => @lem7197681 A s P f h1)). Qed.
Lemma lem7199860 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199859 A s f P h1 h2 h3) (@lem7197681 A s P f h1)). Qed.
Lemma lem7199861 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term9 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term9 P => @lem7199860 A s f P h1 h2 h3) (fun h4 : term25 A P s f => @lem7197682 P h2)). Qed.
Lemma lem7199862 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199861 A s f P h1 h2 h3) (@lem7197682 P h2)). Qed.
Lemma lem7199863 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 P) (h2 : term7 P) (h3 : term6 A s P f) : (term8 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s P f => @lem7199862 A s f P h4 h1 h2) (fun h4 : term25 A P s f => @lem7199857 A s P f h3)). Qed.
Lemma lem7199864 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 P) (h2 : term7 P) (h3 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199863 A s P f h1 h2 h3) (@lem7199857 A s P f h3)). Qed.
Lemma lem7199865 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term6 A s P f) : (term9 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term9 P => @lem7199864 A s P f h3 h1 h2) (fun h3 : term25 A P s f => @lem7199858 A s P f h2)). Qed.
Lemma lem7199866 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199865 A s P f h1 h2) (@lem7199858 A s P f h2)). Qed.
Lemma lem7199867 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term6 A s P f) : (term7 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term7 P => @lem7199866 A s P f h1 h2) (fun h3 : term25 A P s f => @lem7197680 P h1)). Qed.
Lemma lem7199868 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199867 A s P f h1 h2) (@lem7197680 P h1)). Qed.
Lemma lem7199869 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term5 A s P f) : (term6 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term6 A s P f => @lem7199868 A s P f h1 h3) (fun h3 : term25 A P s f => @lem7199855 A s P f h2)). Qed.
Lemma lem7199870 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 P) (h2 : term5 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199869 A s P f h1 h2) (@lem7199855 A s P f h2)). Qed.
Lemma lem7199871 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : (term7 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h2 : term7 P => @lem7199870 A s P f h2 h1) (fun h2 : term25 A P s f => @lem7199856 A s P f h1)). Qed.
Lemma lem7199872 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7199871 A s P f h1) (@lem7199856 A s P f h1)). Qed.
Lemma lem7199873 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : term125 A P s f.
Proof. exact (fun h0 : term5 A s P f => @lem7199872 A s P f h0). Qed.
Lemma lem7199878 {A : Type'} (P : real -> Prop) (f : A -> real) : term126 A P f.
Proof. exact (fun s : A -> Prop => @lem7199873 A P s f). Qed.
Lemma lem7199883 {A : Type'} (P : real -> Prop) : term127 A P.
Proof. exact (fun f : A -> real => @lem7199878 A P f). Qed.
Lemma lem7199888 {A : Type'} : term128 A.
Proof. exact (fun P : real -> Prop => @lem7199883 A P). Qed.
