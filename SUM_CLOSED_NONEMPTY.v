Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLOSED_NONEMPTY_term_abbrevs.
Require Import ITERATE_CLOSED_NONEMPTY_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import sum_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7203539 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (h1). Qed.
Lemma lem7203540 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (SYM (@lem7203539 _131408 h1)). Qed.
Lemma lem7203541 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (h1). Qed.
Lemma lem7203542 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (SYM (@lem7203541 _131408 h1)). Qed.
Lemma lem7203543 {_131408 : Type'} : ((@sum _131408) = (@iterate real _131408 real_add)) = ((@iterate real _131408 real_add) = (@sum _131408)).
Proof. exact (prop_ext (fun h1 : (@sum _131408) = (@iterate real _131408 real_add) => @lem7203540 _131408 h1) (fun h1 : (@iterate real _131408 real_add) = (@sum _131408) => @lem7203542 _131408 h1)). Qed.
Lemma lem7203545 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5809499 A B op). Qed.
Lemma lem7203546 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem7203549 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem7203546 A B op) (@lem7203545 A B op)). Qed.
Lemma lem7203550 {A : Type'} (op : type1627) : term2 A op.
Proof. exact (@lem7203549 A real op). Qed.
Lemma lem7203551 {A : Type'} : term3 A.
Proof. exact (@lem7203550 A real_add). Qed.
Lemma lem7203552 {A : Type'} : term4 A.
Proof. exact (@lem7203551 A (@lem7067132)). Qed.
Lemma lem7203553 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term5 A s P f.
Proof. exact (h1). Qed.
Lemma lem7203554 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term6 A s P f.
Proof. exact (h1). Qed.
Lemma lem7203555 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7203556 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 A s P f) : term7 A s P f.
Proof. exact (h1). Qed.
Lemma lem7203557 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : term8 A s.
Proof. exact (h1). Qed.
Lemma lem7203558 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term9 A s P f.
Proof. exact (h1). Qed.
Lemma lem7203559 (P : real -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem7203560 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7203561 {A : Type'} (P : real -> Prop) (h1 : term4 A) : term11 A P.
Proof. exact (@lem7203560 A h1 P). Qed.
Lemma lem7203562 {A : Type'} (P : real -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem7203563 {A : Type'} (P : real -> Prop) (h1 : term4 A) : term12 A P.
Proof. exact (EQ_MP (@lem7203562 A P) (@lem7203561 A P h1)). Qed.
Lemma lem7203564 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7203566 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem7203579 (x : real) (P : real -> Prop) (h1 : term10 P) : term14 P x.
Proof. exact (@lem7203559 P h1 x). Qed.
Lemma lem7203580 (P : real -> Prop) (x : real) : (term14 P x) = (term15 P x).
Proof. exact (eq_refl (term14 P x)). Qed.
Lemma lem7203581 (x : real) (P : real -> Prop) (h1 : term10 P) : term15 P x.
Proof. exact (EQ_MP (@lem7203580 P x) (@lem7203579 x P h1)). Qed.
Lemma lem7203582 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : term16 P x y.
Proof. exact (@lem7203581 x P h1 y). Qed.
Lemma lem7203583 (P : real -> Prop) (x : real) (y : real) : (term16 P x y) = (term17 P x y).
Proof. exact (eq_refl (term16 P x y)). Qed.
Lemma lem7203584 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : term17 P x y.
Proof. exact (EQ_MP (@lem7203583 P x y) (@lem7203582 x y P h1)). Qed.
Lemma lem7203585 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : term18 x P y.
Proof. exact (h1). Qed.
Lemma lem7203586 (x : real) (P : real -> Prop) (y : real) (h1 : term10 P) (h2 : term18 x P y) : term19 P x y.
Proof. exact (@lem7203584 x y P h1 (@lem7203585 x P y h2)). Qed.
Lemma lem7203587 (P : real -> Prop) (x : real) (y : real) : (term19 P x y) = ((term19 P x y) = True).
Proof. exact (@lem7 (term19 P x y)). Qed.
Lemma lem7203588 (x : real) (P : real -> Prop) (y : real) (h1 : term10 P) (h2 : term18 x P y) : (term19 P x y) = True.
Proof. exact (EQ_MP (@lem7203587 P x y) (@lem7203586 x P y h1 h2)). Qed.
Lemma lem7203594 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term20 A s P f a.
Proof. exact (@lem7203558 A s P f h1 a). Qed.
Lemma lem7203595 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (a : A) : (term20 A s P f a) = (term21 A s P f a).
Proof. exact (eq_refl (term20 A s P f a)). Qed.
Lemma lem7203596 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term21 A s P f a.
Proof. exact (EQ_MP (@lem7203595 A s P f a) (@lem7203594 A a s P f h1)). Qed.
Lemma lem7203597 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem7203598 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A a s) : term22 A P f a.
Proof. exact (@lem7203596 A a s P f h1 (@lem7203597 A a s h2)). Qed.
Lemma lem7203599 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) : (term22 A P f a) = ((term22 A P f a) = True).
Proof. exact (@lem7 (term22 A P f a)). Qed.
Lemma lem7203600 {A : Type'} (P : real -> Prop) (f : A -> real) (a : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A a s) : (term22 A P f a) = True.
Proof. exact (EQ_MP (@lem7203599 A P f a) (@lem7203598 A P f a s h1 h2)). Qed.
Lemma lem7203609 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7203610 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7203609 p q p' q'). Qed.
Lemma lem7203611 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7203610 p q p'). Qed.
Lemma lem7203612 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : term26 A P s f.
Proof. exact (@lem7203611 (term12 A P) (term27 A P s f)). Qed.
Lemma lem7203613 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : term28 A P s f p'.
Proof. exact (@lem7203612 A P s f p'). Qed.
Lemma lem7203614 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : (term28 A P s f p') = (term29 A P s f p').
Proof. exact (eq_refl (term28 A P s f p')). Qed.
Lemma lem7203615 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) : term29 A P s f p'.
Proof. exact (EQ_MP (@lem7203614 A P s f p') (@lem7203613 A P s f p')). Qed.
Lemma lem7203616 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term30 A P s f p' q'.
Proof. exact (@lem7203615 A P s f p' q'). Qed.
Lemma lem7203617 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term30 A P s f p' q') = (term31 A P s f p' q').
Proof. exact (eq_refl (term30 A P s f p' q')). Qed.
Lemma lem7203618 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term31 A P s f p' q'.
Proof. exact (EQ_MP (@lem7203617 A P s f p' q') (@lem7203616 A P s f p' q')). Qed.
Lemma lem7203622 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7203623 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7203622 p q p' q'). Qed.
Lemma lem7203624 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7203623 p q p'). Qed.
Lemma lem7203625 {A : Type'} (P : real -> Prop) : term32 A P.
Proof. exact (@lem7203624 (term10 P) (term33 A P)). Qed.
Lemma lem7203626 {A : Type'} (P : real -> Prop) (p' : Prop) : term34 A P p'.
Proof. exact (@lem7203625 A P p'). Qed.
Lemma lem7203627 {A : Type'} (P : real -> Prop) (p' : Prop) : (term34 A P p') = (term35 A P p').
Proof. exact (eq_refl (term34 A P p')). Qed.
Lemma lem7203628 {A : Type'} (P : real -> Prop) (p' : Prop) : term35 A P p'.
Proof. exact (EQ_MP (@lem7203627 A P p') (@lem7203626 A P p')). Qed.
Lemma lem7203629 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : term36 A P p' q'.
Proof. exact (@lem7203628 A P p' q'). Qed.
Lemma lem7203630 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : (term36 A P p' q') = (term37 A P p' q').
Proof. exact (eq_refl (term36 A P p' q')). Qed.
Lemma lem7203631 {A : Type'} (P : real -> Prop) (p' : Prop) (q' : Prop) : term37 A P p' q'.
Proof. exact (EQ_MP (@lem7203630 A P p' q') (@lem7203629 A P p' q')). Qed.
Lemma lem7203643 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7203644 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7203643 p q p' q'). Qed.
Lemma lem7203645 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7203644 p q p'). Qed.
Lemma lem7203646 (P : real -> Prop) (x : real) (y : real) : term38 P x y.
Proof. exact (@lem7203645 (term18 x P y) (term19 P x y)). Qed.
Lemma lem7203647 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : term39 P x y p'.
Proof. exact (@lem7203646 P x y p'). Qed.
Lemma lem7203648 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : (term39 P x y p') = (term40 P x y p').
Proof. exact (eq_refl (term39 P x y p')). Qed.
Lemma lem7203649 (P : real -> Prop) (x : real) (y : real) (p' : Prop) : term40 P x y p'.
Proof. exact (EQ_MP (@lem7203648 P x y p') (@lem7203647 P x y p')). Qed.
Lemma lem7203650 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term41 P x y p' q'.
Proof. exact (@lem7203649 P x y p' q'). Qed.
Lemma lem7203651 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term41 P x y p' q') = (term42 P x y p' q').
Proof. exact (eq_refl (term41 P x y p' q')). Qed.
Lemma lem7203652 (P : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term42 P x y p' q'.
Proof. exact (EQ_MP (@lem7203651 P x y p' q') (@lem7203650 P x y p' q')). Qed.
Lemma lem7203655 (x : real) (P : real -> Prop) (y : real) : (term18 x P y) = (term18 x P y).
Proof. exact (eq_refl (term18 x P y)). Qed.
Lemma lem7203656 (x : real) (P : real -> Prop) (y : real) (q' : Prop) : term43 x P y q'.
Proof. exact (@lem7203652 P x y (term18 x P y) q'). Qed.
Lemma lem7203657 (x : real) (P : real -> Prop) (y : real) (q' : Prop) : term44 x P y q'.
Proof. exact (@lem7203656 x P y q' (@lem7203655 x P y)). Qed.
Lemma lem7203658 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : term18 x P y.
Proof. exact (h1). Qed.
Lemma lem7203659 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : P y.
Proof. exact (proj2 (@lem7203658 x P y h1)). Qed.
Lemma lem7203660 (P : real -> Prop) (y : real) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem7203662 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : P x.
Proof. exact (proj1 (@lem7203658 x P y h1)). Qed.
Lemma lem7203663 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7203666 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : term45 P x y.
Proof. exact (fun h0 : term18 x P y => @lem7203588 x P y h1 h0). Qed.
Lemma lem7203670 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : (P x) = True.
Proof. exact (EQ_MP (@lem7203663 P x) (@lem7203662 x P y h1)). Qed.
Lemma lem7203671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7203672 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : (term46 P x) = (and True).
Proof. exact (MK_COMB (@lem7203671) (@lem7203670 x P y h1)). Qed.
Lemma lem7203674 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : (P y) = True.
Proof. exact (EQ_MP (@lem7203660 P y) (@lem7203659 x P y h1)). Qed.
Lemma lem7203675 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : (term18 x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem7203672 x P y h1) (@lem7203674 x P y h1)). Qed.
Lemma lem7203677 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7203678 : (True /\ True) = True.
Proof. exact (@lem7203677 True). Qed.
Lemma lem7203679 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : (term18 x P y) = True.
Proof. exact (TRANS (@lem7203675 x P y h1) (@lem7203678)). Qed.
Lemma lem7203680 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : True = (term18 x P y).
Proof. exact (SYM (@lem7203679 x P y h1)). Qed.
Lemma lem7203681 (x : real) (P : real -> Prop) (y : real) (h1 : term18 x P y) : term18 x P y.
Proof. exact (EQ_MP (@lem7203680 x P y h1) (@lem0)). Qed.
Lemma lem7203682 (x : real) (P : real -> Prop) (y : real) (h1 : term10 P) (h2 : term18 x P y) : (term19 P x y) = True.
Proof. exact (@lem7203666 x y P h1 (@lem7203681 x P y h2)). Qed.
Lemma lem7203683 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : term45 P x y.
Proof. exact (fun h0 : term18 x P y => @lem7203682 x P y h1 h0). Qed.
Lemma lem7203684 (x : real) (P : real -> Prop) (y : real) : term47 x P y.
Proof. exact (@lem7203657 x P y True). Qed.
Lemma lem7203685 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : (term17 P x y) = (term48 x P y).
Proof. exact (@lem7203684 x P y (@lem7203683 x y P h1)). Qed.
Lemma lem7203687 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7203688 (x : real) (P : real -> Prop) (y : real) : (term48 x P y) = True.
Proof. exact (@lem7203687 (term18 x P y)). Qed.
Lemma lem7203689 (x : real) (y : real) (P : real -> Prop) (h1 : term10 P) : (term17 P x y) = True.
Proof. exact (TRANS (@lem7203685 x y P h1) (@lem7203688 x P y)). Qed.
Lemma lem7203690 (x : real) (P : real -> Prop) (h1 : term10 P) : (term49 P x) = term50.
Proof. exact (fun_ext (fun y : real => @lem7203689 x y P h1)). Qed.
Lemma lem7203691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7203692 (x : real) (P : real -> Prop) (h1 : term10 P) : (term15 P x) = term51.
Proof. exact (MK_COMB (@lem7203691) (@lem7203690 x P h1)). Qed.
Lemma lem7203694 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7203695 (t : Prop) : (term53 t) = t.
Proof. exact (@lem7203694 real t). Qed.
Lemma lem7203696 : term51 = True.
Proof. exact (@lem7203695 True). Qed.
Lemma lem7203697 (x : real) (P : real -> Prop) (h1 : term10 P) : (term15 P x) = True.
Proof. exact (TRANS (@lem7203692 x P h1) (@lem7203696)). Qed.
Lemma lem7203698 (P : real -> Prop) (h1 : term10 P) : (term54 P) = term50.
Proof. exact (fun_ext (fun x : real => @lem7203697 x P h1)). Qed.
Lemma lem7203699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7203700 (P : real -> Prop) (h1 : term10 P) : (term10 P) = term51.
Proof. exact (MK_COMB (@lem7203699) (@lem7203698 P h1)). Qed.
Lemma lem7203702 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7203703 (t : Prop) : (term53 t) = t.
Proof. exact (@lem7203702 real t). Qed.
Lemma lem7203704 : term51 = True.
Proof. exact (@lem7203703 True). Qed.
Lemma lem7203705 (P : real -> Prop) (h1 : term10 P) : (term10 P) = True.
Proof. exact (TRANS (@lem7203700 P h1) (@lem7203704)). Qed.
Lemma lem7203706 {A : Type'} (P : real -> Prop) (q' : Prop) : term55 A P q'.
Proof. exact (@lem7203631 A P True q'). Qed.
Lemma lem7203707 {A : Type'} (q' : Prop) (P : real -> Prop) (h1 : term10 P) : term56 A P q'.
Proof. exact (@lem7203706 A P q' (@lem7203705 P h1)). Qed.
Lemma lem7203856 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7203857 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7203856 p q p' q'). Qed.
Lemma lem7203858 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7203857 p q p'). Qed.
Lemma lem7203859 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) : term57 A P _96502 f.
Proof. exact (@lem7203858 (term58 A _96502 P f) (term59 A P _96502 f)). Qed.
Lemma lem7203860 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) : term60 A P _96502 f p'.
Proof. exact (@lem7203859 A P _96502 f p'). Qed.
Lemma lem7203861 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) : (term60 A P _96502 f p') = (term61 A P _96502 f p').
Proof. exact (eq_refl (term60 A P _96502 f p')). Qed.
Lemma lem7203862 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) : term61 A P _96502 f p'.
Proof. exact (EQ_MP (@lem7203861 A P _96502 f p') (@lem7203860 A P _96502 f p')). Qed.
Lemma lem7203863 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term62 A P _96502 f p' q'.
Proof. exact (@lem7203862 A P _96502 f p' q'). Qed.
Lemma lem7203864 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term62 A P _96502 f p' q') = (term63 A P _96502 f p' q').
Proof. exact (eq_refl (term62 A P _96502 f p' q')). Qed.
Lemma lem7203865 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term63 A P _96502 f p' q'.
Proof. exact (EQ_MP (@lem7203864 A P _96502 f p' q') (@lem7203863 A P _96502 f p' q')). Qed.
Lemma lem7203911 {A : Type'} (_96502 : A -> Prop) (P : real -> Prop) (f : A -> real) : (term58 A _96502 P f) = (term58 A _96502 P f).
Proof. exact (eq_refl (term58 A _96502 P f)). Qed.
Lemma lem7203912 {A : Type'} (_96502 : A -> Prop) (P : real -> Prop) (f : A -> real) (q' : Prop) : term64 A _96502 P f q'.
Proof. exact (@lem7203865 A P _96502 f (term58 A _96502 P f) q'). Qed.
Lemma lem7203913 {A : Type'} (_96502 : A -> Prop) (P : real -> Prop) (f : A -> real) (q' : Prop) : term65 A _96502 P f q'.
Proof. exact (@lem7203912 A _96502 P f q' (@lem7203911 A _96502 P f)). Qed.
Lemma lem7203947 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7203543 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7203948 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7203947 A). Qed.
Lemma lem7203949 {A : Type'} (_96502 : A -> Prop) : _96502 = _96502.
Proof. exact (eq_refl _96502). Qed.
Lemma lem7203950 {A : Type'} (_96502 : A -> Prop) : (@iterate real A real_add _96502) = (@sum A _96502).
Proof. exact (MK_COMB (@lem7203948 A) (@lem7203949 A _96502)). Qed.
Lemma lem7203951 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7203952 {A : Type'} (_96502 : A -> Prop) (f : A -> real) : (@iterate real A real_add _96502 f) = (@sum A _96502 f).
Proof. exact (MK_COMB (@lem7203950 A _96502) (@lem7203951 A f)). Qed.
Lemma lem7203953 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7203954 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) : (term59 A P _96502 f) = (term27 A P _96502 f).
Proof. exact (MK_COMB (@lem7203953 P) (@lem7203952 A _96502 f)). Qed.
Lemma lem7203955 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) : term66 A P _96502 f.
Proof. exact (fun h0 : term58 A _96502 P f => @lem7203954 A P _96502 f). Qed.
Lemma lem7203956 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) : term67 A P _96502 f.
Proof. exact (@lem7203913 A _96502 P f (term27 A P _96502 f)). Qed.
Lemma lem7203957 {A : Type'} (P : real -> Prop) (_96502 : A -> Prop) (f : A -> real) : (term68 A P _96502 f) = (term69 A P _96502 f).
Proof. exact (@lem7203956 A P _96502 f (@lem7203955 A P _96502 f)). Qed.
Lemma lem7204102 {A : Type'} (P : real -> Prop) (f : A -> real) : (term70 A P f) = (term71 A P f).
Proof. exact (fun_ext (fun _96502 : A -> Prop => @lem7203957 A P _96502 f)). Qed.
Lemma lem7204369 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7204370 {A : Type'} (P : real -> Prop) (f : A -> real) : (term72 A P f) = (term73 A P f).
Proof. exact (MK_COMB (@lem7204369 A) (@lem7204102 A P f)). Qed.
Lemma lem7204641 {A : Type'} (P : real -> Prop) : (term74 A P) = (term75 A P).
Proof. exact (fun_ext (fun f : A -> real => @lem7204370 A P f)). Qed.
Lemma lem7204912 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7204913 {A : Type'} (P : real -> Prop) : (term33 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem7204912 A) (@lem7204641 A P)). Qed.
Lemma lem7205188 {A : Type'} (P : real -> Prop) : term77 A P.
Proof. exact (fun h0 : True => @lem7204913 A P). Qed.
Lemma lem7205189 {A : Type'} (P : real -> Prop) (h1 : term10 P) : term78 A P.
Proof. exact (@lem7203707 A (term76 A P) P h1). Qed.
Lemma lem7205190 {A : Type'} (P : real -> Prop) (h1 : term10 P) : (term12 A P) = (term79 A P).
Proof. exact (@lem7205189 A P h1 (@lem7205188 A P)). Qed.
Lemma lem7205192 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7205193 {A : Type'} (P : real -> Prop) : (term79 A P) = (term76 A P).
Proof. exact (@lem7205192 (term76 A P)). Qed.
Lemma lem7205446 {A : Type'} (P : real -> Prop) (h1 : term10 P) : (term12 A P) = (term76 A P).
Proof. exact (TRANS (@lem7205190 A P h1) (@lem7205193 A P)). Qed.
Lemma lem7205447 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (q' : Prop) : term80 A s f P q'.
Proof. exact (@lem7203618 A P s f (term76 A P) q'). Qed.
Lemma lem7205448 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) (P : real -> Prop) (h1 : term10 P) : term81 A s f P q'.
Proof. exact (@lem7205447 A s f P q' (@lem7205446 A P h1)). Qed.
Lemma lem7205449 {A : Type'} (P : real -> Prop) (h1 : term76 A P) : term76 A P.
Proof. exact (h1). Qed.
Lemma lem7205450 {A : Type'} (f : A -> real) (P : real -> Prop) (h1 : term76 A P) : term82 A P f.
Proof. exact (@lem7205449 A P h1 f). Qed.
Lemma lem7205451 {A : Type'} (P : real -> Prop) (f : A -> real) : (term82 A P f) = (term73 A P f).
Proof. exact (eq_refl (term82 A P f)). Qed.
Lemma lem7205452 {A : Type'} (f : A -> real) (P : real -> Prop) (h1 : term76 A P) : term73 A P f.
Proof. exact (EQ_MP (@lem7205451 A P f) (@lem7205450 A f P h1)). Qed.
Lemma lem7205453 {A : Type'} (f : A -> real) (s : A -> Prop) (P : real -> Prop) (h1 : term76 A P) : term83 A P f s.
Proof. exact (@lem7205452 A f P h1 s). Qed.
Lemma lem7205454 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : (term83 A P f s) = (term69 A P s f).
Proof. exact (eq_refl (term83 A P f s)). Qed.
Lemma lem7205455 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term76 A P) : term69 A P s f.
Proof. exact (EQ_MP (@lem7205454 A P s f) (@lem7205453 A f s P h1)). Qed.
Lemma lem7205456 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term58 A s P f) : term58 A s P f.
Proof. exact (h1). Qed.
Lemma lem7205457 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term76 A P) (h2 : term58 A s P f) : term27 A P s f.
Proof. exact (@lem7205455 A s f P h1 (@lem7205456 A s P f h2)). Qed.
Lemma lem7205458 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : (term27 A P s f) = ((term27 A P s f) = True).
Proof. exact (@lem7 (term27 A P s f)). Qed.
Lemma lem7205459 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term76 A P) (h2 : term58 A s P f) : (term27 A P s f) = True.
Proof. exact (EQ_MP (@lem7205458 A P s f) (@lem7205457 A s P f h1 h2)). Qed.
Lemma lem7205466 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term76 A P) : term84 A P s f.
Proof. exact (fun h0 : term58 A s P f => @lem7205459 A s P f h1 h0). Qed.
Lemma lem7205467 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term76 A P) : term84 A P s f.
Proof. exact (@lem7205466 A s f P h1). Qed.
Lemma lem7205471 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7203564 A s) (@lem7203555 A s h1)). Qed.
Lemma lem7205472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7205473 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term85 A s) = (and True).
Proof. exact (MK_COMB (@lem7205472) (@lem7205471 A s h1)). Qed.
Lemma lem7205477 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem7203566 A s (@lem7203557 A s h1)). Qed.
Lemma lem7205478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7205479 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term8 A s) = (~ False).
Proof. exact (MK_COMB (@lem7205478) (@lem7205477 A s h1)). Qed.
Lemma lem7205481 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7205482 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term8 A s) = True.
Proof. exact (TRANS (@lem7205479 A s h1) (@lem7205481)). Qed.
Lemma lem7205483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7205484 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term86 A s) = (and True).
Proof. exact (MK_COMB (@lem7205483) (@lem7205482 A s h1)). Qed.
Lemma lem7205492 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7205493 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7205492 p q p' q'). Qed.
Lemma lem7205494 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7205493 p q p'). Qed.
Lemma lem7205495 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) : term87 A s P f x.
Proof. exact (@lem7205494 (@IN A x s) (term22 A P f x)). Qed.
Lemma lem7205496 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term88 A s P f x p'.
Proof. exact (@lem7205495 A s P f x p'). Qed.
Lemma lem7205497 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term88 A s P f x p') = (term89 A s P f x p').
Proof. exact (eq_refl (term88 A s P f x p')). Qed.
Lemma lem7205498 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) : term89 A s P f x p'.
Proof. exact (EQ_MP (@lem7205497 A s P f x p') (@lem7205496 A s P f x p')). Qed.
Lemma lem7205499 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term90 A s P f x p' q'.
Proof. exact (@lem7205498 A s P f x p' q'). Qed.
Lemma lem7205500 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term90 A s P f x p' q') = (term91 A s P f x p' q').
Proof. exact (eq_refl (term90 A s P f x p' q')). Qed.
Lemma lem7205501 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term91 A s P f x p' q'.
Proof. exact (EQ_MP (@lem7205500 A s P f x p' q') (@lem7205499 A s P f x p' q')). Qed.
Lemma lem7205502 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7205503 {A : Type'} (P : real -> Prop) (f : A -> real) (x : A) (s : A -> Prop) (q' : Prop) : term92 A P f x s q'.
Proof. exact (@lem7205501 A s P f x (@IN A x s) q'). Qed.
Lemma lem7205504 {A : Type'} (P : real -> Prop) (f : A -> real) (x : A) (s : A -> Prop) (q' : Prop) : term93 A P f x s q'.
Proof. exact (@lem7205503 A P f x s q' (@lem7205502 A x s)). Qed.
Lemma lem7205505 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7205506 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7205509 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term94 A s P f a.
Proof. exact (fun h0 : @IN A a s => @lem7203600 A P f a s h1 h0). Qed.
Lemma lem7205510 {A : Type'} (a : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term94 A s P f a.
Proof. exact (@lem7205509 A a s P f h1). Qed.
Lemma lem7205511 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term94 A s P f x.
Proof. exact (@lem7205510 A x s P f h1). Qed.
Lemma lem7205513 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7205506 A x s) (@lem7205505 A x s h1)). Qed.
Lemma lem7205514 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem7205513 A x s h1)). Qed.
Lemma lem7205515 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7205514 A x s h1) (@lem0)). Qed.
Lemma lem7205516 {A : Type'} (P : real -> Prop) (f : A -> real) (x : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A x s) : (term22 A P f x) = True.
Proof. exact (@lem7205511 A x s P f h1 (@lem7205515 A x s h2)). Qed.
Lemma lem7205517 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : term94 A s P f x.
Proof. exact (fun h0 : @IN A x s => @lem7205516 A P f x s h1 h0). Qed.
Lemma lem7205518 {A : Type'} (P : real -> Prop) (f : A -> real) (x : A) (s : A -> Prop) : term95 A P f x s.
Proof. exact (@lem7205504 A P f x s True). Qed.
Lemma lem7205519 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : (term21 A s P f x) = (term96 A x s).
Proof. exact (@lem7205518 A P f x s (@lem7205517 A x s P f h1)). Qed.
Lemma lem7205521 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7205522 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = True.
Proof. exact (@lem7205521 (@IN A x s)). Qed.
Lemma lem7205523 {A : Type'} (x : A) (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : (term21 A s P f x) = True.
Proof. exact (TRANS (@lem7205519 A x s P f h1) (@lem7205522 A x s)). Qed.
Lemma lem7205524 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : (term97 A s P f) = (term98 A).
Proof. exact (fun_ext (fun x : A => @lem7205523 A x s P f h1)). Qed.
Lemma lem7205525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7205526 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : (term9 A s P f) = (term99 A).
Proof. exact (MK_COMB (@lem7205525 A) (@lem7205524 A s P f h1)). Qed.
Lemma lem7205528 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7205529 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem7205528 A t). Qed.
Lemma lem7205530 {A : Type'} : (term99 A) = True.
Proof. exact (@lem7205529 A True). Qed.
Lemma lem7205531 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term9 A s P f) : (term9 A s P f) = True.
Proof. exact (TRANS (@lem7205526 A s P f h1) (@lem7205530 A)). Qed.
Lemma lem7205532 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term8 A s) : (term100 A s P f) = (True /\ True).
Proof. exact (MK_COMB (@lem7205484 A s h2) (@lem7205531 A s P f h1)). Qed.
Lemma lem7205534 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7205535 : (True /\ True) = True.
Proof. exact (@lem7205534 True). Qed.
Lemma lem7205536 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term8 A s) : (term100 A s P f) = True.
Proof. exact (TRANS (@lem7205532 A P f s h1 h2) (@lem7205535)). Qed.
Lemma lem7205537 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : (term58 A s P f) = (True /\ True).
Proof. exact (MK_COMB (@lem7205473 A s h2) (@lem7205536 A P f s h1 h3)). Qed.
Lemma lem7205539 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7205540 : (True /\ True) = True.
Proof. exact (@lem7205539 True). Qed.
Lemma lem7205541 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : (term58 A s P f) = True.
Proof. exact (TRANS (@lem7205537 A P f s h1 h2 h3) (@lem7205540)). Qed.
Lemma lem7205542 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : True = (term58 A s P f).
Proof. exact (SYM (@lem7205541 A P f s h1 h2 h3)). Qed.
Lemma lem7205543 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : term58 A s P f.
Proof. exact (EQ_MP (@lem7205542 A P f s h1 h2 h3) (@lem0)). Qed.
Lemma lem7205544 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term76 A P) (h3 : @FINITE A s) (h4 : term8 A s) : (term27 A P s f) = True.
Proof. exact (@lem7205467 A s f P h2 (@lem7205543 A P f s h1 h3 h4)). Qed.
Lemma lem7205545 {A : Type'} (P : real -> Prop) (f : A -> real) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : term101 A P s f.
Proof. exact (fun h0 : term76 A P => @lem7205544 A f P s h1 h0 h2 h3). Qed.
Lemma lem7205546 {A : Type'} (s : A -> Prop) (f : A -> real) (P : real -> Prop) (h1 : term10 P) : term102 A s f P.
Proof. exact (@lem7205448 A s f True P h1). Qed.
Lemma lem7205547 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term103 A P s f) = (term104 A P).
Proof. exact (@lem7205546 A s f P h2 (@lem7205545 A P f s h1 h3 h4)). Qed.
Lemma lem7205549 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7205550 {A : Type'} (P : real -> Prop) : (term104 A P) = True.
Proof. exact (@lem7205549 (term76 A P)). Qed.
Lemma lem7205551 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term103 A P s f) = True.
Proof. exact (TRANS (@lem7205547 A f P s h1 h2 h3 h4) (@lem7205550 A P)). Qed.
Lemma lem7205552 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : True = (term103 A P s f).
Proof. exact (SYM (@lem7205551 A f P s h1 h2 h3 h4)). Qed.
Lemma lem7205553 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term103 A P s f.
Proof. exact (EQ_MP (@lem7205552 A f P s h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem7205554 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term4 A) (h3 : term10 P) (h4 : @FINITE A s) (h5 : term8 A s) : term27 A P s f.
Proof. exact (@lem7205553 A f P s h1 h3 h4 h5 (@lem7203563 A P h2)). Qed.
Lemma lem7205555 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term105 A P s f.
Proof. exact (fun h0 : term4 A => @lem7205554 A f P s h1 h0 h2 h3 h4). Qed.
Lemma lem7205556 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (@lem7205555 A f P s h1 h2 h3 h4 (@lem7203552 A)). Qed.
Lemma lem7205557 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term6 A s P f.
Proof. exact (proj2 (@lem7203553 A s P f h1)). Qed.
Lemma lem7205558 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : @FINITE A s.
Proof. exact (proj1 (@lem7203553 A s P f h1)). Qed.
Lemma lem7205559 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term7 A s P f.
Proof. exact (proj2 (@lem7203554 A s P f h1)). Qed.
Lemma lem7205560 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term6 A s P f) : term8 A s.
Proof. exact (proj1 (@lem7203554 A s P f h1)). Qed.
Lemma lem7205561 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 A s P f) : term9 A s P f.
Proof. exact (proj2 (@lem7203556 A s P f h1)). Qed.
Lemma lem7205562 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term7 A s P f) : term10 P.
Proof. exact (proj1 (@lem7203556 A s P f h1)). Qed.
Lemma lem7205563 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term9 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term9 A s P f => @lem7205556 A f P s h1 h2 h3 h4) (fun h5 : term27 A P s f => @lem7203558 A s P f h1)). Qed.
Lemma lem7205564 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205563 A f P s h1 h2 h3 h4) (@lem7203558 A s P f h1)). Qed.
Lemma lem7205565 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term10 P) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term10 P => @lem7205564 A f P s h1 h2 h3 h4) (fun h5 : term27 A P s f => @lem7203559 P h2)). Qed.
Lemma lem7205566 {A : Type'} (f : A -> real) (P : real -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205565 A f P s h1 h2 h3 h4) (@lem7203559 P h2)). Qed.
Lemma lem7205567 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term10 P) (h2 : @FINITE A s) (h3 : term8 A s) (h4 : term7 A s P f) : (term9 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term9 A s P f => @lem7205566 A f P s h5 h1 h2 h3) (fun h5 : term27 A P s f => @lem7205561 A s P f h4)). Qed.
Lemma lem7205568 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term10 P) (h2 : @FINITE A s) (h3 : term8 A s) (h4 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205567 A s P f h1 h2 h3 h4) (@lem7205561 A s P f h4)). Qed.
Lemma lem7205569 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : (term10 P) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term10 P => @lem7205568 A s P f h4 h1 h2 h3) (fun h4 : term27 A P s f => @lem7205562 A s P f h3)). Qed.
Lemma lem7205570 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205569 A s P f h1 h2 h3) (@lem7205562 A s P f h3)). Qed.
Lemma lem7205571 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : (term8 A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s => @lem7205570 A s P f h1 h2 h3) (fun h4 : term27 A P s f => @lem7203557 A s h2)). Qed.
Lemma lem7205572 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205571 A s P f h1 h2 h3) (@lem7203557 A s h2)). Qed.
Lemma lem7205573 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term6 A s P f) : (term7 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term7 A s P f => @lem7205572 A s P f h1 h2 h4) (fun h4 : term27 A P s f => @lem7205559 A s P f h3)). Qed.
Lemma lem7205574 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205573 A s P f h1 h2 h3) (@lem7205559 A s P f h3)). Qed.
Lemma lem7205575 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term6 A s P f) : (term8 A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : term8 A s => @lem7205574 A s P f h1 h3 h2) (fun h3 : term27 A P s f => @lem7205560 A s P f h2)). Qed.
Lemma lem7205576 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205575 A s P f h1 h2) (@lem7205560 A s P f h2)). Qed.
Lemma lem7205577 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term6 A s P f) : (@FINITE A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7205576 A s P f h1 h2) (fun h3 : term27 A P s f => @lem7203555 A s h1)). Qed.
Lemma lem7205578 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205577 A s P f h1 h2) (@lem7203555 A s h1)). Qed.
Lemma lem7205579 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term5 A s P f) : (term6 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : term6 A s P f => @lem7205578 A s P f h1 h3) (fun h3 : term27 A P s f => @lem7205557 A s P f h2)). Qed.
Lemma lem7205580 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term5 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205579 A s P f h1 h2) (@lem7205557 A s P f h2)). Qed.
Lemma lem7205581 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : (@FINITE A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7205580 A s P f h2 h1) (fun h2 : term27 A P s f => @lem7205558 A s P f h1)). Qed.
Lemma lem7205582 {A : Type'} (s : A -> Prop) (P : real -> Prop) (f : A -> real) (h1 : term5 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7205581 A s P f h1) (@lem7205558 A s P f h1)). Qed.
Lemma lem7205583 {A : Type'} (P : real -> Prop) (s : A -> Prop) (f : A -> real) : term106 A P s f.
Proof. exact (fun h0 : term5 A s P f => @lem7205582 A s P f h0). Qed.
Lemma lem7205588 {A : Type'} (P : real -> Prop) (f : A -> real) : term107 A P f.
Proof. exact (fun s : A -> Prop => @lem7205583 A P s f). Qed.
Lemma lem7205593 {A : Type'} (P : real -> Prop) : term108 A P.
Proof. exact (fun f : A -> real => @lem7205588 A P f). Qed.
Lemma lem7205598 {A : Type'} : term109 A.
Proof. exact (fun P : real -> Prop => @lem7205593 A P). Qed.
