Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLOSED_NONEMPTY_term_abbrevs.
Require Import ITERATE_CLOSED_NONEMPTY_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import nsum_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7034543 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (h1). Qed.
Lemma lem7034544 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (SYM (@lem7034543 _126417 h1)). Qed.
Lemma lem7034545 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (h1). Qed.
Lemma lem7034546 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (SYM (@lem7034545 _126417 h1)). Qed.
Lemma lem7034547 {_126417 : Type'} : ((@nsum _126417) = (@iterate nat _126417 Nat.add)) = ((@iterate nat _126417 Nat.add) = (@nsum _126417)).
Proof. exact (prop_ext (fun h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add) => @lem7034544 _126417 h1) (fun h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417) => @lem7034546 _126417 h1)). Qed.
Lemma lem7034549 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5809499 A B op). Qed.
Lemma lem7034550 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem7034553 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem7034550 A B op) (@lem7034549 A B op)). Qed.
Lemma lem7034554 {A : Type'} (op : type1606) : term2 A op.
Proof. exact (@lem7034553 A nat op). Qed.
Lemma lem7034555 {A : Type'} : term3 A.
Proof. exact (@lem7034554 A Nat.add). Qed.
Lemma lem7034556 {A : Type'} : term4 A.
Proof. exact (@lem7034555 A (@lem6924403)). Qed.
Lemma lem7034557 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term5 A s P f.
Proof. exact (h1). Qed.
Lemma lem7034558 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term6 A s P f.
Proof. exact (h1). Qed.
Lemma lem7034559 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7034560 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 A s P f) : term7 A s P f.
Proof. exact (h1). Qed.
Lemma lem7034561 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : term8 A s.
Proof. exact (h1). Qed.
Lemma lem7034562 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term9 A s P f.
Proof. exact (h1). Qed.
Lemma lem7034563 (P : nat -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem7034564 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7034565 {A : Type'} (P : nat -> Prop) (h1 : term4 A) : term11 A P.
Proof. exact (@lem7034564 A h1 P). Qed.
Lemma lem7034566 {A : Type'} (P : nat -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem7034567 {A : Type'} (P : nat -> Prop) (h1 : term4 A) : term12 A P.
Proof. exact (EQ_MP (@lem7034566 A P) (@lem7034565 A P h1)). Qed.
Lemma lem7034568 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7034570 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem7034583 (x : nat) (P : nat -> Prop) (h1 : term10 P) : term14 P x.
Proof. exact (@lem7034563 P h1 x). Qed.
Lemma lem7034584 (P : nat -> Prop) (x : nat) : (term14 P x) = (term15 P x).
Proof. exact (eq_refl (term14 P x)). Qed.
Lemma lem7034585 (x : nat) (P : nat -> Prop) (h1 : term10 P) : term15 P x.
Proof. exact (EQ_MP (@lem7034584 P x) (@lem7034583 x P h1)). Qed.
Lemma lem7034586 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : term16 P x y.
Proof. exact (@lem7034585 x P h1 y). Qed.
Lemma lem7034587 (P : nat -> Prop) (x : nat) (y : nat) : (term16 P x y) = (term17 P x y).
Proof. exact (eq_refl (term16 P x y)). Qed.
Lemma lem7034588 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : term17 P x y.
Proof. exact (EQ_MP (@lem7034587 P x y) (@lem7034586 x y P h1)). Qed.
Lemma lem7034589 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : term18 x P y.
Proof. exact (h1). Qed.
Lemma lem7034590 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term10 P) (h2 : term18 x P y) : term19 P x y.
Proof. exact (@lem7034588 x y P h1 (@lem7034589 x P y h2)). Qed.
Lemma lem7034591 (P : nat -> Prop) (x : nat) (y : nat) : (term19 P x y) = ((term19 P x y) = True).
Proof. exact (@lem7 (term19 P x y)). Qed.
Lemma lem7034592 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term10 P) (h2 : term18 x P y) : (term19 P x y) = True.
Proof. exact (EQ_MP (@lem7034591 P x y) (@lem7034590 x P y h1 h2)). Qed.
Lemma lem7034598 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term20 A s P f a.
Proof. exact (@lem7034562 A s P f h1 a). Qed.
Lemma lem7034599 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (a : A) : (term20 A s P f a) = (term21 A s P f a).
Proof. exact (eq_refl (term20 A s P f a)). Qed.
Lemma lem7034600 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term21 A s P f a.
Proof. exact (EQ_MP (@lem7034599 A s P f a) (@lem7034598 A a s P f h1)). Qed.
Lemma lem7034601 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem7034602 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A a s) : term22 A P f a.
Proof. exact (@lem7034600 A a s P f h1 (@lem7034601 A a s h2)). Qed.
Lemma lem7034603 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) : (term22 A P f a) = ((term22 A P f a) = True).
Proof. exact (@lem7 (term22 A P f a)). Qed.
Lemma lem7034604 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A a s) : (term22 A P f a) = True.
Proof. exact (EQ_MP (@lem7034603 A P f a) (@lem7034602 A P f a s h1 h2)). Qed.
Lemma lem7034613 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7034614 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7034613 p q p' q'). Qed.
Lemma lem7034615 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7034614 p q p'). Qed.
Lemma lem7034616 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : term26 A P s f.
Proof. exact (@lem7034615 (term12 A P) (term27 A P s f)). Qed.
Lemma lem7034617 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : term28 A P s f p'.
Proof. exact (@lem7034616 A P s f p'). Qed.
Lemma lem7034618 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : (term28 A P s f p') = (term29 A P s f p').
Proof. exact (eq_refl (term28 A P s f p')). Qed.
Lemma lem7034619 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : term29 A P s f p'.
Proof. exact (EQ_MP (@lem7034618 A P s f p') (@lem7034617 A P s f p')). Qed.
Lemma lem7034620 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term30 A P s f p' q'.
Proof. exact (@lem7034619 A P s f p' q'). Qed.
Lemma lem7034621 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term30 A P s f p' q') = (term31 A P s f p' q').
Proof. exact (eq_refl (term30 A P s f p' q')). Qed.
Lemma lem7034622 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term31 A P s f p' q'.
Proof. exact (EQ_MP (@lem7034621 A P s f p' q') (@lem7034620 A P s f p' q')). Qed.
Lemma lem7034626 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7034627 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7034626 p q p' q'). Qed.
Lemma lem7034628 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7034627 p q p'). Qed.
Lemma lem7034629 {A : Type'} (P : nat -> Prop) : term32 A P.
Proof. exact (@lem7034628 (term10 P) (term33 A P)). Qed.
Lemma lem7034630 {A : Type'} (P : nat -> Prop) (p' : Prop) : term34 A P p'.
Proof. exact (@lem7034629 A P p'). Qed.
Lemma lem7034631 {A : Type'} (P : nat -> Prop) (p' : Prop) : (term34 A P p') = (term35 A P p').
Proof. exact (eq_refl (term34 A P p')). Qed.
Lemma lem7034632 {A : Type'} (P : nat -> Prop) (p' : Prop) : term35 A P p'.
Proof. exact (EQ_MP (@lem7034631 A P p') (@lem7034630 A P p')). Qed.
Lemma lem7034633 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : term36 A P p' q'.
Proof. exact (@lem7034632 A P p' q'). Qed.
Lemma lem7034634 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term36 A P p' q') = (term37 A P p' q').
Proof. exact (eq_refl (term36 A P p' q')). Qed.
Lemma lem7034635 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : term37 A P p' q'.
Proof. exact (EQ_MP (@lem7034634 A P p' q') (@lem7034633 A P p' q')). Qed.
Lemma lem7034647 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7034648 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7034647 p q p' q'). Qed.
Lemma lem7034649 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7034648 p q p'). Qed.
Lemma lem7034650 (P : nat -> Prop) (x : nat) (y : nat) : term38 P x y.
Proof. exact (@lem7034649 (term18 x P y) (term19 P x y)). Qed.
Lemma lem7034651 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : term39 P x y p'.
Proof. exact (@lem7034650 P x y p'). Qed.
Lemma lem7034652 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : (term39 P x y p') = (term40 P x y p').
Proof. exact (eq_refl (term39 P x y p')). Qed.
Lemma lem7034653 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : term40 P x y p'.
Proof. exact (EQ_MP (@lem7034652 P x y p') (@lem7034651 P x y p')). Qed.
Lemma lem7034654 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term41 P x y p' q'.
Proof. exact (@lem7034653 P x y p' q'). Qed.
Lemma lem7034655 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : (term41 P x y p' q') = (term42 P x y p' q').
Proof. exact (eq_refl (term41 P x y p' q')). Qed.
Lemma lem7034656 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term42 P x y p' q'.
Proof. exact (EQ_MP (@lem7034655 P x y p' q') (@lem7034654 P x y p' q')). Qed.
Lemma lem7034659 (x : nat) (P : nat -> Prop) (y : nat) : (term18 x P y) = (term18 x P y).
Proof. exact (eq_refl (term18 x P y)). Qed.
Lemma lem7034660 (x : nat) (P : nat -> Prop) (y : nat) (q' : Prop) : term43 x P y q'.
Proof. exact (@lem7034656 P x y (term18 x P y) q'). Qed.
Lemma lem7034661 (x : nat) (P : nat -> Prop) (y : nat) (q' : Prop) : term44 x P y q'.
Proof. exact (@lem7034660 x P y q' (@lem7034659 x P y)). Qed.
Lemma lem7034662 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : term18 x P y.
Proof. exact (h1). Qed.
Lemma lem7034663 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : P y.
Proof. exact (proj2 (@lem7034662 x P y h1)). Qed.
Lemma lem7034664 (P : nat -> Prop) (y : nat) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem7034666 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : P x.
Proof. exact (proj1 (@lem7034662 x P y h1)). Qed.
Lemma lem7034667 (P : nat -> Prop) (x : nat) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7034670 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : term45 P x y.
Proof. exact (fun h0 : term18 x P y => @lem7034592 x P y h1 h0). Qed.
Lemma lem7034674 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : (P x) = True.
Proof. exact (EQ_MP (@lem7034667 P x) (@lem7034666 x P y h1)). Qed.
Lemma lem7034675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7034676 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : (term46 P x) = (and True).
Proof. exact (MK_COMB (@lem7034675) (@lem7034674 x P y h1)). Qed.
Lemma lem7034678 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : (P y) = True.
Proof. exact (EQ_MP (@lem7034664 P y) (@lem7034663 x P y h1)). Qed.
Lemma lem7034679 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : (term18 x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem7034676 x P y h1) (@lem7034678 x P y h1)). Qed.
Lemma lem7034681 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7034682 : (True /\ True) = True.
Proof. exact (@lem7034681 True). Qed.
Lemma lem7034683 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : (term18 x P y) = True.
Proof. exact (TRANS (@lem7034679 x P y h1) (@lem7034682)). Qed.
Lemma lem7034684 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : True = (term18 x P y).
Proof. exact (SYM (@lem7034683 x P y h1)). Qed.
Lemma lem7034685 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term18 x P y) : term18 x P y.
Proof. exact (EQ_MP (@lem7034684 x P y h1) (@lem0)). Qed.
Lemma lem7034686 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term10 P) (h2 : term18 x P y) : (term19 P x y) = True.
Proof. exact (@lem7034670 x y P h1 (@lem7034685 x P y h2)). Qed.
Lemma lem7034687 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : term45 P x y.
Proof. exact (fun h0 : term18 x P y => @lem7034686 x P y h1 h0). Qed.
Lemma lem7034688 (x : nat) (P : nat -> Prop) (y : nat) : term47 x P y.
Proof. exact (@lem7034661 x P y True). Qed.
Lemma lem7034689 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : (term17 P x y) = (term48 x P y).
Proof. exact (@lem7034688 x P y (@lem7034687 x y P h1)). Qed.
Lemma lem7034691 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7034692 (x : nat) (P : nat -> Prop) (y : nat) : (term48 x P y) = True.
Proof. exact (@lem7034691 (term18 x P y)). Qed.
Lemma lem7034693 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term10 P) : (term17 P x y) = True.
Proof. exact (TRANS (@lem7034689 x y P h1) (@lem7034692 x P y)). Qed.
Lemma lem7034694 (x : nat) (P : nat -> Prop) (h1 : term10 P) : (term49 P x) = term50.
Proof. exact (fun_ext (fun y : nat => @lem7034693 x y P h1)). Qed.
Lemma lem7034695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7034696 (x : nat) (P : nat -> Prop) (h1 : term10 P) : (term15 P x) = term51.
Proof. exact (MK_COMB (@lem7034695) (@lem7034694 x P h1)). Qed.
Lemma lem7034698 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7034699 (t : Prop) : (term53 t) = t.
Proof. exact (@lem7034698 nat t). Qed.
Lemma lem7034700 : term51 = True.
Proof. exact (@lem7034699 True). Qed.
Lemma lem7034701 (x : nat) (P : nat -> Prop) (h1 : term10 P) : (term15 P x) = True.
Proof. exact (TRANS (@lem7034696 x P h1) (@lem7034700)). Qed.
Lemma lem7034702 (P : nat -> Prop) (h1 : term10 P) : (term54 P) = term50.
Proof. exact (fun_ext (fun x : nat => @lem7034701 x P h1)). Qed.
Lemma lem7034703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7034704 (P : nat -> Prop) (h1 : term10 P) : (term10 P) = term51.
Proof. exact (MK_COMB (@lem7034703) (@lem7034702 P h1)). Qed.
Lemma lem7034706 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7034707 (t : Prop) : (term53 t) = t.
Proof. exact (@lem7034706 nat t). Qed.
Lemma lem7034708 : term51 = True.
Proof. exact (@lem7034707 True). Qed.
Lemma lem7034709 (P : nat -> Prop) (h1 : term10 P) : (term10 P) = True.
Proof. exact (TRANS (@lem7034704 P h1) (@lem7034708)). Qed.
Lemma lem7034710 {A : Type'} (P : nat -> Prop) (q' : Prop) : term55 A P q'.
Proof. exact (@lem7034635 A P True q'). Qed.
Lemma lem7034711 {A : Type'} (q' : Prop) (P : nat -> Prop) (h1 : term10 P) : term56 A P q'.
Proof. exact (@lem7034710 A P q' (@lem7034709 P h1)). Qed.
Lemma lem7034860 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7034861 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7034860 p q p' q'). Qed.
Lemma lem7034862 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7034861 p q p'). Qed.
Lemma lem7034863 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) : term57 A P _93902 f.
Proof. exact (@lem7034862 (term58 A _93902 P f) (term59 A P _93902 f)). Qed.
Lemma lem7034864 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) : term60 A P _93902 f p'.
Proof. exact (@lem7034863 A P _93902 f p'). Qed.
Lemma lem7034865 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) : (term60 A P _93902 f p') = (term61 A P _93902 f p').
Proof. exact (eq_refl (term60 A P _93902 f p')). Qed.
Lemma lem7034866 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) : term61 A P _93902 f p'.
Proof. exact (EQ_MP (@lem7034865 A P _93902 f p') (@lem7034864 A P _93902 f p')). Qed.
Lemma lem7034867 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term62 A P _93902 f p' q'.
Proof. exact (@lem7034866 A P _93902 f p' q'). Qed.
Lemma lem7034868 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term62 A P _93902 f p' q') = (term63 A P _93902 f p' q').
Proof. exact (eq_refl (term62 A P _93902 f p' q')). Qed.
Lemma lem7034869 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term63 A P _93902 f p' q'.
Proof. exact (EQ_MP (@lem7034868 A P _93902 f p' q') (@lem7034867 A P _93902 f p' q')). Qed.
Lemma lem7034915 {A : Type'} (_93902 : A -> Prop) (P : nat -> Prop) (f : A -> nat) : (term58 A _93902 P f) = (term58 A _93902 P f).
Proof. exact (eq_refl (term58 A _93902 P f)). Qed.
Lemma lem7034916 {A : Type'} (_93902 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (q' : Prop) : term64 A _93902 P f q'.
Proof. exact (@lem7034869 A P _93902 f (term58 A _93902 P f) q'). Qed.
Lemma lem7034917 {A : Type'} (_93902 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (q' : Prop) : term65 A _93902 P f q'.
Proof. exact (@lem7034916 A _93902 P f q' (@lem7034915 A _93902 P f)). Qed.
Lemma lem7034951 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7034547 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7034952 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7034951 A). Qed.
Lemma lem7034953 {A : Type'} (_93902 : A -> Prop) : _93902 = _93902.
Proof. exact (eq_refl _93902). Qed.
Lemma lem7034954 {A : Type'} (_93902 : A -> Prop) : (@iterate nat A Nat.add _93902) = (@nsum A _93902).
Proof. exact (MK_COMB (@lem7034952 A) (@lem7034953 A _93902)). Qed.
Lemma lem7034955 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7034956 {A : Type'} (_93902 : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add _93902 f) = (@nsum A _93902 f).
Proof. exact (MK_COMB (@lem7034954 A _93902) (@lem7034955 A f)). Qed.
Lemma lem7034957 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7034958 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) : (term59 A P _93902 f) = (term27 A P _93902 f).
Proof. exact (MK_COMB (@lem7034957 P) (@lem7034956 A _93902 f)). Qed.
Lemma lem7034959 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) : term66 A P _93902 f.
Proof. exact (fun h0 : term58 A _93902 P f => @lem7034958 A P _93902 f). Qed.
Lemma lem7034960 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) : term67 A P _93902 f.
Proof. exact (@lem7034917 A _93902 P f (term27 A P _93902 f)). Qed.
Lemma lem7034961 {A : Type'} (P : nat -> Prop) (_93902 : A -> Prop) (f : A -> nat) : (term68 A P _93902 f) = (term69 A P _93902 f).
Proof. exact (@lem7034960 A P _93902 f (@lem7034959 A P _93902 f)). Qed.
Lemma lem7035106 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term70 A P f) = (term71 A P f).
Proof. exact (fun_ext (fun _93902 : A -> Prop => @lem7034961 A P _93902 f)). Qed.
Lemma lem7035373 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7035374 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term72 A P f) = (term73 A P f).
Proof. exact (MK_COMB (@lem7035373 A) (@lem7035106 A P f)). Qed.
Lemma lem7035645 {A : Type'} (P : nat -> Prop) : (term74 A P) = (term75 A P).
Proof. exact (fun_ext (fun f : A -> nat => @lem7035374 A P f)). Qed.
Lemma lem7035916 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7035917 {A : Type'} (P : nat -> Prop) : (term33 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem7035916 A) (@lem7035645 A P)). Qed.
Lemma lem7036192 {A : Type'} (P : nat -> Prop) : term77 A P.
Proof. exact (fun h0 : True => @lem7035917 A P). Qed.
Lemma lem7036193 {A : Type'} (P : nat -> Prop) (h1 : term10 P) : term78 A P.
Proof. exact (@lem7034711 A (term76 A P) P h1). Qed.
Lemma lem7036194 {A : Type'} (P : nat -> Prop) (h1 : term10 P) : (term12 A P) = (term79 A P).
Proof. exact (@lem7036193 A P h1 (@lem7036192 A P)). Qed.
Lemma lem7036196 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7036197 {A : Type'} (P : nat -> Prop) : (term79 A P) = (term76 A P).
Proof. exact (@lem7036196 (term76 A P)). Qed.
Lemma lem7036450 {A : Type'} (P : nat -> Prop) (h1 : term10 P) : (term12 A P) = (term76 A P).
Proof. exact (TRANS (@lem7036194 A P h1) (@lem7036197 A P)). Qed.
Lemma lem7036451 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (q' : Prop) : term80 A s f P q'.
Proof. exact (@lem7034622 A P s f (term76 A P) q'). Qed.
Lemma lem7036452 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) (P : nat -> Prop) (h1 : term10 P) : term81 A s f P q'.
Proof. exact (@lem7036451 A s f P q' (@lem7036450 A P h1)). Qed.
Lemma lem7036453 {A : Type'} (P : nat -> Prop) (h1 : term76 A P) : term76 A P.
Proof. exact (h1). Qed.
Lemma lem7036454 {A : Type'} (f : A -> nat) (P : nat -> Prop) (h1 : term76 A P) : term82 A P f.
Proof. exact (@lem7036453 A P h1 f). Qed.
Lemma lem7036455 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term82 A P f) = (term73 A P f).
Proof. exact (eq_refl (term82 A P f)). Qed.
Lemma lem7036456 {A : Type'} (f : A -> nat) (P : nat -> Prop) (h1 : term76 A P) : term73 A P f.
Proof. exact (EQ_MP (@lem7036455 A P f) (@lem7036454 A f P h1)). Qed.
Lemma lem7036457 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : nat -> Prop) (h1 : term76 A P) : term83 A P f s.
Proof. exact (@lem7036456 A f P h1 s). Qed.
Lemma lem7036458 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : (term83 A P f s) = (term69 A P s f).
Proof. exact (eq_refl (term83 A P f s)). Qed.
Lemma lem7036459 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term76 A P) : term69 A P s f.
Proof. exact (EQ_MP (@lem7036458 A P s f) (@lem7036457 A f s P h1)). Qed.
Lemma lem7036460 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term58 A s P f) : term58 A s P f.
Proof. exact (h1). Qed.
Lemma lem7036461 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term76 A P) (h2 : term58 A s P f) : term27 A P s f.
Proof. exact (@lem7036459 A s f P h1 (@lem7036460 A s P f h2)). Qed.
Lemma lem7036462 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : (term27 A P s f) = ((term27 A P s f) = True).
Proof. exact (@lem7 (term27 A P s f)). Qed.
Lemma lem7036463 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term76 A P) (h2 : term58 A s P f) : (term27 A P s f) = True.
Proof. exact (EQ_MP (@lem7036462 A P s f) (@lem7036461 A s P f h1 h2)). Qed.
Lemma lem7036470 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term76 A P) : term84 A P s f.
Proof. exact (fun h0 : term58 A s P f => @lem7036463 A s P f h1 h0). Qed.
Lemma lem7036471 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term76 A P) : term84 A P s f.
Proof. exact (@lem7036470 A s f P h1). Qed.
Lemma lem7036475 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7034568 A s) (@lem7034559 A s h1)). Qed.
Lemma lem7036476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7036477 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term85 A s) = (and True).
Proof. exact (MK_COMB (@lem7036476) (@lem7036475 A s h1)). Qed.
Lemma lem7036481 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem7034570 A s (@lem7034561 A s h1)). Qed.
Lemma lem7036482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7036483 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term8 A s) = (~ False).
Proof. exact (MK_COMB (@lem7036482) (@lem7036481 A s h1)). Qed.
Lemma lem7036485 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7036486 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term8 A s) = True.
Proof. exact (TRANS (@lem7036483 A s h1) (@lem7036485)). Qed.
Lemma lem7036487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7036488 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : (term86 A s) = (and True).
Proof. exact (MK_COMB (@lem7036487) (@lem7036486 A s h1)). Qed.
Lemma lem7036496 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7036497 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7036496 p q p' q'). Qed.
Lemma lem7036498 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7036497 p q p'). Qed.
Lemma lem7036499 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : term87 A s P f x.
Proof. exact (@lem7036498 (@IN A x s) (term22 A P f x)). Qed.
Lemma lem7036500 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term88 A s P f x p'.
Proof. exact (@lem7036499 A s P f x p'). Qed.
Lemma lem7036501 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term88 A s P f x p') = (term89 A s P f x p').
Proof. exact (eq_refl (term88 A s P f x p')). Qed.
Lemma lem7036502 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term89 A s P f x p'.
Proof. exact (EQ_MP (@lem7036501 A s P f x p') (@lem7036500 A s P f x p')). Qed.
Lemma lem7036503 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term90 A s P f x p' q'.
Proof. exact (@lem7036502 A s P f x p' q'). Qed.
Lemma lem7036504 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term90 A s P f x p' q') = (term91 A s P f x p' q').
Proof. exact (eq_refl (term90 A s P f x p' q')). Qed.
Lemma lem7036505 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term91 A s P f x p' q'.
Proof. exact (EQ_MP (@lem7036504 A s P f x p' q') (@lem7036503 A s P f x p' q')). Qed.
Lemma lem7036506 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7036507 {A : Type'} (P : nat -> Prop) (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term92 A P f x s q'.
Proof. exact (@lem7036505 A s P f x (@IN A x s) q'). Qed.
Lemma lem7036508 {A : Type'} (P : nat -> Prop) (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term93 A P f x s q'.
Proof. exact (@lem7036507 A P f x s q' (@lem7036506 A x s)). Qed.
Lemma lem7036509 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7036510 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7036513 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term94 A s P f a.
Proof. exact (fun h0 : @IN A a s => @lem7034604 A P f a s h1 h0). Qed.
Lemma lem7036514 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term94 A s P f a.
Proof. exact (@lem7036513 A a s P f h1). Qed.
Lemma lem7036515 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term94 A s P f x.
Proof. exact (@lem7036514 A x s P f h1). Qed.
Lemma lem7036517 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7036510 A x s) (@lem7036509 A x s h1)). Qed.
Lemma lem7036518 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem7036517 A x s h1)). Qed.
Lemma lem7036519 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7036518 A x s h1) (@lem0)). Qed.
Lemma lem7036520 {A : Type'} (P : nat -> Prop) (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @IN A x s) : (term22 A P f x) = True.
Proof. exact (@lem7036515 A x s P f h1 (@lem7036519 A x s h2)). Qed.
Lemma lem7036521 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : term94 A s P f x.
Proof. exact (fun h0 : @IN A x s => @lem7036520 A P f x s h1 h0). Qed.
Lemma lem7036522 {A : Type'} (P : nat -> Prop) (f : A -> nat) (x : A) (s : A -> Prop) : term95 A P f x s.
Proof. exact (@lem7036508 A P f x s True). Qed.
Lemma lem7036523 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : (term21 A s P f x) = (term96 A x s).
Proof. exact (@lem7036522 A P f x s (@lem7036521 A x s P f h1)). Qed.
Lemma lem7036525 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7036526 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = True.
Proof. exact (@lem7036525 (@IN A x s)). Qed.
Lemma lem7036527 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : (term21 A s P f x) = True.
Proof. exact (TRANS (@lem7036523 A x s P f h1) (@lem7036526 A x s)). Qed.
Lemma lem7036528 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : (term97 A s P f) = (term98 A).
Proof. exact (fun_ext (fun x : A => @lem7036527 A x s P f h1)). Qed.
Lemma lem7036529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7036530 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : (term9 A s P f) = (term99 A).
Proof. exact (MK_COMB (@lem7036529 A) (@lem7036528 A s P f h1)). Qed.
Lemma lem7036532 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7036533 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem7036532 A t). Qed.
Lemma lem7036534 {A : Type'} : (term99 A) = True.
Proof. exact (@lem7036533 A True). Qed.
Lemma lem7036535 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 A s P f) : (term9 A s P f) = True.
Proof. exact (TRANS (@lem7036530 A s P f h1) (@lem7036534 A)). Qed.
Lemma lem7036536 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term8 A s) : (term100 A s P f) = (True /\ True).
Proof. exact (MK_COMB (@lem7036488 A s h2) (@lem7036535 A s P f h1)). Qed.
Lemma lem7036538 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7036539 : (True /\ True) = True.
Proof. exact (@lem7036538 True). Qed.
Lemma lem7036540 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term8 A s) : (term100 A s P f) = True.
Proof. exact (TRANS (@lem7036536 A P f s h1 h2) (@lem7036539)). Qed.
Lemma lem7036541 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : (term58 A s P f) = (True /\ True).
Proof. exact (MK_COMB (@lem7036477 A s h2) (@lem7036540 A P f s h1 h3)). Qed.
Lemma lem7036543 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7036544 : (True /\ True) = True.
Proof. exact (@lem7036543 True). Qed.
Lemma lem7036545 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : (term58 A s P f) = True.
Proof. exact (TRANS (@lem7036541 A P f s h1 h2 h3) (@lem7036544)). Qed.
Lemma lem7036546 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : True = (term58 A s P f).
Proof. exact (SYM (@lem7036545 A P f s h1 h2 h3)). Qed.
Lemma lem7036547 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : term58 A s P f.
Proof. exact (EQ_MP (@lem7036546 A P f s h1 h2 h3) (@lem0)). Qed.
Lemma lem7036548 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term76 A P) (h3 : @FINITE A s) (h4 : term8 A s) : (term27 A P s f) = True.
Proof. exact (@lem7036471 A s f P h2 (@lem7036547 A P f s h1 h3 h4)). Qed.
Lemma lem7036549 {A : Type'} (P : nat -> Prop) (f : A -> nat) (s : A -> Prop) (h1 : term9 A s P f) (h2 : @FINITE A s) (h3 : term8 A s) : term101 A P s f.
Proof. exact (fun h0 : term76 A P => @lem7036548 A f P s h1 h0 h2 h3). Qed.
Lemma lem7036550 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term10 P) : term102 A s f P.
Proof. exact (@lem7036452 A s f True P h1). Qed.
Lemma lem7036551 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term103 A P s f) = (term104 A P).
Proof. exact (@lem7036550 A s f P h2 (@lem7036549 A P f s h1 h3 h4)). Qed.
Lemma lem7036553 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7036554 {A : Type'} (P : nat -> Prop) : (term104 A P) = True.
Proof. exact (@lem7036553 (term76 A P)). Qed.
Lemma lem7036555 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term103 A P s f) = True.
Proof. exact (TRANS (@lem7036551 A f P s h1 h2 h3 h4) (@lem7036554 A P)). Qed.
Lemma lem7036556 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : True = (term103 A P s f).
Proof. exact (SYM (@lem7036555 A f P s h1 h2 h3 h4)). Qed.
Lemma lem7036557 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term103 A P s f.
Proof. exact (EQ_MP (@lem7036556 A f P s h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem7036558 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term4 A) (h3 : term10 P) (h4 : @FINITE A s) (h5 : term8 A s) : term27 A P s f.
Proof. exact (@lem7036557 A f P s h1 h3 h4 h5 (@lem7034567 A P h2)). Qed.
Lemma lem7036559 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term105 A P s f.
Proof. exact (fun h0 : term4 A => @lem7036558 A f P s h1 h0 h2 h3 h4). Qed.
Lemma lem7036560 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (@lem7036559 A f P s h1 h2 h3 h4 (@lem7034556 A)). Qed.
Lemma lem7036561 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term6 A s P f.
Proof. exact (proj2 (@lem7034557 A s P f h1)). Qed.
Lemma lem7036562 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : @FINITE A s.
Proof. exact (proj1 (@lem7034557 A s P f h1)). Qed.
Lemma lem7036563 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term7 A s P f.
Proof. exact (proj2 (@lem7034558 A s P f h1)). Qed.
Lemma lem7036564 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term8 A s.
Proof. exact (proj1 (@lem7034558 A s P f h1)). Qed.
Lemma lem7036565 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 A s P f) : term9 A s P f.
Proof. exact (proj2 (@lem7034560 A s P f h1)). Qed.
Lemma lem7036566 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 A s P f) : term10 P.
Proof. exact (proj1 (@lem7034560 A s P f h1)). Qed.
Lemma lem7036567 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term9 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term9 A s P f => @lem7036560 A f P s h1 h2 h3 h4) (fun h5 : term27 A P s f => @lem7034562 A s P f h1)). Qed.
Lemma lem7036568 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036567 A f P s h1 h2 h3 h4) (@lem7034562 A s P f h1)). Qed.
Lemma lem7036569 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : (term10 P) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term10 P => @lem7036568 A f P s h1 h2 h3 h4) (fun h5 : term27 A P s f => @lem7034563 P h2)). Qed.
Lemma lem7036570 {A : Type'} (f : A -> nat) (P : nat -> Prop) (s : A -> Prop) (h1 : term9 A s P f) (h2 : term10 P) (h3 : @FINITE A s) (h4 : term8 A s) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036569 A f P s h1 h2 h3 h4) (@lem7034563 P h2)). Qed.
Lemma lem7036571 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term10 P) (h2 : @FINITE A s) (h3 : term8 A s) (h4 : term7 A s P f) : (term9 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h5 : term9 A s P f => @lem7036570 A f P s h5 h1 h2 h3) (fun h5 : term27 A P s f => @lem7036565 A s P f h4)). Qed.
Lemma lem7036572 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term10 P) (h2 : @FINITE A s) (h3 : term8 A s) (h4 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036571 A s P f h1 h2 h3 h4) (@lem7036565 A s P f h4)). Qed.
Lemma lem7036573 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : (term10 P) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term10 P => @lem7036572 A s P f h4 h1 h2 h3) (fun h4 : term27 A P s f => @lem7036566 A s P f h3)). Qed.
Lemma lem7036574 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036573 A s P f h1 h2 h3) (@lem7036566 A s P f h3)). Qed.
Lemma lem7036575 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : (term8 A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s => @lem7036574 A s P f h1 h2 h3) (fun h4 : term27 A P s f => @lem7034561 A s h2)). Qed.
Lemma lem7036576 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term7 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036575 A s P f h1 h2 h3) (@lem7034561 A s h2)). Qed.
Lemma lem7036577 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term6 A s P f) : (term7 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h4 : term7 A s P f => @lem7036576 A s P f h1 h2 h4) (fun h4 : term27 A P s f => @lem7036563 A s P f h3)). Qed.
Lemma lem7036578 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term8 A s) (h3 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036577 A s P f h1 h2 h3) (@lem7036563 A s P f h3)). Qed.
Lemma lem7036579 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term6 A s P f) : (term8 A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : term8 A s => @lem7036578 A s P f h1 h3 h2) (fun h3 : term27 A P s f => @lem7036564 A s P f h2)). Qed.
Lemma lem7036580 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036579 A s P f h1 h2) (@lem7036564 A s P f h2)). Qed.
Lemma lem7036581 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term6 A s P f) : (@FINITE A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7036580 A s P f h1 h2) (fun h3 : term27 A P s f => @lem7034559 A s h1)). Qed.
Lemma lem7036582 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term6 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036581 A s P f h1 h2) (@lem7034559 A s h1)). Qed.
Lemma lem7036583 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term5 A s P f) : (term6 A s P f) = (term27 A P s f).
Proof. exact (prop_ext (fun h3 : term6 A s P f => @lem7036582 A s P f h1 h3) (fun h3 : term27 A P s f => @lem7036561 A s P f h2)). Qed.
Lemma lem7036584 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term5 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036583 A s P f h1 h2) (@lem7036561 A s P f h2)). Qed.
Lemma lem7036585 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : (@FINITE A s) = (term27 A P s f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7036584 A s P f h2 h1) (fun h2 : term27 A P s f => @lem7036562 A s P f h1)). Qed.
Lemma lem7036586 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term27 A P s f.
Proof. exact (EQ_MP (@lem7036585 A s P f h1) (@lem7036562 A s P f h1)). Qed.
Lemma lem7036587 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : term106 A P s f.
Proof. exact (fun h0 : term5 A s P f => @lem7036586 A s P f h0). Qed.
Lemma lem7036592 {A : Type'} (P : nat -> Prop) (f : A -> nat) : term107 A P f.
Proof. exact (fun s : A -> Prop => @lem7036587 A P s f). Qed.
Lemma lem7036597 {A : Type'} (P : nat -> Prop) : term108 A P.
Proof. exact (fun f : A -> nat => @lem7036592 A P f). Qed.
Lemma lem7036602 {A : Type'} : term109 A.
Proof. exact (fun P : nat -> Prop => @lem7036597 A P). Qed.
