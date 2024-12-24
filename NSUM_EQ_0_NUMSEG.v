Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_0_NUMSEG_term_abbrevs.
Require Import IN_NUMSEG_spec.
Require Import NSUM_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7044409 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7044410 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7044411 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7044410 m) (@lem7044409 m)). Qed.
Lemma lem7044412 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7044411 m n). Qed.
Lemma lem7044413 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7044414 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7044413 m n) (@lem7044412 m n)). Qed.
Lemma lem7044415 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7044414 m n p). Qed.
Lemma lem7044416 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7044418 {A : Type'} (f : A -> nat) : term7 A f.
Proof. exact (@lem6930973 A f). Qed.
Lemma lem7044419 {A : Type'} (f : A -> nat) : (term7 A f) = (term8 A f).
Proof. exact (eq_refl (term7 A f)). Qed.
Lemma lem7044420 {A : Type'} (f : A -> nat) : term8 A f.
Proof. exact (EQ_MP (@lem7044419 A f) (@lem7044418 A f)). Qed.
Lemma lem7044421 {A : Type'} (f : A -> nat) (s : A -> Prop) : term9 A f s.
Proof. exact (@lem7044420 A f s). Qed.
Lemma lem7044422 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term9 A f s) = (term10 A s f).
Proof. exact (eq_refl (term9 A f s)). Qed.
Lemma lem7044423 {A : Type'} (s : A -> Prop) (f : A -> nat) : term10 A s f.
Proof. exact (EQ_MP (@lem7044422 A s f) (@lem7044421 A f s)). Qed.
Lemma lem7044424 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term11 A s f) : term11 A s f.
Proof. exact (h1). Qed.
Lemma lem7044425 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term11 A s f) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem7044423 A s f (@lem7044424 A s f h1)). Qed.
Lemma lem7044446 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7044447 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem7044446 p q p' q'). Qed.
Lemma lem7044448 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem7044447 p q p'). Qed.
Lemma lem7044449 (m : nat) (n : nat) (f : nat -> nat) : term15 m n f.
Proof. exact (@lem7044448 (term16 m n f) ((term17 m n f) = (NUMERAL 0))). Qed.
Lemma lem7044450 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : term18 m n f p'.
Proof. exact (@lem7044449 m n f p'). Qed.
Lemma lem7044451 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : (term18 m n f p') = (term19 m n f p').
Proof. exact (eq_refl (term18 m n f p')). Qed.
Lemma lem7044452 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : term19 m n f p'.
Proof. exact (EQ_MP (@lem7044451 m n f p') (@lem7044450 m n f p')). Qed.
Lemma lem7044453 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term20 m n f p' q'.
Proof. exact (@lem7044452 m n f p' q'). Qed.
Lemma lem7044454 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : (term20 m n f p' q') = (term21 m n f p' q').
Proof. exact (eq_refl (term20 m n f p' q')). Qed.
Lemma lem7044455 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term21 m n f p' q'.
Proof. exact (EQ_MP (@lem7044454 m n f p' q') (@lem7044453 m n f p' q')). Qed.
Lemma lem7044495 (m : nat) (n : nat) (f : nat -> nat) : (term16 m n f) = (term16 m n f).
Proof. exact (eq_refl (term16 m n f)). Qed.
Lemma lem7044496 (m : nat) (n : nat) (f : nat -> nat) (q' : Prop) : term22 m n f q'.
Proof. exact (@lem7044455 m n f (term16 m n f) q'). Qed.
Lemma lem7044497 (m : nat) (n : nat) (f : nat -> nat) (q' : Prop) : term23 m n f q'.
Proof. exact (@lem7044496 m n f q' (@lem7044495 m n f)). Qed.
Lemma lem7044498 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term16 m n f.
Proof. exact (h1). Qed.
Lemma lem7044499 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term24 m n f i.
Proof. exact (@lem7044498 m n f h1 i). Qed.
Lemma lem7044500 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term24 m n f i) = (term25 m n f i).
Proof. exact (eq_refl (term24 m n f i)). Qed.
Lemma lem7044501 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term25 m n f i.
Proof. exact (EQ_MP (@lem7044500 m n f i) (@lem7044499 i m n f h1)). Qed.
Lemma lem7044502 (m : nat) (i : nat) (n : nat) (h1 : term6 m i n) : term6 m i n.
Proof. exact (h1). Qed.
Lemma lem7044503 (f : nat -> nat) (m : nat) (i : nat) (n : nat) (h1 : term16 m n f) (h2 : term6 m i n) : (f i) = (NUMERAL 0).
Proof. exact (@lem7044501 i m n f h1 (@lem7044502 m i n h2)). Qed.
Lemma lem7044512 {A : Type'} (s : A -> Prop) (f : A -> nat) : term10 A s f.
Proof. exact (fun h0 : term11 A s f => @lem7044425 A s f h0). Qed.
Lemma lem7044513 (s : nat -> Prop) (f : nat -> nat) : term26 s f.
Proof. exact (@lem7044512 nat s f). Qed.
Lemma lem7044514 (m : nat) (n : nat) (f : nat -> nat) : term27 m n f.
Proof. exact (@lem7044513 (dotdot m n) f). Qed.
Lemma lem7044522 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7044523 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem7044522 p q p' q'). Qed.
Lemma lem7044524 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem7044523 p q p'). Qed.
Lemma lem7044525 (m : nat) (n : nat) (f : nat -> nat) (x : nat) : term28 m n f x.
Proof. exact (@lem7044524 (term5 x m n) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7044526 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : term29 m n f x p'.
Proof. exact (@lem7044525 m n f x p'). Qed.
Lemma lem7044527 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : (term29 m n f x p') = (term30 m n f x p').
Proof. exact (eq_refl (term29 m n f x p')). Qed.
Lemma lem7044528 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : term30 m n f x p'.
Proof. exact (EQ_MP (@lem7044527 m n f x p') (@lem7044526 m n f x p')). Qed.
Lemma lem7044529 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term31 m n f x p' q'.
Proof. exact (@lem7044528 m n f x p' q'). Qed.
Lemma lem7044530 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : (term31 m n f x p' q') = (term32 m n f x p' q').
Proof. exact (eq_refl (term31 m n f x p' q')). Qed.
Lemma lem7044531 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term32 m n f x p' q'.
Proof. exact (EQ_MP (@lem7044530 m n f x p' q') (@lem7044529 m n f x p' q')). Qed.
Lemma lem7044533 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7044416 m p n) (@lem7044415 m n p)). Qed.
Lemma lem7044534 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7044533 m x n). Qed.
Lemma lem7044537 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term33 f m x n q'.
Proof. exact (@lem7044531 m n f x (term6 m x n) q'). Qed.
Lemma lem7044538 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term34 f m x n q'.
Proof. exact (@lem7044537 f m x n q' (@lem7044534 m x n)). Qed.
Lemma lem7044539 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (h1). Qed.
Lemma lem7044540 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem7044539 m x n h1)). Qed.
Lemma lem7044541 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem7044543 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le m x.
Proof. exact (proj1 (@lem7044539 m x n h1)). Qed.
Lemma lem7044544 (m : nat) (x : nat) : (Peano.le m x) = ((Peano.le m x) = True).
Proof. exact (@lem7 (Peano.le m x)). Qed.
Lemma lem7044549 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term25 m n f i.
Proof. exact (fun h0 : term6 m i n => @lem7044503 f m i n h1 h0). Qed.
Lemma lem7044550 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term25 m n f x.
Proof. exact (@lem7044549 x m n f h1). Qed.
Lemma lem7044554 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le m x) = True.
Proof. exact (EQ_MP (@lem7044544 m x) (@lem7044543 m x n h1)). Qed.
Lemma lem7044555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7044556 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term35 m x) = (and True).
Proof. exact (MK_COMB (@lem7044555) (@lem7044554 m x n h1)). Qed.
Lemma lem7044558 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem7044541 x n) (@lem7044540 m x n h1)). Qed.
Lemma lem7044559 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = (True /\ True).
Proof. exact (MK_COMB (@lem7044556 m x n h1) (@lem7044558 m x n h1)). Qed.
Lemma lem7044561 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7044562 : (True /\ True) = True.
Proof. exact (@lem7044561 True). Qed.
Lemma lem7044563 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = True.
Proof. exact (TRANS (@lem7044559 m x n h1) (@lem7044562)). Qed.
Lemma lem7044564 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : True = (term6 m x n).
Proof. exact (SYM (@lem7044563 m x n h1)). Qed.
Lemma lem7044565 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (EQ_MP (@lem7044564 m x n h1) (@lem0)). Qed.
Lemma lem7044566 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (h1 : term16 m n f) (h2 : term6 m x n) : (f x) = (NUMERAL 0).
Proof. exact (@lem7044550 x m n f h1 (@lem7044565 m x n h2)). Qed.
Lemma lem7044567 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7044568 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (h1 : term16 m n f) (h2 : term6 m x n) : (term36 f x) = term37.
Proof. exact (MK_COMB (@lem7044567) (@lem7044566 f m x n h1 h2)). Qed.
Lemma lem7044569 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7044570 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (h1 : term16 m n f) (h2 : term6 m x n) : ((f x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7044568 f m x n h1 h2) (@lem7044569)). Qed.
Lemma lem7044572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7044573 (x : nat) : (x = x) = True.
Proof. exact (@lem7044572 nat x). Qed.
Lemma lem7044574 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem7044573 (NUMERAL 0)). Qed.
Lemma lem7044575 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (h1 : term16 m n f) (h2 : term6 m x n) : ((f x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem7044570 f m x n h1 h2) (@lem7044574)). Qed.
Lemma lem7044576 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term38 m n f x.
Proof. exact (fun h0 : term6 m x n => @lem7044575 f m x n h1 h0). Qed.
Lemma lem7044577 (f : nat -> nat) (m : nat) (x : nat) (n : nat) : term39 f m x n.
Proof. exact (@lem7044538 f m x n True). Qed.
Lemma lem7044578 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term40 m n f x) = (term41 m x n).
Proof. exact (@lem7044577 f m x n (@lem7044576 x m n f h1)). Qed.
Lemma lem7044580 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7044581 (m : nat) (x : nat) (n : nat) : (term41 m x n) = True.
Proof. exact (@lem7044580 (term6 m x n)). Qed.
Lemma lem7044582 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term40 m n f x) = True.
Proof. exact (TRANS (@lem7044578 x m n f h1) (@lem7044581 m x n)). Qed.
Lemma lem7044583 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term42 m n f) = term43.
Proof. exact (fun_ext (fun x : nat => @lem7044582 x m n f h1)). Qed.
Lemma lem7044584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044585 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term44 m n f) = term45.
Proof. exact (MK_COMB (@lem7044584) (@lem7044583 m n f h1)). Qed.
Lemma lem7044587 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044588 (t : Prop) : (term47 t) = t.
Proof. exact (@lem7044587 nat t). Qed.
Lemma lem7044589 : term45 = True.
Proof. exact (@lem7044588 True). Qed.
Lemma lem7044590 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term44 m n f) = True.
Proof. exact (TRANS (@lem7044585 m n f h1) (@lem7044589)). Qed.
Lemma lem7044591 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : True = (term44 m n f).
Proof. exact (SYM (@lem7044590 m n f h1)). Qed.
Lemma lem7044592 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : term44 m n f.
Proof. exact (EQ_MP (@lem7044591 m n f h1) (@lem0)). Qed.
Lemma lem7044593 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term17 m n f) = (NUMERAL 0).
Proof. exact (@lem7044514 m n f (@lem7044592 m n f h1)). Qed.
Lemma lem7044594 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7044595 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : (term48 m n f) = term37.
Proof. exact (MK_COMB (@lem7044594) (@lem7044593 m n f h1)). Qed.
Lemma lem7044596 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7044597 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : ((term17 m n f) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7044595 m n f h1) (@lem7044596)). Qed.
Lemma lem7044599 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7044600 (x : nat) : (x = x) = True.
Proof. exact (@lem7044599 nat x). Qed.
Lemma lem7044601 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem7044600 (NUMERAL 0)). Qed.
Lemma lem7044602 (m : nat) (n : nat) (f : nat -> nat) (h1 : term16 m n f) : ((term17 m n f) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem7044597 m n f h1) (@lem7044601)). Qed.
Lemma lem7044603 (m : nat) (n : nat) (f : nat -> nat) : term49 m n f.
Proof. exact (fun h0 : term16 m n f => @lem7044602 m n f h0). Qed.
Lemma lem7044604 (m : nat) (n : nat) (f : nat -> nat) : term50 m n f.
Proof. exact (@lem7044497 m n f True). Qed.
Lemma lem7044605 (m : nat) (n : nat) (f : nat -> nat) : (term51 m n f) = (term52 m n f).
Proof. exact (@lem7044604 m n f (@lem7044603 m n f)). Qed.
Lemma lem7044607 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7044608 (m : nat) (n : nat) (f : nat -> nat) : (term52 m n f) = True.
Proof. exact (@lem7044607 (term16 m n f)). Qed.
Lemma lem7044609 (m : nat) (n : nat) (f : nat -> nat) : (term51 m n f) = True.
Proof. exact (TRANS (@lem7044605 m n f) (@lem7044608 m n f)). Qed.
Lemma lem7044610 (m : nat) (f : nat -> nat) : (term53 m f) = term43.
Proof. exact (fun_ext (fun n : nat => @lem7044609 m n f)). Qed.
Lemma lem7044611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044612 (m : nat) (f : nat -> nat) : (term54 m f) = term45.
Proof. exact (MK_COMB (@lem7044611) (@lem7044610 m f)). Qed.
Lemma lem7044614 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044615 (t : Prop) : (term47 t) = t.
Proof. exact (@lem7044614 nat t). Qed.
Lemma lem7044616 : term45 = True.
Proof. exact (@lem7044615 True). Qed.
Lemma lem7044617 (m : nat) (f : nat -> nat) : (term54 m f) = True.
Proof. exact (TRANS (@lem7044612 m f) (@lem7044616)). Qed.
Lemma lem7044618 (f : nat -> nat) : (term55 f) = term43.
Proof. exact (fun_ext (fun m : nat => @lem7044617 m f)). Qed.
Lemma lem7044619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044620 (f : nat -> nat) : (term56 f) = term45.
Proof. exact (MK_COMB (@lem7044619) (@lem7044618 f)). Qed.
Lemma lem7044622 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044623 (t : Prop) : (term47 t) = t.
Proof. exact (@lem7044622 nat t). Qed.
Lemma lem7044624 : term45 = True.
Proof. exact (@lem7044623 True). Qed.
Lemma lem7044625 (f : nat -> nat) : (term56 f) = True.
Proof. exact (TRANS (@lem7044620 f) (@lem7044624)). Qed.
Lemma lem7044626 : term57 = term58.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7044625 f)). Qed.
Lemma lem7044627 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7044628 : term59 = term60.
Proof. exact (MK_COMB (@lem7044627) (@lem7044626)). Qed.
Lemma lem7044630 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044631 (t : Prop) : (term61 t) = t.
Proof. exact (@lem7044630 (nat -> nat) t). Qed.
Lemma lem7044632 : term60 = True.
Proof. exact (@lem7044631 True). Qed.
Lemma lem7044633 : term59 = True.
Proof. exact (TRANS (@lem7044628) (@lem7044632)). Qed.
Lemma lem7044634 : True = term59.
Proof. exact (SYM (@lem7044633)). Qed.
Lemma lem7044635 : term59.
Proof. exact (EQ_MP (@lem7044634) (@lem0)). Qed.
