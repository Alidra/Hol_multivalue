Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_CROSS_term_abbrevs.
Require Import CARD_PRODUCT_spec.
Require Import CROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4325577 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4323933 A B s). Qed.
Lemma lem4325578 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4325579 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4325578 A B s) (@lem4325577 A B s)). Qed.
Lemma lem4325580 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem4325579 A B s t). Qed.
Lemma lem4325581 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term2 A B s t) = (term3 A B s t).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem4325582 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (EQ_MP (@lem4325581 A B s t) (@lem4325580 A B s t)). Qed.
Lemma lem4325583 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term4 A B s t.
Proof. exact (h1). Qed.
Lemma lem4325584 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : (term5 A B s t) = (term6 A B s t).
Proof. exact (@lem4325582 A B s t (@lem4325583 A B s t h1)). Qed.
Lemma lem4325590 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term7 _103681 _103682 s.
Proof. exact (@lem4325236 _103681 _103682 s). Qed.
Lemma lem4325591 {_103681 _103682 : Type'} (s : _103682 -> Prop) : (term7 _103681 _103682 s) = (term8 _103681 _103682 s).
Proof. exact (eq_refl (term7 _103681 _103682 s)). Qed.
Lemma lem4325592 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term8 _103681 _103682 s.
Proof. exact (EQ_MP (@lem4325591 _103681 _103682 s) (@lem4325590 _103681 _103682 s)). Qed.
Lemma lem4325593 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : term9 _103681 _103682 s t.
Proof. exact (@lem4325592 _103681 _103682 s t). Qed.
Lemma lem4325594 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (term9 _103681 _103682 s t) = ((@CROSS _103681 _103682 s t) = (term10 _103681 _103682 s t)).
Proof. exact (eq_refl (term9 _103681 _103682 s t)). Qed.
Lemma lem4325607 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4325608 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem4325607 p q p' q'). Qed.
Lemma lem4325609 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem4325608 p q p'). Qed.
Lemma lem4325610 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : term14 _103797 _103799 s t.
Proof. exact (@lem4325609 (term4 _103797 _103799 s t) ((term15 _103797 _103799 s t) = (term6 _103797 _103799 s t))). Qed.
Lemma lem4325611 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) : term16 _103797 _103799 s t p'.
Proof. exact (@lem4325610 _103797 _103799 s t p'). Qed.
Lemma lem4325612 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) : (term16 _103797 _103799 s t p') = (term17 _103797 _103799 s t p').
Proof. exact (eq_refl (term16 _103797 _103799 s t p')). Qed.
Lemma lem4325613 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) : term17 _103797 _103799 s t p'.
Proof. exact (EQ_MP (@lem4325612 _103797 _103799 s t p') (@lem4325611 _103797 _103799 s t p')). Qed.
Lemma lem4325614 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) (q' : Prop) : term18 _103797 _103799 s t p' q'.
Proof. exact (@lem4325613 _103797 _103799 s t p' q'). Qed.
Lemma lem4325615 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) (q' : Prop) : (term18 _103797 _103799 s t p' q') = (term19 _103797 _103799 s t p' q').
Proof. exact (eq_refl (term18 _103797 _103799 s t p' q')). Qed.
Lemma lem4325616 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (p' : Prop) (q' : Prop) : term19 _103797 _103799 s t p' q'.
Proof. exact (EQ_MP (@lem4325615 _103797 _103799 s t p' q') (@lem4325614 _103797 _103799 s t p' q')). Qed.
Lemma lem4325619 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term4 _103797 _103799 s t) = (term4 _103797 _103799 s t).
Proof. exact (eq_refl (term4 _103797 _103799 s t)). Qed.
Lemma lem4325620 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (q' : Prop) : term20 _103797 _103799 s t q'.
Proof. exact (@lem4325616 _103797 _103799 s t (term4 _103797 _103799 s t) q'). Qed.
Lemma lem4325621 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (q' : Prop) : term21 _103797 _103799 s t q'.
Proof. exact (@lem4325620 _103797 _103799 s t q' (@lem4325619 _103797 _103799 s t)). Qed.
Lemma lem4325622 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : term4 _103797 _103799 s t.
Proof. exact (h1). Qed.
Lemma lem4325623 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : @FINITE _103799 t.
Proof. exact (proj2 (@lem4325622 _103797 _103799 s t h1)). Qed.
Lemma lem4325624 {_103799 : Type'} (t : _103799 -> Prop) : (@FINITE _103799 t) = ((@FINITE _103799 t) = True).
Proof. exact (@lem7 (@FINITE _103799 t)). Qed.
Lemma lem4325626 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : @FINITE _103797 s.
Proof. exact (proj1 (@lem4325622 _103797 _103799 s t h1)). Qed.
Lemma lem4325627 {_103797 : Type'} (s : _103797 -> Prop) : (@FINITE _103797 s) = ((@FINITE _103797 s) = True).
Proof. exact (@lem7 (@FINITE _103797 s)). Qed.
Lemma lem4325632 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (@CROSS _103681 _103682 s t) = (term10 _103681 _103682 s t).
Proof. exact (EQ_MP (@lem4325594 _103681 _103682 s t) (@lem4325593 _103681 _103682 s t)). Qed.
Lemma lem4325633 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (@CROSS _103799 _103797 s t) = (term22 _103797 _103799 s t).
Proof. exact (@lem4325632 _103799 _103797 s t). Qed.
Lemma lem4325644 {_103797 _103799 : Type'} : (@CARD (prod _103797 _103799)) = (@CARD (prod _103797 _103799)).
Proof. exact (eq_refl (@CARD (prod _103797 _103799))). Qed.
Lemma lem4325645 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term15 _103797 _103799 s t) = (term5 _103797 _103799 s t).
Proof. exact (MK_COMB (@lem4325644 _103797 _103799) (@lem4325633 _103797 _103799 s t)). Qed.
Lemma lem4325647 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (fun h0 : term4 A B s t => @lem4325584 A B s t h0). Qed.
Lemma lem4325648 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : term3 _103797 _103799 s t.
Proof. exact (@lem4325647 _103797 _103799 s t). Qed.
Lemma lem4325652 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (@FINITE _103797 s) = True.
Proof. exact (EQ_MP (@lem4325627 _103797 s) (@lem4325626 _103797 _103799 s t h1)). Qed.
Lemma lem4325653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4325654 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term23 _103797 s) = (and True).
Proof. exact (MK_COMB (@lem4325653) (@lem4325652 _103797 _103799 s t h1)). Qed.
Lemma lem4325656 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (@FINITE _103799 t) = True.
Proof. exact (EQ_MP (@lem4325624 _103799 t) (@lem4325623 _103797 _103799 s t h1)). Qed.
Lemma lem4325657 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term4 _103797 _103799 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4325654 _103797 _103799 s t h1) (@lem4325656 _103797 _103799 s t h1)). Qed.
Lemma lem4325659 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4325660 : (True /\ True) = True.
Proof. exact (@lem4325659 True). Qed.
Lemma lem4325661 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term4 _103797 _103799 s t) = True.
Proof. exact (TRANS (@lem4325657 _103797 _103799 s t h1) (@lem4325660)). Qed.
Lemma lem4325662 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : True = (term4 _103797 _103799 s t).
Proof. exact (SYM (@lem4325661 _103797 _103799 s t h1)). Qed.
Lemma lem4325663 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : term4 _103797 _103799 s t.
Proof. exact (EQ_MP (@lem4325662 _103797 _103799 s t h1) (@lem0)). Qed.
Lemma lem4325664 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term5 _103797 _103799 s t) = (term6 _103797 _103799 s t).
Proof. exact (@lem4325648 _103797 _103799 s t (@lem4325663 _103797 _103799 s t h1)). Qed.
Lemma lem4325665 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term15 _103797 _103799 s t) = (term6 _103797 _103799 s t).
Proof. exact (TRANS (@lem4325645 _103797 _103799 s t) (@lem4325664 _103797 _103799 s t h1)). Qed.
Lemma lem4325666 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4325667 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : (term24 _103797 _103799 s t) = (term25 _103797 _103799 s t).
Proof. exact (MK_COMB (@lem4325666) (@lem4325665 _103797 _103799 s t h1)). Qed.
Lemma lem4325668 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term6 _103797 _103799 s t) = (term6 _103797 _103799 s t).
Proof. exact (eq_refl (term6 _103797 _103799 s t)). Qed.
Lemma lem4325669 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : ((term15 _103797 _103799 s t) = (term6 _103797 _103799 s t)) = ((term6 _103797 _103799 s t) = (term6 _103797 _103799 s t)).
Proof. exact (MK_COMB (@lem4325667 _103797 _103799 s t h1) (@lem4325668 _103797 _103799 s t)). Qed.
Lemma lem4325671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4325672 (x : nat) : (x = x) = True.
Proof. exact (@lem4325671 nat x). Qed.
Lemma lem4325673 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : ((term6 _103797 _103799 s t) = (term6 _103797 _103799 s t)) = True.
Proof. exact (@lem4325672 (term6 _103797 _103799 s t)). Qed.
Lemma lem4325674 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) (h1 : term4 _103797 _103799 s t) : ((term15 _103797 _103799 s t) = (term6 _103797 _103799 s t)) = True.
Proof. exact (TRANS (@lem4325669 _103797 _103799 s t h1) (@lem4325673 _103797 _103799 s t)). Qed.
Lemma lem4325675 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : term26 _103797 _103799 s t.
Proof. exact (fun h0 : term4 _103797 _103799 s t => @lem4325674 _103797 _103799 s t h0). Qed.
Lemma lem4325676 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : term27 _103797 _103799 s t.
Proof. exact (@lem4325621 _103797 _103799 s t True). Qed.
Lemma lem4325677 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term28 _103797 _103799 s t) = (term29 _103797 _103799 s t).
Proof. exact (@lem4325676 _103797 _103799 s t (@lem4325675 _103797 _103799 s t)). Qed.
Lemma lem4325679 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4325680 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term29 _103797 _103799 s t) = True.
Proof. exact (@lem4325679 (term4 _103797 _103799 s t)). Qed.
Lemma lem4325681 {_103797 _103799 : Type'} (s : _103797 -> Prop) (t : _103799 -> Prop) : (term28 _103797 _103799 s t) = True.
Proof. exact (TRANS (@lem4325677 _103797 _103799 s t) (@lem4325680 _103797 _103799 s t)). Qed.
Lemma lem4325682 {_103797 _103799 : Type'} (s : _103797 -> Prop) : (term30 _103797 _103799 s) = (term31 _103799).
Proof. exact (fun_ext (fun t : _103799 -> Prop => @lem4325681 _103797 _103799 s t)). Qed.
Lemma lem4325683 {_103799 : Type'} : (@all (_103799 -> Prop)) = (@all (_103799 -> Prop)).
Proof. exact (eq_refl (@all (_103799 -> Prop))). Qed.
Lemma lem4325684 {_103797 _103799 : Type'} (s : _103797 -> Prop) : (term32 _103797 _103799 s) = (term33 _103799).
Proof. exact (MK_COMB (@lem4325683 _103799) (@lem4325682 _103797 _103799 s)). Qed.
Lemma lem4325686 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325687 {_103799 : Type'} (t : Prop) : (term35 _103799 t) = t.
Proof. exact (@lem4325686 (_103799 -> Prop) t). Qed.
Lemma lem4325688 {_103799 : Type'} : (term33 _103799) = True.
Proof. exact (@lem4325687 _103799 True). Qed.
Lemma lem4325689 {_103797 _103799 : Type'} (s : _103797 -> Prop) : (term32 _103797 _103799 s) = True.
Proof. exact (TRANS (@lem4325684 _103797 _103799 s) (@lem4325688 _103799)). Qed.
Lemma lem4325690 {_103797 _103799 : Type'} : (term36 _103797 _103799) = (term31 _103797).
Proof. exact (fun_ext (fun s : _103797 -> Prop => @lem4325689 _103797 _103799 s)). Qed.
Lemma lem4325691 {_103797 : Type'} : (@all (_103797 -> Prop)) = (@all (_103797 -> Prop)).
Proof. exact (eq_refl (@all (_103797 -> Prop))). Qed.
Lemma lem4325692 {_103797 _103799 : Type'} : (term37 _103797 _103799) = (term33 _103797).
Proof. exact (MK_COMB (@lem4325691 _103797) (@lem4325690 _103797 _103799)). Qed.
Lemma lem4325694 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325695 {_103797 : Type'} (t : Prop) : (term35 _103797 t) = t.
Proof. exact (@lem4325694 (_103797 -> Prop) t). Qed.
Lemma lem4325696 {_103797 : Type'} : (term33 _103797) = True.
Proof. exact (@lem4325695 _103797 True). Qed.
Lemma lem4325697 {_103797 _103799 : Type'} : (term37 _103797 _103799) = True.
Proof. exact (TRANS (@lem4325692 _103797 _103799) (@lem4325696 _103797)). Qed.
Lemma lem4325698 {_103797 _103799 : Type'} : True = (term37 _103797 _103799).
Proof. exact (SYM (@lem4325697 _103797 _103799)). Qed.
Lemma lem4325699 {_103797 _103799 : Type'} : term37 _103797 _103799.
Proof. exact (EQ_MP (@lem4325698 _103797 _103799) (@lem0)). Qed.
