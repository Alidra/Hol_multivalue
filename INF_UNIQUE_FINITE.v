Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_UNIQUE_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_INF_LE_FINITE_spec.
Require Import REAL_LE_INF_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm1339379_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5248525 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5248526 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5248527 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5248526 t1) (@lem5248525 t1)). Qed.
Lemma lem5248528 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5248527 t1 t2). Qed.
Lemma lem5248529 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5248530 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5248529 t1 t2) (@lem5248528 t1 t2)). Qed.
Lemma lem5248531 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5248530 t1 t2 t3). Qed.
Lemma lem5248532 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5248533 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5248532 t1 t2 t3) (@lem5248531 t1 t2 t3)). Qed.
Lemma lem5248534 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5248533 t1 t2 t3)). Qed.
Lemma lem5248537 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (term7 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem5248538 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (x = y) = (term7 y x).
Proof. exact (SYM (@lem5248537 x y h1)). Qed.
Lemma lem5248539 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (x = y) = (term7 y x).
Proof. exact (h1). Qed.
Lemma lem5248540 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (term7 y x) = (x = y).
Proof. exact (SYM (@lem5248539 y x h1)). Qed.
Lemma lem5248541 (y : real) (x : real) : ((term7 y x) = (x = y)) = ((x = y) = (term7 y x)).
Proof. exact (prop_ext (fun h1 : (term7 y x) = (x = y) => @lem5248538 x y h1) (fun h1 : (x = y) = (term7 y x) => @lem5248540 y x h1)). Qed.
Lemma lem5248542 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem5248541 y x)). Qed.
Lemma lem5248543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5248544 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem5248543) (@lem5248542 x)). Qed.
Lemma lem5248545 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem5248544 x)). Qed.
Lemma lem5248546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5248547 : term14 = term15.
Proof. exact (MK_COMB (@lem5248546) (@lem5248545)). Qed.
Lemma lem5248548 : term15.
Proof. exact (EQ_MP (@lem5248547) (@lem1339379)). Qed.
Lemma lem5248576 (s : real -> Prop) : term16 s.
Proof. exact (@lem5227045 s). Qed.
Lemma lem5248577 (s : real -> Prop) : (term16 s) = (term17 s).
Proof. exact (eq_refl (term16 s)). Qed.
Lemma lem5248578 (s : real -> Prop) : term17 s.
Proof. exact (EQ_MP (@lem5248577 s) (@lem5248576 s)). Qed.
Lemma lem5248579 (s : real -> Prop) (a : real) : term18 s a.
Proof. exact (@lem5248578 s a). Qed.
Lemma lem5248580 (s : real -> Prop) (a : real) : (term18 s a) = (term19 s a).
Proof. exact (eq_refl (term18 s a)). Qed.
Lemma lem5248581 (s : real -> Prop) (a : real) : term19 s a.
Proof. exact (EQ_MP (@lem5248580 s a) (@lem5248579 s a)). Qed.
Lemma lem5248582 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5248583 (a : real) (s : real -> Prop) (h1 : term20 s) : (term21 s a) = (term22 s a).
Proof. exact (@lem5248581 s a (@lem5248582 s h1)). Qed.
Lemma lem5248589 (s : real -> Prop) : term23 s.
Proof. exact (@lem5224798 s). Qed.
Lemma lem5248590 (s : real -> Prop) : (term23 s) = (term24 s).
Proof. exact (eq_refl (term23 s)). Qed.
Lemma lem5248591 (s : real -> Prop) : term24 s.
Proof. exact (EQ_MP (@lem5248590 s) (@lem5248589 s)). Qed.
Lemma lem5248592 (s : real -> Prop) (a : real) : term25 s a.
Proof. exact (@lem5248591 s a). Qed.
Lemma lem5248593 (s : real -> Prop) (a : real) : (term25 s a) = (term26 s a).
Proof. exact (eq_refl (term25 s a)). Qed.
Lemma lem5248594 (s : real -> Prop) (a : real) : term26 s a.
Proof. exact (EQ_MP (@lem5248593 s a) (@lem5248592 s a)). Qed.
Lemma lem5248595 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5248596 (a : real) (s : real -> Prop) (h1 : term20 s) : (term27 a s) = (term28 s a).
Proof. exact (@lem5248594 s a (@lem5248595 s h1)). Qed.
Lemma lem5248602 (x : real) : term29 x.
Proof. exact (@lem5248548 x). Qed.
Lemma lem5248603 (x : real) : (term29 x) = (term11 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem5248604 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem5248603 x) (@lem5248602 x)). Qed.
Lemma lem5248605 (x : real) (y : real) : term30 x y.
Proof. exact (@lem5248604 x y). Qed.
Lemma lem5248606 (y : real) (x : real) : (term30 x y) = ((x = y) = (term7 y x)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem5248615 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term31 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5248616 (p : Prop) (q : Prop) (p' : Prop) : term32 p q p'.
Proof. exact (fun q' : Prop => @lem5248615 p q p' q'). Qed.
Lemma lem5248617 (p : Prop) (q : Prop) : term33 p q.
Proof. exact (fun p' : Prop => @lem5248616 p q p'). Qed.
Lemma lem5248618 (s : real -> Prop) (a : real) : term34 s a.
Proof. exact (@lem5248617 (term20 s) (((inf s) = a) = (term35 s a))). Qed.
Lemma lem5248619 (s : real -> Prop) (a : real) (p' : Prop) : term36 s a p'.
Proof. exact (@lem5248618 s a p'). Qed.
Lemma lem5248620 (s : real -> Prop) (a : real) (p' : Prop) : (term36 s a p') = (term37 s a p').
Proof. exact (eq_refl (term36 s a p')). Qed.
Lemma lem5248621 (s : real -> Prop) (a : real) (p' : Prop) : term37 s a p'.
Proof. exact (EQ_MP (@lem5248620 s a p') (@lem5248619 s a p')). Qed.
Lemma lem5248622 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : term38 s a p' q'.
Proof. exact (@lem5248621 s a p' q'). Qed.
Lemma lem5248623 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : (term38 s a p' q') = (term39 s a p' q').
Proof. exact (eq_refl (term38 s a p' q')). Qed.
Lemma lem5248624 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : term39 s a p' q'.
Proof. exact (EQ_MP (@lem5248623 s a p' q') (@lem5248622 s a p' q')). Qed.
Lemma lem5248631 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5248632 (a : real) (s : real -> Prop) (q' : Prop) : term40 a s q'.
Proof. exact (@lem5248624 s a (term20 s) q'). Qed.
Lemma lem5248633 (a : real) (s : real -> Prop) (q' : Prop) : term41 a s q'.
Proof. exact (@lem5248632 a s q' (@lem5248631 s)). Qed.
Lemma lem5248634 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5248635 (s : real -> Prop) (h1 : term20 s) : term42 s.
Proof. exact (proj2 (@lem5248634 s h1)). Qed.
Lemma lem5248636 (s : real -> Prop) : term43 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5248649 (s : real -> Prop) (h1 : term20 s) : @FINITE real s.
Proof. exact (proj1 (@lem5248634 s h1)). Qed.
Lemma lem5248650 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5248659 (y : real) (x : real) : (x = y) = (term7 y x).
Proof. exact (EQ_MP (@lem5248606 y x) (@lem5248605 x y)). Qed.
Lemma lem5248660 (a : real) (s : real -> Prop) : ((inf s) = a) = (term44 a s).
Proof. exact (@lem5248659 a (inf s)). Qed.
Lemma lem5248664 (s : real -> Prop) (a : real) : term19 s a.
Proof. exact (fun h0 : term20 s => @lem5248583 a s h0). Qed.
Lemma lem5248668 (s : real -> Prop) (h1 : term20 s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5248650 s) (@lem5248649 s h1)). Qed.
Lemma lem5248669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5248670 (s : real -> Prop) (h1 : term20 s) : (term45 s) = (and True).
Proof. exact (MK_COMB (@lem5248669) (@lem5248668 s h1)). Qed.
Lemma lem5248672 (s : real -> Prop) (h1 : term20 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5248636 s (@lem5248635 s h1)). Qed.
Lemma lem5248673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5248674 (s : real -> Prop) (h1 : term20 s) : (term42 s) = (~ False).
Proof. exact (MK_COMB (@lem5248673) (@lem5248672 s h1)). Qed.
Lemma lem5248676 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5248677 (s : real -> Prop) (h1 : term20 s) : (term42 s) = True.
Proof. exact (TRANS (@lem5248674 s h1) (@lem5248676)). Qed.
Lemma lem5248678 (s : real -> Prop) (h1 : term20 s) : (term20 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5248670 s h1) (@lem5248677 s h1)). Qed.
Lemma lem5248680 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5248681 : (True /\ True) = True.
Proof. exact (@lem5248680 True). Qed.
Lemma lem5248682 (s : real -> Prop) (h1 : term20 s) : (term20 s) = True.
Proof. exact (TRANS (@lem5248678 s h1) (@lem5248681)). Qed.
Lemma lem5248683 (s : real -> Prop) (h1 : term20 s) : True = (term20 s).
Proof. exact (SYM (@lem5248682 s h1)). Qed.
Lemma lem5248684 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (EQ_MP (@lem5248683 s h1) (@lem0)). Qed.
Lemma lem5248685 (a : real) (s : real -> Prop) (h1 : term20 s) : (term21 s a) = (term22 s a).
Proof. exact (@lem5248664 s a (@lem5248684 s h1)). Qed.
Lemma lem5248692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5248693 (a : real) (s : real -> Prop) (h1 : term20 s) : (term46 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5248692) (@lem5248685 a s h1)). Qed.
Lemma lem5248701 (s : real -> Prop) (a : real) : term26 s a.
Proof. exact (fun h0 : term20 s => @lem5248596 a s h0). Qed.
Lemma lem5248705 (s : real -> Prop) (h1 : term20 s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5248650 s) (@lem5248649 s h1)). Qed.
Lemma lem5248706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5248707 (s : real -> Prop) (h1 : term20 s) : (term45 s) = (and True).
Proof. exact (MK_COMB (@lem5248706) (@lem5248705 s h1)). Qed.
Lemma lem5248709 (s : real -> Prop) (h1 : term20 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5248636 s (@lem5248635 s h1)). Qed.
Lemma lem5248710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5248711 (s : real -> Prop) (h1 : term20 s) : (term42 s) = (~ False).
Proof. exact (MK_COMB (@lem5248710) (@lem5248709 s h1)). Qed.
Lemma lem5248713 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5248714 (s : real -> Prop) (h1 : term20 s) : (term42 s) = True.
Proof. exact (TRANS (@lem5248711 s h1) (@lem5248713)). Qed.
Lemma lem5248715 (s : real -> Prop) (h1 : term20 s) : (term20 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5248707 s h1) (@lem5248714 s h1)). Qed.
Lemma lem5248717 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5248718 : (True /\ True) = True.
Proof. exact (@lem5248717 True). Qed.
Lemma lem5248719 (s : real -> Prop) (h1 : term20 s) : (term20 s) = True.
Proof. exact (TRANS (@lem5248715 s h1) (@lem5248718)). Qed.
Lemma lem5248720 (s : real -> Prop) (h1 : term20 s) : True = (term20 s).
Proof. exact (SYM (@lem5248719 s h1)). Qed.
Lemma lem5248721 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (EQ_MP (@lem5248720 s h1) (@lem0)). Qed.
Lemma lem5248722 (a : real) (s : real -> Prop) (h1 : term20 s) : (term27 a s) = (term28 s a).
Proof. exact (@lem5248701 s a (@lem5248721 s h1)). Qed.
Lemma lem5248750 (a : real) (s : real -> Prop) (h1 : term20 s) : (term44 a s) = (term48 s a).
Proof. exact (MK_COMB (@lem5248693 a s h1) (@lem5248722 a s h1)). Qed.
Lemma lem5248786 (a : real) (s : real -> Prop) (h1 : term20 s) : ((inf s) = a) = (term48 s a).
Proof. exact (TRANS (@lem5248660 a s) (@lem5248750 a s h1)). Qed.
Lemma lem5248787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5248788 (a : real) (s : real -> Prop) (h1 : term20 s) : (term49 s a) = (term50 s a).
Proof. exact (MK_COMB (@lem5248787) (@lem5248786 a s h1)). Qed.
Lemma lem5248853 (s : real -> Prop) (a : real) : (term35 s a) = (term35 s a).
Proof. exact (eq_refl (term35 s a)). Qed.
Lemma lem5248854 (a : real) (s : real -> Prop) (h1 : term20 s) : (((inf s) = a) = (term35 s a)) = ((term48 s a) = (term35 s a)).
Proof. exact (MK_COMB (@lem5248788 a s h1) (@lem5248853 s a)). Qed.
Lemma lem5248923 (s : real -> Prop) (a : real) : term51 s a.
Proof. exact (fun h0 : term20 s => @lem5248854 a s h0). Qed.
Lemma lem5248924 (s : real -> Prop) (a : real) : term52 s a.
Proof. exact (@lem5248633 a s ((term48 s a) = (term35 s a))). Qed.
Lemma lem5248925 (s : real -> Prop) (a : real) : (term53 s a) = (term54 s a).
Proof. exact (@lem5248924 s a (@lem5248923 s a)). Qed.
Lemma lem5249112 (a : real) : (term55 a) = (term56 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5248925 s a)). Qed.
Lemma lem5249299 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5249300 (a : real) : (term57 a) = (term58 a).
Proof. exact (MK_COMB (@lem5249299) (@lem5249112 a)). Qed.
Lemma lem5249491 (a : real) : (term58 a) = (term57 a).
Proof. exact (SYM (@lem5249300 a)). Qed.
Lemma lem5249493 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5249494 (a : real) : (term58 a) = (term60 a).
Proof. exact (@lem5249493 (term58 a)). Qed.
Lemma lem5249495 (a : real) : (term60 a) = (term58 a).
Proof. exact (SYM (@lem5249494 a)). Qed.
Lemma lem5249496 (a : real) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem5249499 (a : real) (h1 : term62 a) : term62 a.
Proof. exact (h1). Qed.
Lemma lem5249500 (a : real) : term63 a.
Proof. exact (fun h0 : term62 a => @lem5249499 a h0). Qed.
Lemma lem5249501 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (h1). Qed.
Lemma lem5249502 (a : real) (h1 : term62 a) : term62 a.
Proof. exact (h1). Qed.
Lemma lem5249503 (a : real) (h1 : term62 a) (h2 : term63 a) : term62 a.
Proof. exact (@lem5249501 a h2 (@lem5249502 a h1)). Qed.
Lemma lem5249504 (a : real) (h1 : term62 a) : term64 a.
Proof. exact (fun h0 : term63 a => @lem5249503 a h1 h0). Qed.
Lemma lem5249505 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (h1). Qed.
Lemma lem5249506 (a : real) (h1 : term62 a) (h2 : term63 a) : term62 a.
Proof. exact (@lem5249504 a h1 (@lem5249505 a h2)). Qed.
Lemma lem5249507 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (fun h0 : term62 a => @lem5249506 a h0 h1). Qed.
Lemma lem5249508 (a : real) : term65 a.
Proof. exact (fun h0 : term63 a => @lem5249507 a h0). Qed.
Lemma lem5249511 (a : real) : term63 a.
Proof. exact (@lem5249508 a (@lem5249500 a)). Qed.
Lemma lem5249623 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5249624 : term66 = term67.
Proof. exact (@lem5249623 term68). Qed.
Lemma lem5249629 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem5249630 : term70 = term71.
Proof. exact (MK_COMB (@lem5249629) (@lem5249624)). Qed.
Lemma lem5249633 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem5249634 : term73 = term74.
Proof. exact (MK_COMB (@lem5249633) (@lem5249630)). Qed.
Lemma lem5249637 (a : real) : (term75 a) = (term75 a).
Proof. exact (eq_refl (term75 a)). Qed.
Lemma lem5249638 (a : real) : (term62 a) = (term76 a).
Proof. exact (MK_COMB (@lem5249637 a) (@lem5249634)). Qed.
Lemma lem5249641 : term77 = term78.
Proof. exact (fun_ext (fun a : real => @lem5249638 a)). Qed.
Lemma lem5249642 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249651 : term79 = term80.
Proof. exact (MK_COMB (@lem5249642) (@lem5249641)). Qed.
Lemma lem5249652 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5249653 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5249652 x)). Qed.
Lemma lem5249654 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249655 : term68 = term68.
Proof. exact (MK_COMB (@lem5249654) (@lem5249653)). Qed.
Lemma lem5249656 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249657 : term67 = term67.
Proof. exact (MK_COMB (@lem5249656) (@lem5249655)). Qed.
Lemma lem5249666 (y : real) (x : real) (z : real) : (term82 y x z) = (term82 y x z).
Proof. exact (eq_refl (term82 y x z)). Qed.
Lemma lem5249667 (y : real) (x : real) : (term83 y x) = (term83 y x).
Proof. exact (fun_ext (fun z : real => @lem5249666 y x z)). Qed.
Lemma lem5249668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249669 (y : real) (x : real) : (term84 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem5249668) (@lem5249667 y x)). Qed.
Lemma lem5249670 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem5249669 y x)). Qed.
Lemma lem5249671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249672 (x : real) : (term86 x) = (term86 x).
Proof. exact (MK_COMB (@lem5249671) (@lem5249670 x)). Qed.
Lemma lem5249673 : term87 = term87.
Proof. exact (fun_ext (fun x : real => @lem5249672 x)). Qed.
Lemma lem5249674 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249675 : term88 = term88.
Proof. exact (MK_COMB (@lem5249674) (@lem5249673)). Qed.
Lemma lem5249676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5249677 : term69 = term69.
Proof. exact (MK_COMB (@lem5249676) (@lem5249675)). Qed.
Lemma lem5249678 : term71 = term71.
Proof. exact (MK_COMB (@lem5249677) (@lem5249657)). Qed.
Lemma lem5249687 (x : real) (y : real) : ((term7 y x) = (x = y)) = ((term7 y x) = (x = y)).
Proof. exact (eq_refl ((term7 y x) = (x = y))). Qed.
Lemma lem5249688 (x : real) : (term8 x) = (term8 x).
Proof. exact (fun_ext (fun y : real => @lem5249687 x y)). Qed.
Lemma lem5249689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249690 (x : real) : (term10 x) = (term10 x).
Proof. exact (MK_COMB (@lem5249689) (@lem5249688 x)). Qed.
Lemma lem5249691 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem5249690 x)). Qed.
Lemma lem5249692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249693 : term14 = term14.
Proof. exact (MK_COMB (@lem5249692) (@lem5249691)). Qed.
Lemma lem5249694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5249695 : term72 = term72.
Proof. exact (MK_COMB (@lem5249694) (@lem5249693)). Qed.
Lemma lem5249696 : term74 = term74.
Proof. exact (MK_COMB (@lem5249695) (@lem5249678)). Qed.
Lemma lem5249701 (s : real -> Prop) (a : real) (y : real) : (term89 s a y) = (term89 s a y).
Proof. exact (eq_refl (term89 s a y)). Qed.
Lemma lem5249702 (s : real -> Prop) (a : real) : (term90 s a) = (term90 s a).
Proof. exact (fun_ext (fun y : real => @lem5249701 s a y)). Qed.
Lemma lem5249703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249704 (s : real -> Prop) (a : real) : (term28 s a) = (term28 s a).
Proof. exact (MK_COMB (@lem5249703) (@lem5249702 s a)). Qed.
Lemma lem5249707 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5249708 (s : real -> Prop) (a : real) : (term35 s a) = (term35 s a).
Proof. exact (MK_COMB (@lem5249707 a s) (@lem5249704 s a)). Qed.
Lemma lem5249713 (s : real -> Prop) (a : real) (x : real) : (term89 s a x) = (term89 s a x).
Proof. exact (eq_refl (term89 s a x)). Qed.
Lemma lem5249714 (s : real -> Prop) (a : real) : (term90 s a) = (term90 s a).
Proof. exact (fun_ext (fun x : real => @lem5249713 s a x)). Qed.
Lemma lem5249715 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249716 (s : real -> Prop) (a : real) : (term28 s a) = (term28 s a).
Proof. exact (MK_COMB (@lem5249715) (@lem5249714 s a)). Qed.
Lemma lem5249721 (s : real -> Prop) (x : real) (a : real) : (term92 s x a) = (term92 s x a).
Proof. exact (eq_refl (term92 s x a)). Qed.
Lemma lem5249722 (s : real -> Prop) (a : real) : (term93 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5249721 s x a)). Qed.
Lemma lem5249723 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5249724 (s : real -> Prop) (a : real) : (term22 s a) = (term22 s a).
Proof. exact (MK_COMB (@lem5249723) (@lem5249722 s a)). Qed.
Lemma lem5249725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5249726 (s : real -> Prop) (a : real) : (term47 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5249725) (@lem5249724 s a)). Qed.
Lemma lem5249727 (s : real -> Prop) (a : real) : (term48 s a) = (term48 s a).
Proof. exact (MK_COMB (@lem5249726 s a) (@lem5249716 s a)). Qed.
Lemma lem5249728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5249729 (s : real -> Prop) (a : real) : (term50 s a) = (term50 s a).
Proof. exact (MK_COMB (@lem5249728) (@lem5249727 s a)). Qed.
Lemma lem5249730 (s : real -> Prop) (a : real) : ((term48 s a) = (term35 s a)) = ((term48 s a) = (term35 s a)).
Proof. exact (MK_COMB (@lem5249729 s a) (@lem5249708 s a)). Qed.
Lemma lem5249739 (s : real -> Prop) : (term94 s) = (term94 s).
Proof. exact (eq_refl (term94 s)). Qed.
Lemma lem5249740 (s : real -> Prop) (a : real) : (term54 s a) = (term54 s a).
Proof. exact (MK_COMB (@lem5249739 s) (@lem5249730 s a)). Qed.
Lemma lem5249741 (a : real) : (term56 a) = (term56 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5249740 s a)). Qed.
Lemma lem5249742 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5249743 (a : real) : (term58 a) = (term58 a).
Proof. exact (MK_COMB (@lem5249742) (@lem5249741 a)). Qed.
Lemma lem5249744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249745 (a : real) : (term61 a) = (term61 a).
Proof. exact (MK_COMB (@lem5249744) (@lem5249743 a)). Qed.
Lemma lem5249746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5249747 (a : real) : (term75 a) = (term75 a).
Proof. exact (MK_COMB (@lem5249746) (@lem5249745 a)). Qed.
Lemma lem5249748 (a : real) : (term76 a) = (term76 a).
Proof. exact (MK_COMB (@lem5249747 a) (@lem5249696)). Qed.
Lemma lem5249749 : term78 = term78.
Proof. exact (fun_ext (fun a : real => @lem5249748 a)). Qed.
Lemma lem5249750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249751 : term80 = term80.
Proof. exact (MK_COMB (@lem5249750) (@lem5249749)). Qed.
Lemma lem5249846 : term79 = term80.
Proof. exact (TRANS (@lem5249651) (@lem5249751)). Qed.
Lemma lem5249847 : term80 = term79.
Proof. exact (SYM (@lem5249846)). Qed.
Lemma lem5249848 (a : real) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem5249849 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem5249851 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem5249865 (s : real -> Prop) (x : real) (a : real) : (term95 s x a) = (term96 s x a).
Proof. exact (@lem17045 (@IN real x s) (real_le x a)). Qed.
Lemma lem5249868 (s : real -> Prop) (x : real) (a : real) : (term92 s x a) = (term92 s x a).
Proof. exact (eq_refl (term92 s x a)). Qed.
Lemma lem5249869 (P : real -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5249870 (s : real -> Prop) (a : real) : (term99 s a) = (term100 s a).
Proof. exact (@lem5249869 (term93 s a)). Qed.
Lemma lem5249871 (s : real -> Prop) (x : real) (a : real) : (term101 s a x) = (term92 s x a).
Proof. exact (eq_refl (term101 s a x)). Qed.
Lemma lem5249872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249873 (s : real -> Prop) (x : real) (a : real) : (term102 s a x) = (term95 s x a).
Proof. exact (MK_COMB (@lem5249872) (@lem5249871 s x a)). Qed.
Lemma lem5249874 (s : real -> Prop) (x : real) (a : real) : (term102 s a x) = (term96 s x a).
Proof. exact (TRANS (@lem5249873 s x a) (@lem5249865 s x a)). Qed.
Lemma lem5249875 (s : real -> Prop) (a : real) : (term103 s a) = (term104 s a).
Proof. exact (fun_ext (fun x : real => @lem5249874 s x a)). Qed.
Lemma lem5249876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249877 (s : real -> Prop) (a : real) : (term100 s a) = (term105 s a).
Proof. exact (MK_COMB (@lem5249876) (@lem5249875 s a)). Qed.
Lemma lem5249878 (s : real -> Prop) (a : real) : (term99 s a) = (term105 s a).
Proof. exact (TRANS (@lem5249870 s a) (@lem5249877 s a)). Qed.
Lemma lem5249879 (s : real -> Prop) (a : real) : (term93 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5249868 s x a)). Qed.
Lemma lem5249880 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5249881 (s : real -> Prop) (a : real) : (term22 s a) = (term22 s a).
Proof. exact (MK_COMB (@lem5249880) (@lem5249879 s a)). Qed.
Lemma lem5249890 (s : real -> Prop) (a : real) (x : real) : (term106 s a x) = (term107 s a x).
Proof. exact (@lem17362 (@IN real x s) (real_le a x)). Qed.
Lemma lem5249895 (s : real -> Prop) (a : real) (x : real) : (term89 s a x) = (term108 s a x).
Proof. exact (@lem17265 (@IN real x s) (real_le a x)). Qed.
Lemma lem5249896 (P : real -> Prop) : (term109 P) = (term110 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5249897 (s : real -> Prop) (a : real) : (term111 s a) = (term112 s a).
Proof. exact (@lem5249896 (term90 s a)). Qed.
Lemma lem5249898 (s : real -> Prop) (a : real) (x : real) : (term113 s a x) = (term89 s a x).
Proof. exact (eq_refl (term113 s a x)). Qed.
Lemma lem5249899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249900 (s : real -> Prop) (a : real) (x : real) : (term114 s a x) = (term106 s a x).
Proof. exact (MK_COMB (@lem5249899) (@lem5249898 s a x)). Qed.
Lemma lem5249901 (s : real -> Prop) (a : real) (x : real) : (term114 s a x) = (term107 s a x).
Proof. exact (TRANS (@lem5249900 s a x) (@lem5249890 s a x)). Qed.
Lemma lem5249902 (s : real -> Prop) (a : real) : (term115 s a) = (term116 s a).
Proof. exact (fun_ext (fun x : real => @lem5249901 s a x)). Qed.
Lemma lem5249903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5249904 (s : real -> Prop) (a : real) : (term112 s a) = (term117 s a).
Proof. exact (MK_COMB (@lem5249903) (@lem5249902 s a)). Qed.
Lemma lem5249905 (s : real -> Prop) (a : real) : (term111 s a) = (term117 s a).
Proof. exact (TRANS (@lem5249897 s a) (@lem5249904 s a)). Qed.
Lemma lem5249906 (s : real -> Prop) (a : real) : (term90 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5249895 s a x)). Qed.
Lemma lem5249907 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249908 (s : real -> Prop) (a : real) : (term28 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5249907) (@lem5249906 s a)). Qed.
Lemma lem5249909 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5249910 (s : real -> Prop) (a : real) : (term120 s a) = (term121 s a).
Proof. exact (MK_COMB (@lem5249909) (@lem5249878 s a)). Qed.
Lemma lem5249911 (s : real -> Prop) (a : real) : (term122 s a) = (term123 s a).
Proof. exact (MK_COMB (@lem5249910 s a) (@lem5249905 s a)). Qed.
Lemma lem5249912 (s : real -> Prop) (a : real) : (term124 s a) = (term122 s a).
Proof. exact (@lem17045 (term22 s a) (term28 s a)). Qed.
Lemma lem5249913 (s : real -> Prop) (a : real) : (term124 s a) = (term123 s a).
Proof. exact (TRANS (@lem5249912 s a) (@lem5249911 s a)). Qed.
Lemma lem5249914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5249915 (s : real -> Prop) (a : real) : (term47 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5249914) (@lem5249881 s a)). Qed.
Lemma lem5249916 (s : real -> Prop) (a : real) : (term48 s a) = (term125 s a).
Proof. exact (MK_COMB (@lem5249915 s a) (@lem5249908 s a)). Qed.
Lemma lem5249927 (s : real -> Prop) (a : real) (y : real) : (term106 s a y) = (term107 s a y).
Proof. exact (@lem17362 (@IN real y s) (real_le a y)). Qed.
Lemma lem5249932 (s : real -> Prop) (a : real) (y : real) : (term89 s a y) = (term108 s a y).
Proof. exact (@lem17265 (@IN real y s) (real_le a y)). Qed.
Lemma lem5249933 (P : real -> Prop) : (term109 P) = (term110 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5249934 (s : real -> Prop) (a : real) : (term111 s a) = (term112 s a).
Proof. exact (@lem5249933 (term90 s a)). Qed.
Lemma lem5249935 (s : real -> Prop) (a : real) (y : real) : (term113 s a y) = (term89 s a y).
Proof. exact (eq_refl (term113 s a y)). Qed.
Lemma lem5249936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249937 (s : real -> Prop) (a : real) (y : real) : (term114 s a y) = (term106 s a y).
Proof. exact (MK_COMB (@lem5249936) (@lem5249935 s a y)). Qed.
Lemma lem5249938 (s : real -> Prop) (a : real) (y : real) : (term114 s a y) = (term107 s a y).
Proof. exact (TRANS (@lem5249937 s a y) (@lem5249927 s a y)). Qed.
Lemma lem5249939 (s : real -> Prop) (a : real) : (term115 s a) = (term116 s a).
Proof. exact (fun_ext (fun y : real => @lem5249938 s a y)). Qed.
Lemma lem5249940 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5249941 (s : real -> Prop) (a : real) : (term112 s a) = (term117 s a).
Proof. exact (MK_COMB (@lem5249940) (@lem5249939 s a)). Qed.
Lemma lem5249942 (s : real -> Prop) (a : real) : (term111 s a) = (term117 s a).
Proof. exact (TRANS (@lem5249934 s a) (@lem5249941 s a)). Qed.
Lemma lem5249943 (s : real -> Prop) (a : real) : (term90 s a) = (term118 s a).
Proof. exact (fun_ext (fun y : real => @lem5249932 s a y)). Qed.
Lemma lem5249944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5249945 (s : real -> Prop) (a : real) : (term28 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5249944) (@lem5249943 s a)). Qed.
Lemma lem5249947 (a : real) (s : real -> Prop) : (term126 a s) = (term126 a s).
Proof. exact (eq_refl (term126 a s)). Qed.
Lemma lem5249948 (s : real -> Prop) (a : real) : (term127 s a) = (term128 s a).
Proof. exact (MK_COMB (@lem5249947 a s) (@lem5249942 s a)). Qed.
Lemma lem5249949 (s : real -> Prop) (a : real) : (term129 s a) = (term127 s a).
Proof. exact (@lem17045 (@IN real a s) (term28 s a)). Qed.
Lemma lem5249950 (s : real -> Prop) (a : real) : (term129 s a) = (term128 s a).
Proof. exact (TRANS (@lem5249949 s a) (@lem5249948 s a)). Qed.
Lemma lem5249952 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5249953 (s : real -> Prop) (a : real) : (term35 s a) = (term130 s a).
Proof. exact (MK_COMB (@lem5249952 a s) (@lem5249945 s a)). Qed.
Lemma lem5249954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5249955 (s : real -> Prop) (a : real) : (term131 s a) = (term132 s a).
Proof. exact (MK_COMB (@lem5249954) (@lem5249913 s a)). Qed.
Lemma lem5249956 (s : real -> Prop) (a : real) : (term133 s a) = (term134 s a).
Proof. exact (MK_COMB (@lem5249955 s a) (@lem5249953 s a)). Qed.
Lemma lem5249957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5249958 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (MK_COMB (@lem5249957) (@lem5249916 s a)). Qed.
Lemma lem5249959 (s : real -> Prop) (a : real) : (term137 s a) = (term138 s a).
Proof. exact (MK_COMB (@lem5249958 s a) (@lem5249950 s a)). Qed.
Lemma lem5249960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5249961 (s : real -> Prop) (a : real) : (term139 s a) = (term140 s a).
Proof. exact (MK_COMB (@lem5249960) (@lem5249959 s a)). Qed.
Lemma lem5249962 (s : real -> Prop) (a : real) : (term141 s a) = (term142 s a).
Proof. exact (MK_COMB (@lem5249961 s a) (@lem5249956 s a)). Qed.
Lemma lem5249963 (s : real -> Prop) (a : real) : (term143 s a) = (term141 s a).
Proof. exact (@lem17646 (term48 s a) (term35 s a)). Qed.
Lemma lem5249964 (s : real -> Prop) (a : real) : (term143 s a) = (term142 s a).
Proof. exact (TRANS (@lem5249963 s a) (@lem5249962 s a)). Qed.
Lemma lem5249966 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5249967 (s : real -> Prop) (a : real) : (term145 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5249966 s) (@lem5249964 s a)). Qed.
Lemma lem5249968 (s : real -> Prop) (a : real) : (term147 s a) = (term145 s a).
Proof. exact (@lem17362 (term20 s) ((term48 s a) = (term35 s a))). Qed.
Lemma lem5249969 (s : real -> Prop) (a : real) : (term147 s a) = (term146 s a).
Proof. exact (TRANS (@lem5249968 s a) (@lem5249967 s a)). Qed.
Lemma lem5249970 (P : type1022) : (term148 P) = (term149 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5249971 (a : real) : (term61 a) = (term150 a).
Proof. exact (@lem5249970 (term56 a)). Qed.
Lemma lem5249972 (s : real -> Prop) (a : real) : (term151 a s) = (term54 s a).
Proof. exact (eq_refl (term151 a s)). Qed.
Lemma lem5249973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5249974 (s : real -> Prop) (a : real) : (term152 a s) = (term147 s a).
Proof. exact (MK_COMB (@lem5249973) (@lem5249972 s a)). Qed.
Lemma lem5249975 (s : real -> Prop) (a : real) : (term152 a s) = (term146 s a).
Proof. exact (TRANS (@lem5249974 s a) (@lem5249969 s a)). Qed.
Lemma lem5249976 (a : real) : (term153 a) = (term154 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5249975 s a)). Qed.
Lemma lem5249977 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5249978 (a : real) : (term150 a) = (term155 a).
Proof. exact (MK_COMB (@lem5249977) (@lem5249976 a)). Qed.
Lemma lem5249979 (a : real) : (term61 a) = (term155 a).
Proof. exact (TRANS (@lem5249971 a) (@lem5249978 a)). Qed.
Lemma lem5250318 {A : Type'} (P : A -> Prop) (Q : Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5250319 (P : real -> Prop) (Q : Prop) : (term158 P Q) = (term159 P Q).
Proof. exact (@lem5250318 real P Q). Qed.
Lemma lem5250320 (s : real -> Prop) (a : real) : (term160 s a) = (term161 s a).
Proof. exact (@lem5250319 (term93 s a) (term119 s a)). Qed.
Lemma lem5250321 (s : real -> Prop) (x : real) (a : real) : (term101 s a x) = (term92 s x a).
Proof. exact (eq_refl (term101 s a x)). Qed.
Lemma lem5250322 (s : real -> Prop) (a : real) : (term162 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5250321 s x a)). Qed.
Lemma lem5250323 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250324 (s : real -> Prop) (a : real) : (term163 s a) = (term22 s a).
Proof. exact (MK_COMB (@lem5250323) (@lem5250322 s a)). Qed.
Lemma lem5250325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250326 (s : real -> Prop) (a : real) : (term164 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5250325) (@lem5250324 s a)). Qed.
Lemma lem5250327 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (eq_refl (term119 s a)). Qed.
Lemma lem5250328 (s : real -> Prop) (a : real) : (term160 s a) = (term125 s a).
Proof. exact (MK_COMB (@lem5250326 s a) (@lem5250327 s a)). Qed.
Lemma lem5250329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250330 (s : real -> Prop) (a : real) : (term165 s a) = (term166 s a).
Proof. exact (MK_COMB (@lem5250329) (@lem5250328 s a)). Qed.
Lemma lem5250331 (s : real -> Prop) (x : real) (a : real) : (term101 s a x) = (term92 s x a).
Proof. exact (eq_refl (term101 s a x)). Qed.
Lemma lem5250332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250333 (s : real -> Prop) (x : real) (a : real) : (term167 s a x) = (term168 s x a).
Proof. exact (MK_COMB (@lem5250332) (@lem5250331 s x a)). Qed.
Lemma lem5250334 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (eq_refl (term119 s a)). Qed.
Lemma lem5250335 (x : real) (s : real -> Prop) (a : real) : (term169 x s a) = (term170 x s a).
Proof. exact (MK_COMB (@lem5250333 s x a) (@lem5250334 s a)). Qed.
Lemma lem5250336 (s : real -> Prop) (a : real) : (term171 s a) = (term172 s a).
Proof. exact (fun_ext (fun x : real => @lem5250335 x s a)). Qed.
Lemma lem5250337 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250338 (s : real -> Prop) (a : real) : (term161 s a) = (term173 s a).
Proof. exact (MK_COMB (@lem5250337) (@lem5250336 s a)). Qed.
Lemma lem5250339 (s : real -> Prop) (a : real) : ((term160 s a) = (term161 s a)) = ((term125 s a) = (term173 s a)).
Proof. exact (MK_COMB (@lem5250330 s a) (@lem5250338 s a)). Qed.
Lemma lem5250340 (s : real -> Prop) (a : real) : (term125 s a) = (term173 s a).
Proof. exact (EQ_MP (@lem5250339 s a) (@lem5250320 s a)). Qed.
Lemma lem5250341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250342 (s : real -> Prop) (a : real) : (term136 s a) = (term174 s a).
Proof. exact (MK_COMB (@lem5250341) (@lem5250340 s a)). Qed.
Lemma lem5250344 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5250345 (P : Prop) (Q : real -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem5250344 real P Q). Qed.
Lemma lem5250346 (s : real -> Prop) (a : real) : (term179 s a) = (term180 s a).
Proof. exact (@lem5250345 (term181 a s) (term116 s a)). Qed.
Lemma lem5250347 (s : real -> Prop) (a : real) (y : real) : (term182 s a y) = (term107 s a y).
Proof. exact (eq_refl (term182 s a y)). Qed.
Lemma lem5250348 (s : real -> Prop) (a : real) : (term183 s a) = (term116 s a).
Proof. exact (fun_ext (fun y : real => @lem5250347 s a y)). Qed.
Lemma lem5250349 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250350 (s : real -> Prop) (a : real) : (term184 s a) = (term117 s a).
Proof. exact (MK_COMB (@lem5250349) (@lem5250348 s a)). Qed.
Lemma lem5250351 (a : real) (s : real -> Prop) : (term126 a s) = (term126 a s).
Proof. exact (eq_refl (term126 a s)). Qed.
Lemma lem5250352 (s : real -> Prop) (a : real) : (term179 s a) = (term128 s a).
Proof. exact (MK_COMB (@lem5250351 a s) (@lem5250350 s a)). Qed.
Lemma lem5250353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250354 (s : real -> Prop) (a : real) : (term185 s a) = (term186 s a).
Proof. exact (MK_COMB (@lem5250353) (@lem5250352 s a)). Qed.
Lemma lem5250355 (s : real -> Prop) (a : real) (y : real) : (term182 s a y) = (term107 s a y).
Proof. exact (eq_refl (term182 s a y)). Qed.
Lemma lem5250356 (a : real) (s : real -> Prop) : (term126 a s) = (term126 a s).
Proof. exact (eq_refl (term126 a s)). Qed.
Lemma lem5250357 (s : real -> Prop) (a : real) (y : real) : (term187 s a y) = (term188 s a y).
Proof. exact (MK_COMB (@lem5250356 a s) (@lem5250355 s a y)). Qed.
Lemma lem5250358 (s : real -> Prop) (a : real) : (term189 s a) = (term190 s a).
Proof. exact (fun_ext (fun y : real => @lem5250357 s a y)). Qed.
Lemma lem5250359 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250360 (s : real -> Prop) (a : real) : (term180 s a) = (term191 s a).
Proof. exact (MK_COMB (@lem5250359) (@lem5250358 s a)). Qed.
Lemma lem5250361 (s : real -> Prop) (a : real) : ((term179 s a) = (term180 s a)) = ((term128 s a) = (term191 s a)).
Proof. exact (MK_COMB (@lem5250354 s a) (@lem5250360 s a)). Qed.
Lemma lem5250362 (s : real -> Prop) (a : real) : (term128 s a) = (term191 s a).
Proof. exact (EQ_MP (@lem5250361 s a) (@lem5250346 s a)). Qed.
Lemma lem5250363 (s : real -> Prop) (a : real) : (term138 s a) = (term192 s a).
Proof. exact (MK_COMB (@lem5250342 s a) (@lem5250362 s a)). Qed.
Lemma lem5250365 {A : Type'} (P : A -> Prop) (Q : Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5250366 (P : real -> Prop) (Q : Prop) : (term158 P Q) = (term159 P Q).
Proof. exact (@lem5250365 real P Q). Qed.
Lemma lem5250367 (s : real -> Prop) (a : real) : (term193 s a) = (term194 s a).
Proof. exact (@lem5250366 (term172 s a) (term191 s a)). Qed.
Lemma lem5250368 (x : real) (s : real -> Prop) (a : real) : (term195 s a x) = (term170 x s a).
Proof. exact (eq_refl (term195 s a x)). Qed.
Lemma lem5250369 (s : real -> Prop) (a : real) : (term196 s a) = (term172 s a).
Proof. exact (fun_ext (fun x : real => @lem5250368 x s a)). Qed.
Lemma lem5250370 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250371 (s : real -> Prop) (a : real) : (term197 s a) = (term173 s a).
Proof. exact (MK_COMB (@lem5250370) (@lem5250369 s a)). Qed.
Lemma lem5250372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250373 (s : real -> Prop) (a : real) : (term198 s a) = (term174 s a).
Proof. exact (MK_COMB (@lem5250372) (@lem5250371 s a)). Qed.
Lemma lem5250374 (s : real -> Prop) (a : real) : (term191 s a) = (term191 s a).
Proof. exact (eq_refl (term191 s a)). Qed.
Lemma lem5250375 (s : real -> Prop) (a : real) : (term193 s a) = (term192 s a).
Proof. exact (MK_COMB (@lem5250373 s a) (@lem5250374 s a)). Qed.
Lemma lem5250376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250377 (s : real -> Prop) (a : real) : (term199 s a) = (term200 s a).
Proof. exact (MK_COMB (@lem5250376) (@lem5250375 s a)). Qed.
Lemma lem5250378 (x : real) (s : real -> Prop) (a : real) : (term195 s a x) = (term170 x s a).
Proof. exact (eq_refl (term195 s a x)). Qed.
Lemma lem5250379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250380 (x : real) (s : real -> Prop) (a : real) : (term201 s a x) = (term202 x s a).
Proof. exact (MK_COMB (@lem5250379) (@lem5250378 x s a)). Qed.
Lemma lem5250381 (s : real -> Prop) (a : real) : (term191 s a) = (term191 s a).
Proof. exact (eq_refl (term191 s a)). Qed.
Lemma lem5250382 (x : real) (s : real -> Prop) (a : real) : (term203 x s a) = (term204 x s a).
Proof. exact (MK_COMB (@lem5250380 x s a) (@lem5250381 s a)). Qed.
Lemma lem5250383 (s : real -> Prop) (a : real) : (term205 s a) = (term206 s a).
Proof. exact (fun_ext (fun x : real => @lem5250382 x s a)). Qed.
Lemma lem5250384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250385 (s : real -> Prop) (a : real) : (term194 s a) = (term207 s a).
Proof. exact (MK_COMB (@lem5250384) (@lem5250383 s a)). Qed.
Lemma lem5250386 (s : real -> Prop) (a : real) : ((term193 s a) = (term194 s a)) = ((term192 s a) = (term207 s a)).
Proof. exact (MK_COMB (@lem5250377 s a) (@lem5250385 s a)). Qed.
Lemma lem5250387 (s : real -> Prop) (a : real) : (term192 s a) = (term207 s a).
Proof. exact (EQ_MP (@lem5250386 s a) (@lem5250367 s a)). Qed.
Lemma lem5250389 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5250390 (P : Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem5250389 real P Q). Qed.
Lemma lem5250391 (x : real) (s : real -> Prop) (a : real) : (term212 x s a) = (term213 x s a).
Proof. exact (@lem5250390 (term170 x s a) (term190 s a)). Qed.
Lemma lem5250392 (s : real -> Prop) (a : real) (y : real) : (term214 s a y) = (term188 s a y).
Proof. exact (eq_refl (term214 s a y)). Qed.
Lemma lem5250393 (s : real -> Prop) (a : real) : (term215 s a) = (term190 s a).
Proof. exact (fun_ext (fun y : real => @lem5250392 s a y)). Qed.
Lemma lem5250394 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250395 (s : real -> Prop) (a : real) : (term216 s a) = (term191 s a).
Proof. exact (MK_COMB (@lem5250394) (@lem5250393 s a)). Qed.
Lemma lem5250396 (x : real) (s : real -> Prop) (a : real) : (term202 x s a) = (term202 x s a).
Proof. exact (eq_refl (term202 x s a)). Qed.
Lemma lem5250397 (x : real) (s : real -> Prop) (a : real) : (term212 x s a) = (term204 x s a).
Proof. exact (MK_COMB (@lem5250396 x s a) (@lem5250395 s a)). Qed.
Lemma lem5250398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250399 (x : real) (s : real -> Prop) (a : real) : (term217 x s a) = (term218 x s a).
Proof. exact (MK_COMB (@lem5250398) (@lem5250397 x s a)). Qed.
Lemma lem5250400 (s : real -> Prop) (a : real) (y : real) : (term214 s a y) = (term188 s a y).
Proof. exact (eq_refl (term214 s a y)). Qed.
Lemma lem5250401 (x : real) (s : real -> Prop) (a : real) : (term202 x s a) = (term202 x s a).
Proof. exact (eq_refl (term202 x s a)). Qed.
Lemma lem5250402 (x : real) (s : real -> Prop) (a : real) (y : real) : (term219 x s a y) = (term220 x s a y).
Proof. exact (MK_COMB (@lem5250401 x s a) (@lem5250400 s a y)). Qed.
Lemma lem5250403 (x : real) (s : real -> Prop) (a : real) : (term221 x s a) = (term222 x s a).
Proof. exact (fun_ext (fun y : real => @lem5250402 x s a y)). Qed.
Lemma lem5250404 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250405 (x : real) (s : real -> Prop) (a : real) : (term213 x s a) = (term223 x s a).
Proof. exact (MK_COMB (@lem5250404) (@lem5250403 x s a)). Qed.
Lemma lem5250406 (x : real) (s : real -> Prop) (a : real) : ((term212 x s a) = (term213 x s a)) = ((term204 x s a) = (term223 x s a)).
Proof. exact (MK_COMB (@lem5250399 x s a) (@lem5250405 x s a)). Qed.
Lemma lem5250407 (x : real) (s : real -> Prop) (a : real) : (term204 x s a) = (term223 x s a).
Proof. exact (EQ_MP (@lem5250406 x s a) (@lem5250391 x s a)). Qed.
Lemma lem5250408 (s : real -> Prop) (a : real) : (term206 s a) = (term224 s a).
Proof. exact (fun_ext (fun x : real => @lem5250407 x s a)). Qed.
Lemma lem5250409 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250410 (s : real -> Prop) (a : real) : (term207 s a) = (term225 s a).
Proof. exact (MK_COMB (@lem5250409) (@lem5250408 s a)). Qed.
Lemma lem5250411 (s : real -> Prop) (a : real) : (term192 s a) = (term225 s a).
Proof. exact (TRANS (@lem5250387 s a) (@lem5250410 s a)). Qed.
Lemma lem5250412 (s : real -> Prop) (a : real) : (term138 s a) = (term225 s a).
Proof. exact (TRANS (@lem5250363 s a) (@lem5250411 s a)). Qed.
Lemma lem5250413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250414 (s : real -> Prop) (a : real) : (term140 s a) = (term226 s a).
Proof. exact (MK_COMB (@lem5250413) (@lem5250412 s a)). Qed.
Lemma lem5250416 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5250417 (P : Prop) (Q : real -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem5250416 real P Q). Qed.
Lemma lem5250418 (s : real -> Prop) (a : real) : (term227 s a) = (term228 s a).
Proof. exact (@lem5250417 (term105 s a) (term116 s a)). Qed.
Lemma lem5250419 (s : real -> Prop) (a : real) (x : real) : (term182 s a x) = (term107 s a x).
Proof. exact (eq_refl (term182 s a x)). Qed.
Lemma lem5250420 (s : real -> Prop) (a : real) : (term183 s a) = (term116 s a).
Proof. exact (fun_ext (fun x : real => @lem5250419 s a x)). Qed.
Lemma lem5250421 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250422 (s : real -> Prop) (a : real) : (term184 s a) = (term117 s a).
Proof. exact (MK_COMB (@lem5250421) (@lem5250420 s a)). Qed.
Lemma lem5250423 (s : real -> Prop) (a : real) : (term121 s a) = (term121 s a).
Proof. exact (eq_refl (term121 s a)). Qed.
Lemma lem5250424 (s : real -> Prop) (a : real) : (term227 s a) = (term123 s a).
Proof. exact (MK_COMB (@lem5250423 s a) (@lem5250422 s a)). Qed.
Lemma lem5250425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250426 (s : real -> Prop) (a : real) : (term229 s a) = (term230 s a).
Proof. exact (MK_COMB (@lem5250425) (@lem5250424 s a)). Qed.
Lemma lem5250427 (s : real -> Prop) (a : real) (x : real) : (term182 s a x) = (term107 s a x).
Proof. exact (eq_refl (term182 s a x)). Qed.
Lemma lem5250428 (s : real -> Prop) (a : real) : (term121 s a) = (term121 s a).
Proof. exact (eq_refl (term121 s a)). Qed.
Lemma lem5250429 (s : real -> Prop) (a : real) (x : real) : (term231 s a x) = (term232 s a x).
Proof. exact (MK_COMB (@lem5250428 s a) (@lem5250427 s a x)). Qed.
Lemma lem5250430 (s : real -> Prop) (a : real) : (term233 s a) = (term234 s a).
Proof. exact (fun_ext (fun x : real => @lem5250429 s a x)). Qed.
Lemma lem5250431 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250432 (s : real -> Prop) (a : real) : (term228 s a) = (term235 s a).
Proof. exact (MK_COMB (@lem5250431) (@lem5250430 s a)). Qed.
Lemma lem5250433 (s : real -> Prop) (a : real) : ((term227 s a) = (term228 s a)) = ((term123 s a) = (term235 s a)).
Proof. exact (MK_COMB (@lem5250426 s a) (@lem5250432 s a)). Qed.
Lemma lem5250434 (s : real -> Prop) (a : real) : (term123 s a) = (term235 s a).
Proof. exact (EQ_MP (@lem5250433 s a) (@lem5250418 s a)). Qed.
Lemma lem5250435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250436 (s : real -> Prop) (a : real) : (term132 s a) = (term236 s a).
Proof. exact (MK_COMB (@lem5250435) (@lem5250434 s a)). Qed.
Lemma lem5250437 (s : real -> Prop) (a : real) : (term130 s a) = (term130 s a).
Proof. exact (eq_refl (term130 s a)). Qed.
Lemma lem5250438 (s : real -> Prop) (a : real) : (term134 s a) = (term237 s a).
Proof. exact (MK_COMB (@lem5250436 s a) (@lem5250437 s a)). Qed.
Lemma lem5250440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5250441 (P : real -> Prop) (Q : Prop) : (term158 P Q) = (term159 P Q).
Proof. exact (@lem5250440 real P Q). Qed.
Lemma lem5250442 (s : real -> Prop) (a : real) : (term238 s a) = (term239 s a).
Proof. exact (@lem5250441 (term234 s a) (term130 s a)). Qed.
Lemma lem5250443 (s : real -> Prop) (a : real) (x : real) : (term240 s a x) = (term232 s a x).
Proof. exact (eq_refl (term240 s a x)). Qed.
Lemma lem5250444 (s : real -> Prop) (a : real) : (term241 s a) = (term234 s a).
Proof. exact (fun_ext (fun x : real => @lem5250443 s a x)). Qed.
Lemma lem5250445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250446 (s : real -> Prop) (a : real) : (term242 s a) = (term235 s a).
Proof. exact (MK_COMB (@lem5250445) (@lem5250444 s a)). Qed.
Lemma lem5250447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250448 (s : real -> Prop) (a : real) : (term243 s a) = (term236 s a).
Proof. exact (MK_COMB (@lem5250447) (@lem5250446 s a)). Qed.
Lemma lem5250449 (s : real -> Prop) (a : real) : (term130 s a) = (term130 s a).
Proof. exact (eq_refl (term130 s a)). Qed.
Lemma lem5250450 (s : real -> Prop) (a : real) : (term238 s a) = (term237 s a).
Proof. exact (MK_COMB (@lem5250448 s a) (@lem5250449 s a)). Qed.
Lemma lem5250451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250452 (s : real -> Prop) (a : real) : (term244 s a) = (term245 s a).
Proof. exact (MK_COMB (@lem5250451) (@lem5250450 s a)). Qed.
Lemma lem5250453 (s : real -> Prop) (a : real) (x : real) : (term240 s a x) = (term232 s a x).
Proof. exact (eq_refl (term240 s a x)). Qed.
Lemma lem5250454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250455 (s : real -> Prop) (a : real) (x : real) : (term246 s a x) = (term247 s a x).
Proof. exact (MK_COMB (@lem5250454) (@lem5250453 s a x)). Qed.
Lemma lem5250456 (s : real -> Prop) (a : real) : (term130 s a) = (term130 s a).
Proof. exact (eq_refl (term130 s a)). Qed.
Lemma lem5250457 (x : real) (s : real -> Prop) (a : real) : (term248 x s a) = (term249 x s a).
Proof. exact (MK_COMB (@lem5250455 s a x) (@lem5250456 s a)). Qed.
Lemma lem5250458 (s : real -> Prop) (a : real) : (term250 s a) = (term251 s a).
Proof. exact (fun_ext (fun x : real => @lem5250457 x s a)). Qed.
Lemma lem5250459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250460 (s : real -> Prop) (a : real) : (term239 s a) = (term252 s a).
Proof. exact (MK_COMB (@lem5250459) (@lem5250458 s a)). Qed.
Lemma lem5250461 (s : real -> Prop) (a : real) : ((term238 s a) = (term239 s a)) = ((term237 s a) = (term252 s a)).
Proof. exact (MK_COMB (@lem5250452 s a) (@lem5250460 s a)). Qed.
Lemma lem5250462 (s : real -> Prop) (a : real) : (term237 s a) = (term252 s a).
Proof. exact (EQ_MP (@lem5250461 s a) (@lem5250442 s a)). Qed.
Lemma lem5250463 (s : real -> Prop) (a : real) : (term134 s a) = (term252 s a).
Proof. exact (TRANS (@lem5250438 s a) (@lem5250462 s a)). Qed.
Lemma lem5250464 (s : real -> Prop) (a : real) : (term142 s a) = (term253 s a).
Proof. exact (MK_COMB (@lem5250414 s a) (@lem5250463 s a)). Qed.
Lemma lem5250466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5250467 (P : real -> Prop) (Q : real -> Prop) : (term256 P Q) = (term257 P Q).
Proof. exact (@lem5250466 real P Q). Qed.
Lemma lem5250468 (s : real -> Prop) (a : real) : (term258 s a) = (term259 s a).
Proof. exact (@lem5250467 (term224 s a) (term251 s a)). Qed.
Lemma lem5250469 (x : real) (s : real -> Prop) (a : real) : (term260 s a x) = (term223 x s a).
Proof. exact (eq_refl (term260 s a x)). Qed.
Lemma lem5250470 (s : real -> Prop) (a : real) : (term261 s a) = (term224 s a).
Proof. exact (fun_ext (fun x : real => @lem5250469 x s a)). Qed.
Lemma lem5250471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250472 (s : real -> Prop) (a : real) : (term262 s a) = (term225 s a).
Proof. exact (MK_COMB (@lem5250471) (@lem5250470 s a)). Qed.
Lemma lem5250473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250474 (s : real -> Prop) (a : real) : (term263 s a) = (term226 s a).
Proof. exact (MK_COMB (@lem5250473) (@lem5250472 s a)). Qed.
Lemma lem5250475 (x : real) (s : real -> Prop) (a : real) : (term264 s a x) = (term249 x s a).
Proof. exact (eq_refl (term264 s a x)). Qed.
Lemma lem5250476 (s : real -> Prop) (a : real) : (term265 s a) = (term251 s a).
Proof. exact (fun_ext (fun x : real => @lem5250475 x s a)). Qed.
Lemma lem5250477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250478 (s : real -> Prop) (a : real) : (term266 s a) = (term252 s a).
Proof. exact (MK_COMB (@lem5250477) (@lem5250476 s a)). Qed.
Lemma lem5250479 (s : real -> Prop) (a : real) : (term258 s a) = (term253 s a).
Proof. exact (MK_COMB (@lem5250474 s a) (@lem5250478 s a)). Qed.
Lemma lem5250480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250481 (s : real -> Prop) (a : real) : (term267 s a) = (term268 s a).
Proof. exact (MK_COMB (@lem5250480) (@lem5250479 s a)). Qed.
Lemma lem5250482 (x : real) (s : real -> Prop) (a : real) : (term260 s a x) = (term223 x s a).
Proof. exact (eq_refl (term260 s a x)). Qed.
Lemma lem5250483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250484 (x : real) (s : real -> Prop) (a : real) : (term269 s a x) = (term270 x s a).
Proof. exact (MK_COMB (@lem5250483) (@lem5250482 x s a)). Qed.
Lemma lem5250485 (x : real) (s : real -> Prop) (a : real) : (term264 s a x) = (term249 x s a).
Proof. exact (eq_refl (term264 s a x)). Qed.
Lemma lem5250486 (x : real) (s : real -> Prop) (a : real) : (term271 s a x) = (term272 x s a).
Proof. exact (MK_COMB (@lem5250484 x s a) (@lem5250485 x s a)). Qed.
Lemma lem5250487 (s : real -> Prop) (a : real) : (term273 s a) = (term274 s a).
Proof. exact (fun_ext (fun x : real => @lem5250486 x s a)). Qed.
Lemma lem5250488 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250489 (s : real -> Prop) (a : real) : (term259 s a) = (term275 s a).
Proof. exact (MK_COMB (@lem5250488) (@lem5250487 s a)). Qed.
Lemma lem5250490 (s : real -> Prop) (a : real) : ((term258 s a) = (term259 s a)) = ((term253 s a) = (term275 s a)).
Proof. exact (MK_COMB (@lem5250481 s a) (@lem5250489 s a)). Qed.
Lemma lem5250491 (s : real -> Prop) (a : real) : (term253 s a) = (term275 s a).
Proof. exact (EQ_MP (@lem5250490 s a) (@lem5250468 s a)). Qed.
Lemma lem5250493 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5250494 (P : real -> Prop) (Q : Prop) : (term278 P Q) = (term279 P Q).
Proof. exact (@lem5250493 real P Q). Qed.
Lemma lem5250495 (x : real) (s : real -> Prop) (a : real) : (term280 x s a) = (term281 x s a).
Proof. exact (@lem5250494 (term222 x s a) (term249 x s a)). Qed.
Lemma lem5250496 (x : real) (s : real -> Prop) (a : real) (y : real) : (term282 x s a y) = (term220 x s a y).
Proof. exact (eq_refl (term282 x s a y)). Qed.
Lemma lem5250497 (x : real) (s : real -> Prop) (a : real) : (term283 x s a) = (term222 x s a).
Proof. exact (fun_ext (fun y : real => @lem5250496 x s a y)). Qed.
Lemma lem5250498 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250499 (x : real) (s : real -> Prop) (a : real) : (term284 x s a) = (term223 x s a).
Proof. exact (MK_COMB (@lem5250498) (@lem5250497 x s a)). Qed.
Lemma lem5250500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250501 (x : real) (s : real -> Prop) (a : real) : (term285 x s a) = (term270 x s a).
Proof. exact (MK_COMB (@lem5250500) (@lem5250499 x s a)). Qed.
Lemma lem5250502 (x : real) (s : real -> Prop) (a : real) : (term249 x s a) = (term249 x s a).
Proof. exact (eq_refl (term249 x s a)). Qed.
Lemma lem5250503 (x : real) (s : real -> Prop) (a : real) : (term280 x s a) = (term272 x s a).
Proof. exact (MK_COMB (@lem5250501 x s a) (@lem5250502 x s a)). Qed.
Lemma lem5250504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250505 (x : real) (s : real -> Prop) (a : real) : (term286 x s a) = (term287 x s a).
Proof. exact (MK_COMB (@lem5250504) (@lem5250503 x s a)). Qed.
Lemma lem5250506 (x : real) (s : real -> Prop) (a : real) (y : real) : (term282 x s a y) = (term220 x s a y).
Proof. exact (eq_refl (term282 x s a y)). Qed.
Lemma lem5250507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250508 (x : real) (s : real -> Prop) (a : real) (y : real) : (term288 x s a y) = (term289 x s a y).
Proof. exact (MK_COMB (@lem5250507) (@lem5250506 x s a y)). Qed.
Lemma lem5250509 (x : real) (s : real -> Prop) (a : real) : (term249 x s a) = (term249 x s a).
Proof. exact (eq_refl (term249 x s a)). Qed.
Lemma lem5250510 (y : real) (x : real) (s : real -> Prop) (a : real) : (term290 y x s a) = (term291 y x s a).
Proof. exact (MK_COMB (@lem5250508 x s a y) (@lem5250509 x s a)). Qed.
Lemma lem5250511 (x : real) (s : real -> Prop) (a : real) : (term292 x s a) = (term293 x s a).
Proof. exact (fun_ext (fun y : real => @lem5250510 y x s a)). Qed.
Lemma lem5250512 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250513 (x : real) (s : real -> Prop) (a : real) : (term281 x s a) = (term294 x s a).
Proof. exact (MK_COMB (@lem5250512) (@lem5250511 x s a)). Qed.
Lemma lem5250514 (x : real) (s : real -> Prop) (a : real) : ((term280 x s a) = (term281 x s a)) = ((term272 x s a) = (term294 x s a)).
Proof. exact (MK_COMB (@lem5250505 x s a) (@lem5250513 x s a)). Qed.
Lemma lem5250515 (x : real) (s : real -> Prop) (a : real) : (term272 x s a) = (term294 x s a).
Proof. exact (EQ_MP (@lem5250514 x s a) (@lem5250495 x s a)). Qed.
Lemma lem5250516 (s : real -> Prop) (a : real) : (term274 s a) = (term295 s a).
Proof. exact (fun_ext (fun x : real => @lem5250515 x s a)). Qed.
Lemma lem5250517 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250518 (s : real -> Prop) (a : real) : (term275 s a) = (term296 s a).
Proof. exact (MK_COMB (@lem5250517) (@lem5250516 s a)). Qed.
Lemma lem5250519 (s : real -> Prop) (a : real) : (term253 s a) = (term296 s a).
Proof. exact (TRANS (@lem5250491 s a) (@lem5250518 s a)). Qed.
Lemma lem5250520 (s : real -> Prop) (a : real) : (term142 s a) = (term296 s a).
Proof. exact (TRANS (@lem5250464 s a) (@lem5250519 s a)). Qed.
Lemma lem5250521 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5250522 (s : real -> Prop) (a : real) : (term146 s a) = (term297 s a).
Proof. exact (MK_COMB (@lem5250521 s) (@lem5250520 s a)). Qed.
Lemma lem5250524 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5250525 (P : Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem5250524 real P Q). Qed.
Lemma lem5250526 (s : real -> Prop) (a : real) : (term298 s a) = (term299 s a).
Proof. exact (@lem5250525 (term20 s) (term295 s a)). Qed.
Lemma lem5250527 (x : real) (s : real -> Prop) (a : real) : (term300 s a x) = (term294 x s a).
Proof. exact (eq_refl (term300 s a x)). Qed.
Lemma lem5250528 (s : real -> Prop) (a : real) : (term301 s a) = (term295 s a).
Proof. exact (fun_ext (fun x : real => @lem5250527 x s a)). Qed.
Lemma lem5250529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250530 (s : real -> Prop) (a : real) : (term302 s a) = (term296 s a).
Proof. exact (MK_COMB (@lem5250529) (@lem5250528 s a)). Qed.
Lemma lem5250531 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5250532 (s : real -> Prop) (a : real) : (term298 s a) = (term297 s a).
Proof. exact (MK_COMB (@lem5250531 s) (@lem5250530 s a)). Qed.
Lemma lem5250533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250534 (s : real -> Prop) (a : real) : (term303 s a) = (term304 s a).
Proof. exact (MK_COMB (@lem5250533) (@lem5250532 s a)). Qed.
Lemma lem5250535 (x : real) (s : real -> Prop) (a : real) : (term300 s a x) = (term294 x s a).
Proof. exact (eq_refl (term300 s a x)). Qed.
Lemma lem5250536 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5250537 (x : real) (s : real -> Prop) (a : real) : (term305 s a x) = (term306 x s a).
Proof. exact (MK_COMB (@lem5250536 s) (@lem5250535 x s a)). Qed.
Lemma lem5250538 (s : real -> Prop) (a : real) : (term307 s a) = (term308 s a).
Proof. exact (fun_ext (fun x : real => @lem5250537 x s a)). Qed.
Lemma lem5250539 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250540 (s : real -> Prop) (a : real) : (term299 s a) = (term309 s a).
Proof. exact (MK_COMB (@lem5250539) (@lem5250538 s a)). Qed.
Lemma lem5250541 (s : real -> Prop) (a : real) : ((term298 s a) = (term299 s a)) = ((term297 s a) = (term309 s a)).
Proof. exact (MK_COMB (@lem5250534 s a) (@lem5250540 s a)). Qed.
Lemma lem5250542 (s : real -> Prop) (a : real) : (term297 s a) = (term309 s a).
Proof. exact (EQ_MP (@lem5250541 s a) (@lem5250526 s a)). Qed.
Lemma lem5250544 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5250545 (P : Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem5250544 real P Q). Qed.
Lemma lem5250546 (x : real) (s : real -> Prop) (a : real) : (term310 x s a) = (term311 x s a).
Proof. exact (@lem5250545 (term20 s) (term293 x s a)). Qed.
Lemma lem5250547 (y : real) (x : real) (s : real -> Prop) (a : real) : (term312 x s a y) = (term291 y x s a).
Proof. exact (eq_refl (term312 x s a y)). Qed.
Lemma lem5250548 (x : real) (s : real -> Prop) (a : real) : (term313 x s a) = (term293 x s a).
Proof. exact (fun_ext (fun y : real => @lem5250547 y x s a)). Qed.
Lemma lem5250549 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250550 (x : real) (s : real -> Prop) (a : real) : (term314 x s a) = (term294 x s a).
Proof. exact (MK_COMB (@lem5250549) (@lem5250548 x s a)). Qed.
Lemma lem5250551 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5250552 (x : real) (s : real -> Prop) (a : real) : (term310 x s a) = (term306 x s a).
Proof. exact (MK_COMB (@lem5250551 s) (@lem5250550 x s a)). Qed.
Lemma lem5250553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250554 (x : real) (s : real -> Prop) (a : real) : (term315 x s a) = (term316 x s a).
Proof. exact (MK_COMB (@lem5250553) (@lem5250552 x s a)). Qed.
Lemma lem5250555 (y : real) (x : real) (s : real -> Prop) (a : real) : (term312 x s a y) = (term291 y x s a).
Proof. exact (eq_refl (term312 x s a y)). Qed.
Lemma lem5250556 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5250557 (y : real) (x : real) (s : real -> Prop) (a : real) : (term317 x s a y) = (term318 y x s a).
Proof. exact (MK_COMB (@lem5250556 s) (@lem5250555 y x s a)). Qed.
Lemma lem5250558 (x : real) (s : real -> Prop) (a : real) : (term319 x s a) = (term320 x s a).
Proof. exact (fun_ext (fun y : real => @lem5250557 y x s a)). Qed.
Lemma lem5250559 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250560 (x : real) (s : real -> Prop) (a : real) : (term311 x s a) = (term321 x s a).
Proof. exact (MK_COMB (@lem5250559) (@lem5250558 x s a)). Qed.
Lemma lem5250561 (x : real) (s : real -> Prop) (a : real) : ((term310 x s a) = (term311 x s a)) = ((term306 x s a) = (term321 x s a)).
Proof. exact (MK_COMB (@lem5250554 x s a) (@lem5250560 x s a)). Qed.
Lemma lem5250562 (x : real) (s : real -> Prop) (a : real) : (term306 x s a) = (term321 x s a).
Proof. exact (EQ_MP (@lem5250561 x s a) (@lem5250546 x s a)). Qed.
Lemma lem5250563 (s : real -> Prop) (a : real) : (term308 s a) = (term322 s a).
Proof. exact (fun_ext (fun x : real => @lem5250562 x s a)). Qed.
Lemma lem5250564 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5250565 (s : real -> Prop) (a : real) : (term309 s a) = (term323 s a).
Proof. exact (MK_COMB (@lem5250564) (@lem5250563 s a)). Qed.
Lemma lem5250566 (s : real -> Prop) (a : real) : (term297 s a) = (term323 s a).
Proof. exact (TRANS (@lem5250542 s a) (@lem5250565 s a)). Qed.
Lemma lem5250567 (s : real -> Prop) (a : real) : (term146 s a) = (term323 s a).
Proof. exact (TRANS (@lem5250522 s a) (@lem5250566 s a)). Qed.
Lemma lem5250568 (a : real) : (term154 a) = (term324 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5250567 s a)). Qed.
Lemma lem5250569 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5250571 (a : real) : (term155 a) = (term325 a).
Proof. exact (MK_COMB (@lem5250569) (@lem5250568 a)). Qed.
Lemma lem5250572 (a : real) : (term61 a) = (term325 a).
Proof. exact (TRANS (@lem5249979 a) (@lem5250571 a)). Qed.
Lemma lem5250573 (a : real) (h1 : term61 a) : term325 a.
Proof. exact (EQ_MP (@lem5250572 a) (@lem5249848 a h1)). Qed.
Lemma lem5250582 (y : real) (x : real) : (term326 y x) = (term327 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5250587 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5250588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5250589 (y : real) (x : real) : (term328 y x) = (term329 y x).
Proof. exact (MK_COMB (@lem5250588) (@lem5250582 y x)). Qed.
Lemma lem5250590 (x : real) (y : real) : (term330 x y) = (term331 x y).
Proof. exact (MK_COMB (@lem5250589 y x) (@lem5250587 x y)). Qed.
Lemma lem5250595 (x : real) (y : real) : (term332 x y) = (term332 x y).
Proof. exact (eq_refl (term332 x y)). Qed.
Lemma lem5250596 (x : real) (y : real) : (term333 x y) = (term334 x y).
Proof. exact (MK_COMB (@lem5250595 x y) (@lem5250590 x y)). Qed.
Lemma lem5250597 (x : real) (y : real) : ((term7 y x) = (x = y)) = (term333 x y).
Proof. exact (@lem17784 (term7 y x) (x = y)). Qed.
Lemma lem5250598 (x : real) (y : real) : ((term7 y x) = (x = y)) = (term334 x y).
Proof. exact (TRANS (@lem5250597 x y) (@lem5250596 x y)). Qed.
Lemma lem5250599 (x : real) : (term8 x) = (term335 x).
Proof. exact (fun_ext (fun y : real => @lem5250598 x y)). Qed.
Lemma lem5250600 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250601 (x : real) : (term10 x) = (term336 x).
Proof. exact (MK_COMB (@lem5250600) (@lem5250599 x)). Qed.
Lemma lem5250602 : term12 = term337.
Proof. exact (fun_ext (fun x : real => @lem5250601 x)). Qed.
Lemma lem5250603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250604 : term14 = term338.
Proof. exact (MK_COMB (@lem5250603) (@lem5250602)). Qed.
Lemma lem5250610 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term339 A P Q) = (term340 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5250611 (P : real -> Prop) (Q : real -> Prop) : (term341 P Q) = (term342 P Q).
Proof. exact (@lem5250610 real P Q). Qed.
Lemma lem5250612 (x : real) : (term343 x) = (term344 x).
Proof. exact (@lem5250611 (term345 x) (term346 x)). Qed.
Lemma lem5250613 (x : real) (y : real) : (term347 x y) = (term348 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5250614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250615 (x : real) (y : real) : (term349 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem5250614) (@lem5250613 x y)). Qed.
Lemma lem5250616 (x : real) (y : real) : (term350 x y) = (term331 x y).
Proof. exact (eq_refl (term350 x y)). Qed.
Lemma lem5250617 (x : real) (y : real) : (term351 x y) = (term334 x y).
Proof. exact (MK_COMB (@lem5250615 x y) (@lem5250616 x y)). Qed.
Lemma lem5250618 (x : real) : (term352 x) = (term335 x).
Proof. exact (fun_ext (fun y : real => @lem5250617 x y)). Qed.
Lemma lem5250619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250620 (x : real) : (term343 x) = (term336 x).
Proof. exact (MK_COMB (@lem5250619) (@lem5250618 x)). Qed.
Lemma lem5250621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250622 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem5250621) (@lem5250620 x)). Qed.
Lemma lem5250623 (x : real) (y : real) : (term347 x y) = (term348 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5250624 (x : real) : (term355 x) = (term345 x).
Proof. exact (fun_ext (fun y : real => @lem5250623 x y)). Qed.
Lemma lem5250625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250626 (x : real) : (term356 x) = (term357 x).
Proof. exact (MK_COMB (@lem5250625) (@lem5250624 x)). Qed.
Lemma lem5250627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250628 (x : real) : (term358 x) = (term359 x).
Proof. exact (MK_COMB (@lem5250627) (@lem5250626 x)). Qed.
Lemma lem5250629 (x : real) (y : real) : (term350 x y) = (term331 x y).
Proof. exact (eq_refl (term350 x y)). Qed.
Lemma lem5250630 (x : real) : (term360 x) = (term346 x).
Proof. exact (fun_ext (fun y : real => @lem5250629 x y)). Qed.
Lemma lem5250631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250632 (x : real) : (term361 x) = (term362 x).
Proof. exact (MK_COMB (@lem5250631) (@lem5250630 x)). Qed.
Lemma lem5250633 (x : real) : (term344 x) = (term363 x).
Proof. exact (MK_COMB (@lem5250628 x) (@lem5250632 x)). Qed.
Lemma lem5250634 (x : real) : ((term343 x) = (term344 x)) = ((term336 x) = (term363 x)).
Proof. exact (MK_COMB (@lem5250622 x) (@lem5250633 x)). Qed.
Lemma lem5250635 (x : real) : (term336 x) = (term363 x).
Proof. exact (EQ_MP (@lem5250634 x) (@lem5250612 x)). Qed.
Lemma lem5250732 : term337 = term364.
Proof. exact (fun_ext (fun x : real => @lem5250635 x)). Qed.
Lemma lem5250733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250734 : term338 = term365.
Proof. exact (MK_COMB (@lem5250733) (@lem5250732)). Qed.
Lemma lem5250736 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term339 A P Q) = (term340 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5250737 (P : real -> Prop) (Q : real -> Prop) : (term341 P Q) = (term342 P Q).
Proof. exact (@lem5250736 real P Q). Qed.
Lemma lem5250738 : term366 = term367.
Proof. exact (@lem5250737 term368 term369). Qed.
Lemma lem5250739 (x : real) : (term370 x) = (term357 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem5250740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250741 (x : real) : (term371 x) = (term359 x).
Proof. exact (MK_COMB (@lem5250740) (@lem5250739 x)). Qed.
Lemma lem5250742 (x : real) : (term372 x) = (term362 x).
Proof. exact (eq_refl (term372 x)). Qed.
Lemma lem5250743 (x : real) : (term373 x) = (term363 x).
Proof. exact (MK_COMB (@lem5250741 x) (@lem5250742 x)). Qed.
Lemma lem5250744 : term374 = term364.
Proof. exact (fun_ext (fun x : real => @lem5250743 x)). Qed.
Lemma lem5250745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250746 : term366 = term365.
Proof. exact (MK_COMB (@lem5250745) (@lem5250744)). Qed.
Lemma lem5250747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5250748 : term375 = term376.
Proof. exact (MK_COMB (@lem5250747) (@lem5250746)). Qed.
Lemma lem5250749 (x : real) : (term370 x) = (term357 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem5250750 : term377 = term368.
Proof. exact (fun_ext (fun x : real => @lem5250749 x)). Qed.
Lemma lem5250751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250752 : term378 = term379.
Proof. exact (MK_COMB (@lem5250751) (@lem5250750)). Qed.
Lemma lem5250753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5250754 : term380 = term381.
Proof. exact (MK_COMB (@lem5250753) (@lem5250752)). Qed.
Lemma lem5250755 (x : real) : (term372 x) = (term362 x).
Proof. exact (eq_refl (term372 x)). Qed.
Lemma lem5250756 : term382 = term369.
Proof. exact (fun_ext (fun x : real => @lem5250755 x)). Qed.
Lemma lem5250757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250758 : term383 = term384.
Proof. exact (MK_COMB (@lem5250757) (@lem5250756)). Qed.
Lemma lem5250759 : term367 = term385.
Proof. exact (MK_COMB (@lem5250754) (@lem5250758)). Qed.
Lemma lem5250760 : (term366 = term367) = (term365 = term385).
Proof. exact (MK_COMB (@lem5250748) (@lem5250759)). Qed.
Lemma lem5250761 : term365 = term385.
Proof. exact (EQ_MP (@lem5250760) (@lem5250738)). Qed.
Lemma lem5250868 : term338 = term385.
Proof. exact (TRANS (@lem5250734) (@lem5250761)). Qed.
Lemma lem5250869 : term14 = term385.
Proof. exact (TRANS (@lem5250604) (@lem5250868)). Qed.
Lemma lem5250870 (h1 : term14) : term385.
Proof. exact (EQ_MP (@lem5250869) (@lem5249849 h1)). Qed.
Lemma lem5250954 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5250955 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5250954 x)). Qed.
Lemma lem5250956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250965 : term68 = term68.
Proof. exact (MK_COMB (@lem5250956) (@lem5250955)). Qed.
Lemma lem5250966 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5250965) (@lem5249851 h1)). Qed.
Lemma lem5250967 (s : real -> Prop) (a : real) (h1 : term323 s a) : term323 s a.
Proof. exact (h1). Qed.
Lemma lem5250968 (x : real) (s : real -> Prop) (a : real) (h1 : term321 x s a) : term321 x s a.
Proof. exact (h1). Qed.
Lemma lem5250969 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term318 y x s a) : term318 y x s a.
Proof. exact (h1). Qed.
Lemma lem5250994 (x : real) (y : real) : (term331 x y) = (term331 x y).
Proof. exact (eq_refl (term331 x y)). Qed.
Lemma lem5250995 (x : real) : (term346 x) = (term346 x).
Proof. exact (fun_ext (fun y : real => @lem5250994 x y)). Qed.
Lemma lem5250996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5250997 (x : real) : (term362 x) = (term362 x).
Proof. exact (MK_COMB (@lem5250996) (@lem5250995 x)). Qed.
Lemma lem5250998 : term369 = term369.
Proof. exact (fun_ext (fun x : real => @lem5250997 x)). Qed.
Lemma lem5250999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251000 : term384 = term384.
Proof. exact (MK_COMB (@lem5250999) (@lem5250998)). Qed.
Lemma lem5251023 (x : real) (y : real) : (term348 x y) = (term348 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem5251024 (x : real) : (term345 x) = (term345 x).
Proof. exact (fun_ext (fun y : real => @lem5251023 x y)). Qed.
Lemma lem5251025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251026 (x : real) : (term357 x) = (term357 x).
Proof. exact (MK_COMB (@lem5251025) (@lem5251024 x)). Qed.
Lemma lem5251027 : term368 = term368.
Proof. exact (fun_ext (fun x : real => @lem5251026 x)). Qed.
Lemma lem5251028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251029 : term379 = term379.
Proof. exact (MK_COMB (@lem5251028) (@lem5251027)). Qed.
Lemma lem5251030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5251031 : term381 = term381.
Proof. exact (MK_COMB (@lem5251030) (@lem5251029)). Qed.
Lemma lem5251032 : term385 = term385.
Proof. exact (MK_COMB (@lem5251031) (@lem5251000)). Qed.
Lemma lem5251033 (h1 : term14) : term385.
Proof. exact (EQ_MP (@lem5251032) (@lem5250870 h1)). Qed.
Lemma lem5251073 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5251074 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5251073 x)). Qed.
Lemma lem5251075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251076 : term68 = term68.
Proof. exact (MK_COMB (@lem5251075) (@lem5251074)). Qed.
Lemma lem5251077 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5251076) (@lem5250966 h1)). Qed.
Lemma lem5251092 (s : real -> Prop) (a : real) (y : real) : (term108 s a y) = (term108 s a y).
Proof. exact (eq_refl (term108 s a y)). Qed.
Lemma lem5251093 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun y : real => @lem5251092 s a y)). Qed.
Lemma lem5251094 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251095 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5251094) (@lem5251093 s a)). Qed.
Lemma lem5251102 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5251103 (s : real -> Prop) (a : real) : (term130 s a) = (term130 s a).
Proof. exact (MK_COMB (@lem5251102 a s) (@lem5251095 s a)). Qed.
Lemma lem5251118 (s : real -> Prop) (a : real) (x : real) : (term107 s a x) = (term107 s a x).
Proof. exact (eq_refl (term107 s a x)). Qed.
Lemma lem5251135 (s : real -> Prop) (x : real) (a : real) : (term96 s x a) = (term96 s x a).
Proof. exact (eq_refl (term96 s x a)). Qed.
Lemma lem5251136 (s : real -> Prop) (a : real) : (term104 s a) = (term104 s a).
Proof. exact (fun_ext (fun x : real => @lem5251135 s x a)). Qed.
Lemma lem5251137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251138 (s : real -> Prop) (a : real) : (term105 s a) = (term105 s a).
Proof. exact (MK_COMB (@lem5251137) (@lem5251136 s a)). Qed.
Lemma lem5251139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5251140 (s : real -> Prop) (a : real) : (term121 s a) = (term121 s a).
Proof. exact (MK_COMB (@lem5251139) (@lem5251138 s a)). Qed.
Lemma lem5251141 (s : real -> Prop) (a : real) (x : real) : (term232 s a x) = (term232 s a x).
Proof. exact (MK_COMB (@lem5251140 s a) (@lem5251118 s a x)). Qed.
Lemma lem5251142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5251143 (s : real -> Prop) (a : real) (x : real) : (term247 s a x) = (term247 s a x).
Proof. exact (MK_COMB (@lem5251142) (@lem5251141 s a x)). Qed.
Lemma lem5251144 (x : real) (s : real -> Prop) (a : real) : (term249 x s a) = (term249 x s a).
Proof. exact (MK_COMB (@lem5251143 s a x) (@lem5251103 s a)). Qed.
Lemma lem5251169 (s : real -> Prop) (a : real) (y : real) : (term188 s a y) = (term188 s a y).
Proof. exact (eq_refl (term188 s a y)). Qed.
Lemma lem5251184 (s : real -> Prop) (a : real) (x : real) : (term108 s a x) = (term108 s a x).
Proof. exact (eq_refl (term108 s a x)). Qed.
Lemma lem5251185 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5251184 s a x)). Qed.
Lemma lem5251186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251187 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5251186) (@lem5251185 s a)). Qed.
Lemma lem5251202 (s : real -> Prop) (x : real) (a : real) : (term168 s x a) = (term168 s x a).
Proof. exact (eq_refl (term168 s x a)). Qed.
Lemma lem5251203 (x : real) (s : real -> Prop) (a : real) : (term170 x s a) = (term170 x s a).
Proof. exact (MK_COMB (@lem5251202 s x a) (@lem5251187 s a)). Qed.
Lemma lem5251204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5251205 (x : real) (s : real -> Prop) (a : real) : (term202 x s a) = (term202 x s a).
Proof. exact (MK_COMB (@lem5251204) (@lem5251203 x s a)). Qed.
Lemma lem5251206 (x : real) (s : real -> Prop) (a : real) (y : real) : (term220 x s a y) = (term220 x s a y).
Proof. exact (MK_COMB (@lem5251205 x s a) (@lem5251169 s a y)). Qed.
Lemma lem5251207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5251208 (x : real) (s : real -> Prop) (a : real) (y : real) : (term289 x s a y) = (term289 x s a y).
Proof. exact (MK_COMB (@lem5251207) (@lem5251206 x s a y)). Qed.
Lemma lem5251209 (y : real) (x : real) (s : real -> Prop) (a : real) : (term291 y x s a) = (term291 y x s a).
Proof. exact (MK_COMB (@lem5251208 x s a y) (@lem5251144 x s a)). Qed.
Lemma lem5251224 (s : real -> Prop) : (term144 s) = (term144 s).
Proof. exact (eq_refl (term144 s)). Qed.
Lemma lem5251225 (y : real) (x : real) (s : real -> Prop) (a : real) : (term318 y x s a) = (term318 y x s a).
Proof. exact (MK_COMB (@lem5251224 s) (@lem5251209 y x s a)). Qed.
Lemma lem5251226 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term318 y x s a) : term318 y x s a.
Proof. exact (EQ_MP (@lem5251225 y x s a) (@lem5250969 y x s a h1)). Qed.
Lemma lem5251227 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term318 y x s a) : term291 y x s a.
Proof. exact (proj2 (@lem5251226 y x s a h1)). Qed.
Lemma lem5251231 (h1 : term14) : term384.
Proof. exact (proj2 (@lem5251033 h1)). Qed.
Lemma lem5251233 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term220 x s a y.
Proof. exact (h1). Qed.
Lemma lem5251234 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term249 x s a.
Proof. exact (h1). Qed.
Lemma lem5251235 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term188 s a y.
Proof. exact (proj2 (@lem5251233 x s a y h1)). Qed.
Lemma lem5251236 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term170 x s a.
Proof. exact (proj1 (@lem5251233 x s a y h1)). Qed.
Lemma lem5251237 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term119 s a.
Proof. exact (proj2 (@lem5251236 x s a y h1)). Qed.
Lemma lem5251238 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term92 s x a.
Proof. exact (proj1 (@lem5251236 x s a y h1)). Qed.
Lemma lem5251242 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : term107 s a y.
Proof. exact (h1). Qed.
Lemma lem5251245 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term130 s a.
Proof. exact (proj2 (@lem5251234 x s a h1)). Qed.
Lemma lem5251246 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term232 s a x.
Proof. exact (proj1 (@lem5251234 x s a h1)). Qed.
Lemma lem5251247 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term119 s a.
Proof. exact (proj2 (@lem5251245 x s a h1)). Qed.
Lemma lem5251249 (s : real -> Prop) (a : real) (h1 : term105 s a) : term105 s a.
Proof. exact (h1). Qed.
Lemma lem5251250 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : term107 s a x.
Proof. exact (h1). Qed.
Lemma lem5251332 (x : real) (y : real) : (term331 x y) = (term331 x y).
Proof. exact (eq_refl (term331 x y)). Qed.
Lemma lem5251333 (x : real) : (term346 x) = (term346 x).
Proof. exact (fun_ext (fun y : real => @lem5251332 x y)). Qed.
Lemma lem5251334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251335 (x : real) : (term362 x) = (term362 x).
Proof. exact (MK_COMB (@lem5251334) (@lem5251333 x)). Qed.
Lemma lem5251336 : term369 = term369.
Proof. exact (fun_ext (fun x : real => @lem5251335 x)). Qed.
Lemma lem5251337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251339 : term384 = term384.
Proof. exact (MK_COMB (@lem5251337) (@lem5251336)). Qed.
Lemma lem5251340 (h1 : term14) : term384.
Proof. exact (EQ_MP (@lem5251339) (@lem5251231 h1)). Qed.
Lemma lem5251348 (s : real -> Prop) (a : real) (x : real) : (term108 s a x) = (term108 s a x).
Proof. exact (eq_refl (term108 s a x)). Qed.
Lemma lem5251349 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5251348 s a x)). Qed.
Lemma lem5251350 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251352 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5251350) (@lem5251349 s a)). Qed.
Lemma lem5251353 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term119 s a.
Proof. exact (EQ_MP (@lem5251352 s a) (@lem5251237 x s a y h1)). Qed.
Lemma lem5251365 (a : real) (s : real -> Prop) (h1 : term181 a s) : term181 a s.
Proof. exact (h1). Qed.
Lemma lem5251461 (s : real -> Prop) (a : real) (x : real) : (term108 s a x) = (term108 s a x).
Proof. exact (eq_refl (term108 s a x)). Qed.
Lemma lem5251462 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5251461 s a x)). Qed.
Lemma lem5251463 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251465 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5251463) (@lem5251462 s a)). Qed.
Lemma lem5251466 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term119 s a.
Proof. exact (EQ_MP (@lem5251465 s a) (@lem5251237 x s a y h1)). Qed.
Lemma lem5251509 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5251510 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5251509 x)). Qed.
Lemma lem5251511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251513 : term68 = term68.
Proof. exact (MK_COMB (@lem5251511) (@lem5251510)). Qed.
Lemma lem5251514 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5251513) (@lem5251077 h1)). Qed.
Lemma lem5251595 (s : real -> Prop) (x : real) (a : real) : (term96 s x a) = (term96 s x a).
Proof. exact (eq_refl (term96 s x a)). Qed.
Lemma lem5251596 (s : real -> Prop) (a : real) : (term104 s a) = (term104 s a).
Proof. exact (fun_ext (fun x : real => @lem5251595 s x a)). Qed.
Lemma lem5251597 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251599 (s : real -> Prop) (a : real) : (term105 s a) = (term105 s a).
Proof. exact (MK_COMB (@lem5251597) (@lem5251596 s a)). Qed.
Lemma lem5251600 (s : real -> Prop) (a : real) (h1 : term105 s a) : term105 s a.
Proof. exact (EQ_MP (@lem5251599 s a) (@lem5251249 s a h1)). Qed.
Lemma lem5251700 (s : real -> Prop) (a : real) (y : real) : (term108 s a y) = (term108 s a y).
Proof. exact (eq_refl (term108 s a y)). Qed.
Lemma lem5251701 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun y : real => @lem5251700 s a y)). Qed.
Lemma lem5251702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5251704 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5251702) (@lem5251701 s a)). Qed.
Lemma lem5251705 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term119 s a.
Proof. exact (EQ_MP (@lem5251704 s a) (@lem5251247 x s a h1)). Qed.
Lemma lem5251732 (_68733 : real) (h1 : term14) : term372 _68733.
Proof. exact (@lem5251340 h1 _68733). Qed.
Lemma lem5251733 (_68733 : real) : (term372 _68733) = (term362 _68733).
Proof. exact (eq_refl (term372 _68733)). Qed.
Lemma lem5251734 (_68733 : real) (h1 : term14) : term362 _68733.
Proof. exact (EQ_MP (@lem5251733 _68733) (@lem5251732 _68733 h1)). Qed.
Lemma lem5251735 (_68733 : real) (_68734 : real) (h1 : term14) : term350 _68733 _68734.
Proof. exact (@lem5251734 _68733 h1 _68734). Qed.
Lemma lem5251736 (_68733 : real) (_68734 : real) : (term350 _68733 _68734) = (term331 _68733 _68734).
Proof. exact (eq_refl (term350 _68733 _68734)). Qed.
Lemma lem5251737 (_68733 : real) (_68734 : real) (h1 : term14) : term331 _68733 _68734.
Proof. exact (EQ_MP (@lem5251736 _68733 _68734) (@lem5251735 _68733 _68734 h1)). Qed.
Lemma lem5251738 (_68735 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term386 s a _68735.
Proof. exact (@lem5251353 x s a y h1 _68735). Qed.
Lemma lem5251739 (s : real -> Prop) (a : real) (_68735 : real) : (term386 s a _68735) = (term108 s a _68735).
Proof. exact (eq_refl (term386 s a _68735)). Qed.
Lemma lem5251765 (_68744 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term386 s a _68744.
Proof. exact (@lem5251466 x s a y h1 _68744). Qed.
Lemma lem5251766 (s : real -> Prop) (a : real) (_68744 : real) : (term386 s a _68744) = (term108 s a _68744).
Proof. exact (eq_refl (term386 s a _68744)). Qed.
Lemma lem5251777 (_68748 : real) (h1 : term68) : term387 _68748.
Proof. exact (@lem5251514 h1 _68748). Qed.
Lemma lem5251778 (_68748 : real) : (term387 _68748) = (real_le _68748 _68748).
Proof. exact (eq_refl (term387 _68748)). Qed.
Lemma lem5251795 (_68754 : real) (s : real -> Prop) (a : real) (h1 : term105 s a) : term388 s a _68754.
Proof. exact (@lem5251600 s a h1 _68754). Qed.
Lemma lem5251796 (s : real -> Prop) (_68754 : real) (a : real) : (term388 s a _68754) = (term96 s _68754 a).
Proof. exact (eq_refl (term388 s a _68754)). Qed.
Lemma lem5251822 (_68763 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term386 s a _68763.
Proof. exact (@lem5251705 x s a h1 _68763). Qed.
Lemma lem5251823 (s : real -> Prop) (a : real) (_68763 : real) : (term386 s a _68763) = (term108 s a _68763).
Proof. exact (eq_refl (term386 s a _68763)). Qed.
Lemma lem5251861 (_68733 : real) (_68734 : real) : (term331 _68733 _68734) = (term389 _68733 _68734).
Proof. exact (@lem5248534 (term390 _68733 _68734) (term390 _68734 _68733) (_68733 = _68734)). Qed.
Lemma lem5251862 (_68733 : real) (_68734 : real) (h1 : term14) : term389 _68733 _68734.
Proof. exact (EQ_MP (@lem5251861 _68733 _68734) (@lem5251737 _68733 _68734 h1)). Qed.
Lemma lem5251868 (_68735 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term108 s a _68735.
Proof. exact (EQ_MP (@lem5251739 s a _68735) (@lem5251738 _68735 x s a y h1)). Qed.
Lemma lem5251874 (a : real) (s : real -> Prop) (h1 : term181 a s) : term181 a s.
Proof. exact (h1). Qed.
Lemma lem5251922 (_68744 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term108 s a _68744.
Proof. exact (EQ_MP (@lem5251766 s a _68744) (@lem5251765 _68744 x s a y h1)). Qed.
Lemma lem5251930 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : term390 a y.
Proof. exact (proj2 (@lem5251242 s a y h1)). Qed.
Lemma lem5251986 (_68754 : real) (s : real -> Prop) (a : real) (h1 : term105 s a) : term96 s _68754 a.
Proof. exact (EQ_MP (@lem5251796 s _68754 a) (@lem5251795 _68754 s a h1)). Qed.
Lemma lem5252036 (_68763 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term108 s a _68763.
Proof. exact (EQ_MP (@lem5251823 s a _68763) (@lem5251822 _68763 x s a h1)). Qed.
Lemma lem5252040 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : term390 a x.
Proof. exact (proj2 (@lem5251250 s a x h1)). Qed.
Lemma lem5252053 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5252054 (_68764 : real) (_68766 : real) (h1 : _68764 = _68766) : _68764 = _68766.
Proof. exact (h1). Qed.
Lemma lem5252055 (_68765 : real -> Prop) (_68767 : real -> Prop) (h1 : _68765 = _68767) : _68765 = _68767.
Proof. exact (h1). Qed.
Lemma lem5252056 (_68764 : real) (_68766 : real) (h1 : _68764 = _68766) : (@IN real _68764) = (@IN real _68766).
Proof. exact (MK_COMB (@lem5252053) (@lem5252054 _68764 _68766 h1)). Qed.
Lemma lem5252057 (_68765 : real -> Prop) (_68767 : real -> Prop) (_68764 : real) (_68766 : real) (h1 : _68765 = _68767) (h2 : _68764 = _68766) : (@IN real _68764 _68765) = (@IN real _68766 _68767).
Proof. exact (MK_COMB (@lem5252056 _68764 _68766 h2) (@lem5252055 _68765 _68767 h1)). Qed.
Lemma lem5252059 (b : Prop) (a : Prop) : term391 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5252060 (_68766 : real) (_68767 : real -> Prop) (_68764 : real) (_68765 : real -> Prop) : term392 _68766 _68767 _68764 _68765.
Proof. exact (@lem5252059 (@IN real _68766 _68767) (@IN real _68764 _68765)). Qed.
Lemma lem5252061 (_68765 : real -> Prop) (_68767 : real -> Prop) (_68764 : real) (_68766 : real) (h1 : _68765 = _68767) (h2 : _68764 = _68766) : term393 _68766 _68767 _68764 _68765.
Proof. exact (@lem5252060 _68766 _68767 _68764 _68765 (@lem5252057 _68765 _68767 _68764 _68766 h1 h2)). Qed.
Lemma lem5252062 (_68766 : real) (_68764 : real) (_68765 : real -> Prop) (_68767 : real -> Prop) (h1 : _68765 = _68767) : term394 _68766 _68767 _68764 _68765.
Proof. exact (fun h0 : _68764 = _68766 => @lem5252061 _68765 _68767 _68764 _68766 h1 h0). Qed.
Lemma lem5252064 (a : Prop) (b : Prop) : (a -> b) = (term395 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5252065 (_68766 : real) (_68767 : real -> Prop) (_68764 : real) (_68765 : real -> Prop) : (term394 _68766 _68767 _68764 _68765) = (term396 _68766 _68767 _68764 _68765).
Proof. exact (@lem5252064 (_68764 = _68766) (term393 _68766 _68767 _68764 _68765)). Qed.
Lemma lem5252066 (_68766 : real) (_68764 : real) (_68765 : real -> Prop) (_68767 : real -> Prop) (h1 : _68765 = _68767) : term396 _68766 _68767 _68764 _68765.
Proof. exact (EQ_MP (@lem5252065 _68766 _68767 _68764 _68765) (@lem5252062 _68766 _68764 _68765 _68767 h1)). Qed.
Lemma lem5252067 (_68766 : real) (_68767 : real -> Prop) (_68764 : real) (_68765 : real -> Prop) : term397 _68766 _68767 _68764 _68765.
Proof. exact (fun h0 : _68765 = _68767 => @lem5252066 _68766 _68764 _68765 _68767 h0). Qed.
Lemma lem5252069 (a : Prop) (b : Prop) : (a -> b) = (term395 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5252070 (_68766 : real) (_68767 : real -> Prop) (_68764 : real) (_68765 : real -> Prop) : (term397 _68766 _68767 _68764 _68765) = (term398 _68766 _68767 _68764 _68765).
Proof. exact (@lem5252069 (_68765 = _68767) (term396 _68766 _68767 _68764 _68765)). Qed.
Lemma lem5252071 (_68766 : real) (_68767 : real -> Prop) (_68764 : real) (_68765 : real -> Prop) : term398 _68766 _68767 _68764 _68765.
Proof. exact (EQ_MP (@lem5252070 _68766 _68767 _68764 _68765) (@lem5252067 _68766 _68767 _68764 _68765)). Qed.
Lemma lem5252108 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5252109 (s : real -> Prop) : s = s.
Proof. exact (@lem5252108 s). Qed.
Lemma lem5252110 (s : real -> Prop) : term399 s.
Proof. exact (fun h0 : term400 s => @lem5252109 s). Qed.
Lemma lem5252112 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252113 (s : real -> Prop) : (term399 s) = (s = s).
Proof. exact (@lem5252112 (s = s)). Qed.
Lemma lem5252114 (s : real -> Prop) : s = s.
Proof. exact (EQ_MP (@lem5252113 s) (@lem5252110 s)). Qed.
Lemma lem5252116 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : real_le x a.
Proof. exact (proj2 (@lem5251238 x s a y h1)). Qed.
Lemma lem5252117 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term402 x a.
Proof. exact (fun h0 : term390 x a => @lem5252116 x s a y h1). Qed.
Lemma lem5252119 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252120 (x : real) (a : real) : (term402 x a) = (real_le x a).
Proof. exact (@lem5252119 (real_le x a)). Qed.
Lemma lem5252121 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : real_le x a.
Proof. exact (EQ_MP (@lem5252120 x a) (@lem5252117 x s a y h1)). Qed.
Lemma lem5252123 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : @IN real x s.
Proof. exact (proj1 (@lem5251238 x s a y h1)). Qed.
Lemma lem5252124 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term403 x s.
Proof. exact (fun h0 : term181 x s => @lem5252123 x s a y h1). Qed.
Lemma lem5252126 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252127 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5252126 (@IN real x s)). Qed.
Lemma lem5252128 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : @IN real x s.
Proof. exact (EQ_MP (@lem5252127 x s) (@lem5252124 x s a y h1)). Qed.
Lemma lem5252134 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5252135 (a : real) (_68735 : real) (s : real -> Prop) : (term108 s a _68735) = (term404 a _68735 s).
Proof. exact (@lem5252134 (real_le a _68735) (term181 _68735 s)). Qed.
Lemma lem5252141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252142 (a : real) (_68735 : real) (s : real -> Prop) : (term405 s a _68735) = (term406 a _68735 s).
Proof. exact (MK_COMB (@lem5252141) (@lem5252135 a _68735 s)). Qed.
Lemma lem5252148 (a : real) (_68735 : real) (s : real -> Prop) : (term404 a _68735 s) = (term404 a _68735 s).
Proof. exact (eq_refl (term404 a _68735 s)). Qed.
Lemma lem5252149 (a : real) (_68735 : real) (s : real -> Prop) : ((term108 s a _68735) = (term404 a _68735 s)) = ((term404 a _68735 s) = (term404 a _68735 s)).
Proof. exact (MK_COMB (@lem5252142 a _68735 s) (@lem5252148 a _68735 s)). Qed.
Lemma lem5252151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5252152 (x : Prop) : (x = x) = True.
Proof. exact (@lem5252151 Prop x). Qed.
Lemma lem5252153 (a : real) (_68735 : real) (s : real -> Prop) : ((term404 a _68735 s) = (term404 a _68735 s)) = True.
Proof. exact (@lem5252152 (term404 a _68735 s)). Qed.
Lemma lem5252154 (a : real) (_68735 : real) (s : real -> Prop) : ((term108 s a _68735) = (term404 a _68735 s)) = True.
Proof. exact (TRANS (@lem5252149 a _68735 s) (@lem5252153 a _68735 s)). Qed.
Lemma lem5252155 (a : real) (_68735 : real) (s : real -> Prop) : True = ((term108 s a _68735) = (term404 a _68735 s)).
Proof. exact (SYM (@lem5252154 a _68735 s)). Qed.
Lemma lem5252156 (a : real) (_68735 : real) (s : real -> Prop) : (term108 s a _68735) = (term404 a _68735 s).
Proof. exact (EQ_MP (@lem5252155 a _68735 s) (@lem0)). Qed.
Lemma lem5252157 (_68735 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term404 a _68735 s.
Proof. exact (EQ_MP (@lem5252156 a _68735 s) (@lem5251868 _68735 x s a y h1)). Qed.
Lemma lem5252159 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5252160 (s : real -> Prop) (a : real) (_68735 : real) : (term404 a _68735 s) = (term408 s a _68735).
Proof. exact (@lem5252159 (term181 _68735 s) (real_le a _68735)). Qed.
Lemma lem5252162 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252163 (_68735 : real) (s : real -> Prop) : (term410 _68735 s) = (@IN real _68735 s).
Proof. exact (@lem5252162 (@IN real _68735 s)). Qed.
Lemma lem5252164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5252165 (_68735 : real) (s : real -> Prop) : (term411 _68735 s) = (term412 _68735 s).
Proof. exact (MK_COMB (@lem5252164) (@lem5252163 _68735 s)). Qed.
Lemma lem5252166 (a : real) (_68735 : real) : (real_le a _68735) = (real_le a _68735).
Proof. exact (eq_refl (real_le a _68735)). Qed.
Lemma lem5252167 (s : real -> Prop) (a : real) (_68735 : real) : (term408 s a _68735) = (term89 s a _68735).
Proof. exact (MK_COMB (@lem5252165 _68735 s) (@lem5252166 a _68735)). Qed.
Lemma lem5252168 (s : real -> Prop) (a : real) (_68735 : real) : (term404 a _68735 s) = (term89 s a _68735).
Proof. exact (TRANS (@lem5252160 s a _68735) (@lem5252167 s a _68735)). Qed.
Lemma lem5252171 (_68735 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term89 s a _68735.
Proof. exact (EQ_MP (@lem5252168 s a _68735) (@lem5252157 _68735 x s a y h1)). Qed.
Lemma lem5252172 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term89 s a x.
Proof. exact (@lem5252171 x x s a y h1). Qed.
Lemma lem5252175 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : real_le a x.
Proof. exact (@lem5252172 x s a y h1 (@lem5252128 x s a y h1)). Qed.
Lemma lem5252176 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term402 a x.
Proof. exact (fun h0 : term390 a x => @lem5252175 x s a y h1). Qed.
Lemma lem5252178 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252179 (a : real) (x : real) : (term402 a x) = (real_le a x).
Proof. exact (@lem5252178 (real_le a x)). Qed.
Lemma lem5252180 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : real_le a x.
Proof. exact (EQ_MP (@lem5252179 a x) (@lem5252176 x s a y h1)). Qed.
Lemma lem5252196 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5252197 (_68734 : real) (_68733 : real) : (term413 _68733 _68734) = (term414 _68734 _68733).
Proof. exact (@lem5252196 (_68733 = _68734) (term390 _68734 _68733)). Qed.
Lemma lem5252205 (_68733 : real) (_68734 : real) : (term415 _68733 _68734) = (term415 _68733 _68734).
Proof. exact (eq_refl (term415 _68733 _68734)). Qed.
Lemma lem5252206 (_68734 : real) (_68733 : real) : (term389 _68733 _68734) = (term416 _68734 _68733).
Proof. exact (MK_COMB (@lem5252205 _68733 _68734) (@lem5252197 _68734 _68733)). Qed.
Lemma lem5252210 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5252211 (_68734 : real) (_68733 : real) : (term416 _68734 _68733) = (term417 _68734 _68733).
Proof. exact (@lem5252210 (_68733 = _68734) (term390 _68733 _68734) (term390 _68734 _68733)). Qed.
Lemma lem5252229 (_68734 : real) (_68733 : real) : (term389 _68733 _68734) = (term417 _68734 _68733).
Proof. exact (TRANS (@lem5252206 _68734 _68733) (@lem5252211 _68734 _68733)). Qed.
Lemma lem5252230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252231 (_68734 : real) (_68733 : real) : (term418 _68733 _68734) = (term419 _68734 _68733).
Proof. exact (MK_COMB (@lem5252230) (@lem5252229 _68734 _68733)). Qed.
Lemma lem5252249 (_68734 : real) (_68733 : real) : (term417 _68734 _68733) = (term417 _68734 _68733).
Proof. exact (eq_refl (term417 _68734 _68733)). Qed.
Lemma lem5252250 (_68734 : real) (_68733 : real) : ((term389 _68733 _68734) = (term417 _68734 _68733)) = ((term417 _68734 _68733) = (term417 _68734 _68733)).
Proof. exact (MK_COMB (@lem5252231 _68734 _68733) (@lem5252249 _68734 _68733)). Qed.
Lemma lem5252252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5252253 (x : Prop) : (x = x) = True.
Proof. exact (@lem5252252 Prop x). Qed.
Lemma lem5252254 (_68734 : real) (_68733 : real) : ((term417 _68734 _68733) = (term417 _68734 _68733)) = True.
Proof. exact (@lem5252253 (term417 _68734 _68733)). Qed.
Lemma lem5252255 (_68734 : real) (_68733 : real) : ((term389 _68733 _68734) = (term417 _68734 _68733)) = True.
Proof. exact (TRANS (@lem5252250 _68734 _68733) (@lem5252254 _68734 _68733)). Qed.
Lemma lem5252256 (_68734 : real) (_68733 : real) : True = ((term389 _68733 _68734) = (term417 _68734 _68733)).
Proof. exact (SYM (@lem5252255 _68734 _68733)). Qed.
Lemma lem5252257 (_68734 : real) (_68733 : real) : (term389 _68733 _68734) = (term417 _68734 _68733).
Proof. exact (EQ_MP (@lem5252256 _68734 _68733) (@lem0)). Qed.
Lemma lem5252258 (_68734 : real) (_68733 : real) (h1 : term14) : term417 _68734 _68733.
Proof. exact (EQ_MP (@lem5252257 _68734 _68733) (@lem5251862 _68733 _68734 h1)). Qed.
Lemma lem5252260 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5252261 (_68733 : real) (_68734 : real) : (term417 _68734 _68733) = (term420 _68733 _68734).
Proof. exact (@lem5252260 (term327 _68734 _68733) (_68733 = _68734)). Qed.
Lemma lem5252263 (a : Prop) (b : Prop) : (term421 a b) = (term422 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5252264 (_68734 : real) (_68733 : real) : (term423 _68734 _68733) = (term424 _68734 _68733).
Proof. exact (@lem5252263 (term390 _68733 _68734) (term390 _68734 _68733)). Qed.
Lemma lem5252266 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252267 (_68733 : real) (_68734 : real) : (term425 _68733 _68734) = (real_le _68733 _68734).
Proof. exact (@lem5252266 (real_le _68733 _68734)). Qed.
Lemma lem5252268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5252269 (_68733 : real) (_68734 : real) : (term426 _68733 _68734) = (term427 _68733 _68734).
Proof. exact (MK_COMB (@lem5252268) (@lem5252267 _68733 _68734)). Qed.
Lemma lem5252271 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252272 (_68734 : real) (_68733 : real) : (term425 _68734 _68733) = (real_le _68734 _68733).
Proof. exact (@lem5252271 (real_le _68734 _68733)). Qed.
Lemma lem5252273 (_68734 : real) (_68733 : real) : (term424 _68734 _68733) = (term7 _68734 _68733).
Proof. exact (MK_COMB (@lem5252269 _68733 _68734) (@lem5252272 _68734 _68733)). Qed.
Lemma lem5252274 (_68734 : real) (_68733 : real) : (term423 _68734 _68733) = (term7 _68734 _68733).
Proof. exact (TRANS (@lem5252264 _68734 _68733) (@lem5252273 _68734 _68733)). Qed.
Lemma lem5252275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5252276 (_68734 : real) (_68733 : real) : (term428 _68734 _68733) = (term429 _68734 _68733).
Proof. exact (MK_COMB (@lem5252275) (@lem5252274 _68734 _68733)). Qed.
Lemma lem5252277 (_68733 : real) (_68734 : real) : (_68733 = _68734) = (_68733 = _68734).
Proof. exact (eq_refl (_68733 = _68734)). Qed.
Lemma lem5252278 (_68733 : real) (_68734 : real) : (term420 _68733 _68734) = (term430 _68733 _68734).
Proof. exact (MK_COMB (@lem5252276 _68734 _68733) (@lem5252277 _68733 _68734)). Qed.
Lemma lem5252279 (_68733 : real) (_68734 : real) : (term417 _68734 _68733) = (term430 _68733 _68734).
Proof. exact (TRANS (@lem5252261 _68733 _68734) (@lem5252278 _68733 _68734)). Qed.
Lemma lem5252281 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term7 a x.
Proof. exact (conj (@lem5252121 x s a y h1) (@lem5252180 x s a y h1)). Qed.
Lemma lem5252283 (_68733 : real) (_68734 : real) (h1 : term14) : term430 _68733 _68734.
Proof. exact (EQ_MP (@lem5252279 _68733 _68734) (@lem5252258 _68734 _68733 h1)). Qed.
Lemma lem5252284 (x : real) (a : real) (h1 : term14) : term430 x a.
Proof. exact (@lem5252283 x a h1). Qed.
Lemma lem5252287 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : x = a.
Proof. exact (@lem5252284 x a h1 (@lem5252281 x s a y h2)). Qed.
Lemma lem5252288 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : term431 x a.
Proof. exact (fun h0 : term432 x a => @lem5252287 x s a y h1 h2). Qed.
Lemma lem5252290 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252291 (x : real) (a : real) : (term431 x a) = (x = a).
Proof. exact (@lem5252290 (x = a)). Qed.
Lemma lem5252292 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : x = a.
Proof. exact (EQ_MP (@lem5252291 x a) (@lem5252288 x s a y h1 h2)). Qed.
Lemma lem5252294 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : @IN real x s.
Proof. exact (proj1 (@lem5251238 x s a y h1)). Qed.
Lemma lem5252295 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term403 x s.
Proof. exact (fun h0 : term181 x s => @lem5252294 x s a y h1). Qed.
Lemma lem5252297 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252298 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5252297 (@IN real x s)). Qed.
Lemma lem5252299 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : @IN real x s.
Proof. exact (EQ_MP (@lem5252298 x s) (@lem5252295 x s a y h1)). Qed.
Lemma lem5252317 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5252318 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term396 _68766 _68767 _68764 _68765) = (term433 _68767 _68766 _68764 _68765).
Proof. exact (@lem5252317 (@IN real _68766 _68767) (term432 _68764 _68766) (term181 _68764 _68765)). Qed.
Lemma lem5252336 (_68765 : real -> Prop) (_68767 : real -> Prop) : (term434 _68765 _68767) = (term434 _68765 _68767).
Proof. exact (eq_refl (term434 _68765 _68767)). Qed.
Lemma lem5252337 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term398 _68766 _68767 _68764 _68765) = (term435 _68767 _68766 _68764 _68765).
Proof. exact (MK_COMB (@lem5252336 _68765 _68767) (@lem5252318 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252341 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5252342 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term435 _68767 _68766 _68764 _68765) = (term436 _68767 _68766 _68764 _68765).
Proof. exact (@lem5252341 (@IN real _68766 _68767) (term437 _68765 _68767) (term438 _68766 _68764 _68765)). Qed.
Lemma lem5252372 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term398 _68766 _68767 _68764 _68765) = (term436 _68767 _68766 _68764 _68765).
Proof. exact (TRANS (@lem5252337 _68767 _68766 _68764 _68765) (@lem5252342 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252374 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term439 _68766 _68767 _68764 _68765) = (term440 _68767 _68766 _68764 _68765).
Proof. exact (MK_COMB (@lem5252373) (@lem5252372 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252404 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term436 _68767 _68766 _68764 _68765) = (term436 _68767 _68766 _68764 _68765).
Proof. exact (eq_refl (term436 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252405 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : ((term398 _68766 _68767 _68764 _68765) = (term436 _68767 _68766 _68764 _68765)) = ((term436 _68767 _68766 _68764 _68765) = (term436 _68767 _68766 _68764 _68765)).
Proof. exact (MK_COMB (@lem5252374 _68767 _68766 _68764 _68765) (@lem5252404 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5252408 (x : Prop) : (x = x) = True.
Proof. exact (@lem5252407 Prop x). Qed.
Lemma lem5252409 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : ((term436 _68767 _68766 _68764 _68765) = (term436 _68767 _68766 _68764 _68765)) = True.
Proof. exact (@lem5252408 (term436 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252410 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : ((term398 _68766 _68767 _68764 _68765) = (term436 _68767 _68766 _68764 _68765)) = True.
Proof. exact (TRANS (@lem5252405 _68767 _68766 _68764 _68765) (@lem5252409 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252411 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : True = ((term398 _68766 _68767 _68764 _68765) = (term436 _68767 _68766 _68764 _68765)).
Proof. exact (SYM (@lem5252410 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252412 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term398 _68766 _68767 _68764 _68765) = (term436 _68767 _68766 _68764 _68765).
Proof. exact (EQ_MP (@lem5252411 _68767 _68766 _68764 _68765) (@lem0)). Qed.
Lemma lem5252413 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : term436 _68767 _68766 _68764 _68765.
Proof. exact (EQ_MP (@lem5252412 _68767 _68766 _68764 _68765) (@lem5252071 _68766 _68767 _68764 _68765)). Qed.
Lemma lem5252415 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5252416 (_68764 : real) (_68765 : real -> Prop) (_68766 : real) (_68767 : real -> Prop) : (term436 _68767 _68766 _68764 _68765) = (term441 _68764 _68765 _68766 _68767).
Proof. exact (@lem5252415 (term442 _68767 _68766 _68764 _68765) (@IN real _68766 _68767)). Qed.
Lemma lem5252418 (a : Prop) (b : Prop) : (term421 a b) = (term422 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5252419 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term443 _68767 _68766 _68764 _68765) = (term444 _68767 _68766 _68764 _68765).
Proof. exact (@lem5252418 (term437 _68765 _68767) (term438 _68766 _68764 _68765)). Qed.
Lemma lem5252421 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252422 (_68765 : real -> Prop) (_68767 : real -> Prop) : (term445 _68765 _68767) = (_68765 = _68767).
Proof. exact (@lem5252421 (_68765 = _68767)). Qed.
Lemma lem5252423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5252424 (_68765 : real -> Prop) (_68767 : real -> Prop) : (term446 _68765 _68767) = (term447 _68765 _68767).
Proof. exact (MK_COMB (@lem5252423) (@lem5252422 _68765 _68767)). Qed.
Lemma lem5252426 (a : Prop) (b : Prop) : (term421 a b) = (term422 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5252427 (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term448 _68766 _68764 _68765) = (term449 _68766 _68764 _68765).
Proof. exact (@lem5252426 (term432 _68764 _68766) (term181 _68764 _68765)). Qed.
Lemma lem5252429 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252430 (_68764 : real) (_68766 : real) : (term450 _68764 _68766) = (_68764 = _68766).
Proof. exact (@lem5252429 (_68764 = _68766)). Qed.
Lemma lem5252431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5252432 (_68764 : real) (_68766 : real) : (term451 _68764 _68766) = (term452 _68764 _68766).
Proof. exact (MK_COMB (@lem5252431) (@lem5252430 _68764 _68766)). Qed.
Lemma lem5252434 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252435 (_68764 : real) (_68765 : real -> Prop) : (term410 _68764 _68765) = (@IN real _68764 _68765).
Proof. exact (@lem5252434 (@IN real _68764 _68765)). Qed.
Lemma lem5252436 (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term449 _68766 _68764 _68765) = (term453 _68766 _68764 _68765).
Proof. exact (MK_COMB (@lem5252432 _68764 _68766) (@lem5252435 _68764 _68765)). Qed.
Lemma lem5252437 (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term448 _68766 _68764 _68765) = (term453 _68766 _68764 _68765).
Proof. exact (TRANS (@lem5252427 _68766 _68764 _68765) (@lem5252436 _68766 _68764 _68765)). Qed.
Lemma lem5252438 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term444 _68767 _68766 _68764 _68765) = (term454 _68767 _68766 _68764 _68765).
Proof. exact (MK_COMB (@lem5252424 _68765 _68767) (@lem5252437 _68766 _68764 _68765)). Qed.
Lemma lem5252439 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term443 _68767 _68766 _68764 _68765) = (term454 _68767 _68766 _68764 _68765).
Proof. exact (TRANS (@lem5252419 _68767 _68766 _68764 _68765) (@lem5252438 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5252441 (_68767 : real -> Prop) (_68766 : real) (_68764 : real) (_68765 : real -> Prop) : (term455 _68767 _68766 _68764 _68765) = (term456 _68767 _68766 _68764 _68765).
Proof. exact (MK_COMB (@lem5252440) (@lem5252439 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252442 (_68766 : real) (_68767 : real -> Prop) : (@IN real _68766 _68767) = (@IN real _68766 _68767).
Proof. exact (eq_refl (@IN real _68766 _68767)). Qed.
Lemma lem5252443 (_68764 : real) (_68765 : real -> Prop) (_68766 : real) (_68767 : real -> Prop) : (term441 _68764 _68765 _68766 _68767) = (term457 _68764 _68765 _68766 _68767).
Proof. exact (MK_COMB (@lem5252441 _68767 _68766 _68764 _68765) (@lem5252442 _68766 _68767)). Qed.
Lemma lem5252444 (_68764 : real) (_68765 : real -> Prop) (_68766 : real) (_68767 : real -> Prop) : (term436 _68767 _68766 _68764 _68765) = (term457 _68764 _68765 _68766 _68767).
Proof. exact (TRANS (@lem5252416 _68764 _68765 _68766 _68767) (@lem5252443 _68764 _68765 _68766 _68767)). Qed.
Lemma lem5252446 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : term453 a x s.
Proof. exact (conj (@lem5252292 x s a y h1 h2) (@lem5252299 x s a y h2)). Qed.
Lemma lem5252447 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : term458 a x s.
Proof. exact (conj (@lem5252114 s) (@lem5252446 x s a y h1 h2)). Qed.
Lemma lem5252449 (_68764 : real) (_68765 : real -> Prop) (_68766 : real) (_68767 : real -> Prop) : term457 _68764 _68765 _68766 _68767.
Proof. exact (EQ_MP (@lem5252444 _68764 _68765 _68766 _68767) (@lem5252413 _68767 _68766 _68764 _68765)). Qed.
Lemma lem5252450 (x : real) (a : real) (s : real -> Prop) : term459 x a s.
Proof. exact (@lem5252449 x s a s). Qed.
Lemma lem5252453 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : @IN real a s.
Proof. exact (@lem5252450 x a s (@lem5252447 x s a y h1 h2)). Qed.
Lemma lem5252454 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : term403 a s.
Proof. exact (fun h0 : term181 a s => @lem5252453 x s a y h1 h2). Qed.
Lemma lem5252456 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252457 (a : real) (s : real -> Prop) : (term403 a s) = (@IN real a s).
Proof. exact (@lem5252456 (@IN real a s)). Qed.
Lemma lem5252458 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : @IN real a s.
Proof. exact (EQ_MP (@lem5252457 a s) (@lem5252454 x s a y h1 h2)). Qed.
Lemma lem5252461 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5252463 (a : real) (s : real -> Prop) : (term181 a s) = (term460 a s).
Proof. exact (@lem5252461 (@IN real a s)). Qed.
Lemma lem5252466 (a : real) (s : real -> Prop) (h1 : term181 a s) : term460 a s.
Proof. exact (EQ_MP (@lem5252463 a s) (@lem5251874 a s h1)). Qed.
Lemma lem5252469 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : False.
Proof. exact (@lem5252466 a s h2 (@lem5252458 x s a y h1 h3)). Qed.
Lemma lem5252470 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : term461.
Proof. exact (fun h0 : ~ False => @lem5252469 x s a y h1 h2 h3). Qed.
Lemma lem5252472 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252473 : term461 = False.
Proof. exact (@lem5252472 False). Qed.
Lemma lem5252474 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : False.
Proof. exact (EQ_MP (@lem5252473) (@lem5252470 x s a y h1 h2 h3)). Qed.
Lemma lem5252530 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : @IN real y s.
Proof. exact (proj1 (@lem5251242 s a y h1)). Qed.
Lemma lem5252531 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : term403 y s.
Proof. exact (fun h0 : term181 y s => @lem5252530 s a y h1). Qed.
Lemma lem5252533 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252534 (y : real) (s : real -> Prop) : (term403 y s) = (@IN real y s).
Proof. exact (@lem5252533 (@IN real y s)). Qed.
Lemma lem5252535 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : @IN real y s.
Proof. exact (EQ_MP (@lem5252534 y s) (@lem5252531 s a y h1)). Qed.
Lemma lem5252541 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5252542 (a : real) (_68744 : real) (s : real -> Prop) : (term108 s a _68744) = (term404 a _68744 s).
Proof. exact (@lem5252541 (real_le a _68744) (term181 _68744 s)). Qed.
Lemma lem5252548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252549 (a : real) (_68744 : real) (s : real -> Prop) : (term405 s a _68744) = (term406 a _68744 s).
Proof. exact (MK_COMB (@lem5252548) (@lem5252542 a _68744 s)). Qed.
Lemma lem5252555 (a : real) (_68744 : real) (s : real -> Prop) : (term404 a _68744 s) = (term404 a _68744 s).
Proof. exact (eq_refl (term404 a _68744 s)). Qed.
Lemma lem5252556 (a : real) (_68744 : real) (s : real -> Prop) : ((term108 s a _68744) = (term404 a _68744 s)) = ((term404 a _68744 s) = (term404 a _68744 s)).
Proof. exact (MK_COMB (@lem5252549 a _68744 s) (@lem5252555 a _68744 s)). Qed.
Lemma lem5252558 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5252559 (x : Prop) : (x = x) = True.
Proof. exact (@lem5252558 Prop x). Qed.
Lemma lem5252560 (a : real) (_68744 : real) (s : real -> Prop) : ((term404 a _68744 s) = (term404 a _68744 s)) = True.
Proof. exact (@lem5252559 (term404 a _68744 s)). Qed.
Lemma lem5252561 (a : real) (_68744 : real) (s : real -> Prop) : ((term108 s a _68744) = (term404 a _68744 s)) = True.
Proof. exact (TRANS (@lem5252556 a _68744 s) (@lem5252560 a _68744 s)). Qed.
Lemma lem5252562 (a : real) (_68744 : real) (s : real -> Prop) : True = ((term108 s a _68744) = (term404 a _68744 s)).
Proof. exact (SYM (@lem5252561 a _68744 s)). Qed.
Lemma lem5252563 (a : real) (_68744 : real) (s : real -> Prop) : (term108 s a _68744) = (term404 a _68744 s).
Proof. exact (EQ_MP (@lem5252562 a _68744 s) (@lem0)). Qed.
Lemma lem5252564 (_68744 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term404 a _68744 s.
Proof. exact (EQ_MP (@lem5252563 a _68744 s) (@lem5251922 _68744 x s a y h1)). Qed.
Lemma lem5252566 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5252567 (s : real -> Prop) (a : real) (_68744 : real) : (term404 a _68744 s) = (term408 s a _68744).
Proof. exact (@lem5252566 (term181 _68744 s) (real_le a _68744)). Qed.
Lemma lem5252569 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252570 (_68744 : real) (s : real -> Prop) : (term410 _68744 s) = (@IN real _68744 s).
Proof. exact (@lem5252569 (@IN real _68744 s)). Qed.
Lemma lem5252571 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5252572 (_68744 : real) (s : real -> Prop) : (term411 _68744 s) = (term412 _68744 s).
Proof. exact (MK_COMB (@lem5252571) (@lem5252570 _68744 s)). Qed.
Lemma lem5252573 (a : real) (_68744 : real) : (real_le a _68744) = (real_le a _68744).
Proof. exact (eq_refl (real_le a _68744)). Qed.
Lemma lem5252574 (s : real -> Prop) (a : real) (_68744 : real) : (term408 s a _68744) = (term89 s a _68744).
Proof. exact (MK_COMB (@lem5252572 _68744 s) (@lem5252573 a _68744)). Qed.
Lemma lem5252575 (s : real -> Prop) (a : real) (_68744 : real) : (term404 a _68744 s) = (term89 s a _68744).
Proof. exact (TRANS (@lem5252567 s a _68744) (@lem5252574 s a _68744)). Qed.
Lemma lem5252578 (_68744 : real) (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term89 s a _68744.
Proof. exact (EQ_MP (@lem5252575 s a _68744) (@lem5252564 _68744 x s a y h1)). Qed.
Lemma lem5252579 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) : term89 s a y.
Proof. exact (@lem5252578 y x s a y h1). Qed.
Lemma lem5252582 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : real_le a y.
Proof. exact (@lem5252579 x s a y h1 (@lem5252535 s a y h2)). Qed.
Lemma lem5252583 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : term402 a y.
Proof. exact (fun h0 : term390 a y => @lem5252582 x s a y h1 h2). Qed.
Lemma lem5252585 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252586 (a : real) (y : real) : (term402 a y) = (real_le a y).
Proof. exact (@lem5252585 (real_le a y)). Qed.
Lemma lem5252587 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : real_le a y.
Proof. exact (EQ_MP (@lem5252586 a y) (@lem5252583 x s a y h1 h2)). Qed.
Lemma lem5252590 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5252592 (a : real) (y : real) : (term390 a y) = (term462 a y).
Proof. exact (@lem5252590 (real_le a y)). Qed.
Lemma lem5252595 (s : real -> Prop) (a : real) (y : real) (h1 : term107 s a y) : term462 a y.
Proof. exact (EQ_MP (@lem5252592 a y) (@lem5251930 s a y h1)). Qed.
Lemma lem5252598 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : False.
Proof. exact (@lem5252595 s a y h2 (@lem5252587 x s a y h1 h2)). Qed.
Lemma lem5252599 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : term461.
Proof. exact (fun h0 : ~ False => @lem5252598 x s a y h1 h2). Qed.
Lemma lem5252601 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252602 : term461 = False.
Proof. exact (@lem5252601 False). Qed.
Lemma lem5252603 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term220 x s a y) (h2 : term107 s a y) : False.
Proof. exact (EQ_MP (@lem5252602) (@lem5252599 x s a y h1 h2)). Qed.
Lemma lem5252659 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : @IN real a s.
Proof. exact (proj1 (@lem5251245 x s a h1)). Qed.
Lemma lem5252660 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term403 a s.
Proof. exact (fun h0 : term181 a s => @lem5252659 x s a h1). Qed.
Lemma lem5252662 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252663 (a : real) (s : real -> Prop) : (term403 a s) = (@IN real a s).
Proof. exact (@lem5252662 (@IN real a s)). Qed.
Lemma lem5252664 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : @IN real a s.
Proof. exact (EQ_MP (@lem5252663 a s) (@lem5252660 x s a h1)). Qed.
Lemma lem5252666 (_68748 : real) (h1 : term68) : real_le _68748 _68748.
Proof. exact (EQ_MP (@lem5251778 _68748) (@lem5251777 _68748 h1)). Qed.
Lemma lem5252667 (a : real) (h1 : term68) : real_le a a.
Proof. exact (@lem5252666 a h1). Qed.
Lemma lem5252668 (a : real) (h1 : term68) : term463 a.
Proof. exact (fun h0 : term464 a => @lem5252667 a h1). Qed.
Lemma lem5252670 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252671 (a : real) : (term463 a) = (real_le a a).
Proof. exact (@lem5252670 (real_le a a)). Qed.
Lemma lem5252672 (a : real) (h1 : term68) : real_le a a.
Proof. exact (EQ_MP (@lem5252671 a) (@lem5252668 a h1)). Qed.
Lemma lem5252674 (a : Prop) (b : Prop) : (term465 a b) = (term466 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5252675 (s : real -> Prop) (_68754 : real) (a : real) : (term96 s _68754 a) = (term95 s _68754 a).
Proof. exact (@lem5252674 (@IN real _68754 s) (real_le _68754 a)). Qed.
Lemma lem5252677 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5252678 (s : real -> Prop) (_68754 : real) (a : real) : (term95 s _68754 a) = (term467 s _68754 a).
Proof. exact (@lem5252677 (term92 s _68754 a)). Qed.
Lemma lem5252679 (s : real -> Prop) (_68754 : real) (a : real) : (term96 s _68754 a) = (term467 s _68754 a).
Proof. exact (TRANS (@lem5252675 s _68754 a) (@lem5252678 s _68754 a)). Qed.
Lemma lem5252681 (x : real) (s : real -> Prop) (a : real) (h1 : term68) (h2 : term249 x s a) : term468 s a.
Proof. exact (conj (@lem5252664 x s a h2) (@lem5252672 a h1)). Qed.
Lemma lem5252683 (_68754 : real) (s : real -> Prop) (a : real) (h1 : term105 s a) : term467 s _68754 a.
Proof. exact (EQ_MP (@lem5252679 s _68754 a) (@lem5251986 _68754 s a h1)). Qed.
Lemma lem5252684 (s : real -> Prop) (a : real) (h1 : term105 s a) : term469 s a.
Proof. exact (@lem5252683 a s a h1). Qed.
Lemma lem5252687 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : False.
Proof. exact (@lem5252684 s a h1 (@lem5252681 x s a h2 h3)). Qed.
Lemma lem5252688 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : term461.
Proof. exact (fun h0 : ~ False => @lem5252687 x s a h1 h2 h3). Qed.
Lemma lem5252690 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252691 : term461 = False.
Proof. exact (@lem5252690 False). Qed.
Lemma lem5252692 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : False.
Proof. exact (EQ_MP (@lem5252691) (@lem5252688 x s a h1 h2 h3)). Qed.
Lemma lem5252748 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : @IN real x s.
Proof. exact (proj1 (@lem5251250 s a x h1)). Qed.
Lemma lem5252749 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : term403 x s.
Proof. exact (fun h0 : term181 x s => @lem5252748 s a x h1). Qed.
Lemma lem5252751 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252752 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5252751 (@IN real x s)). Qed.
Lemma lem5252753 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : @IN real x s.
Proof. exact (EQ_MP (@lem5252752 x s) (@lem5252749 s a x h1)). Qed.
Lemma lem5252759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5252760 (a : real) (_68763 : real) (s : real -> Prop) : (term108 s a _68763) = (term404 a _68763 s).
Proof. exact (@lem5252759 (real_le a _68763) (term181 _68763 s)). Qed.
Lemma lem5252766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252767 (a : real) (_68763 : real) (s : real -> Prop) : (term405 s a _68763) = (term406 a _68763 s).
Proof. exact (MK_COMB (@lem5252766) (@lem5252760 a _68763 s)). Qed.
Lemma lem5252773 (a : real) (_68763 : real) (s : real -> Prop) : (term404 a _68763 s) = (term404 a _68763 s).
Proof. exact (eq_refl (term404 a _68763 s)). Qed.
Lemma lem5252774 (a : real) (_68763 : real) (s : real -> Prop) : ((term108 s a _68763) = (term404 a _68763 s)) = ((term404 a _68763 s) = (term404 a _68763 s)).
Proof. exact (MK_COMB (@lem5252767 a _68763 s) (@lem5252773 a _68763 s)). Qed.
Lemma lem5252776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5252777 (x : Prop) : (x = x) = True.
Proof. exact (@lem5252776 Prop x). Qed.
Lemma lem5252778 (a : real) (_68763 : real) (s : real -> Prop) : ((term404 a _68763 s) = (term404 a _68763 s)) = True.
Proof. exact (@lem5252777 (term404 a _68763 s)). Qed.
Lemma lem5252779 (a : real) (_68763 : real) (s : real -> Prop) : ((term108 s a _68763) = (term404 a _68763 s)) = True.
Proof. exact (TRANS (@lem5252774 a _68763 s) (@lem5252778 a _68763 s)). Qed.
Lemma lem5252780 (a : real) (_68763 : real) (s : real -> Prop) : True = ((term108 s a _68763) = (term404 a _68763 s)).
Proof. exact (SYM (@lem5252779 a _68763 s)). Qed.
Lemma lem5252781 (a : real) (_68763 : real) (s : real -> Prop) : (term108 s a _68763) = (term404 a _68763 s).
Proof. exact (EQ_MP (@lem5252780 a _68763 s) (@lem0)). Qed.
Lemma lem5252782 (_68763 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term404 a _68763 s.
Proof. exact (EQ_MP (@lem5252781 a _68763 s) (@lem5252036 _68763 x s a h1)). Qed.
Lemma lem5252784 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5252785 (s : real -> Prop) (a : real) (_68763 : real) : (term404 a _68763 s) = (term408 s a _68763).
Proof. exact (@lem5252784 (term181 _68763 s) (real_le a _68763)). Qed.
Lemma lem5252787 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5252788 (_68763 : real) (s : real -> Prop) : (term410 _68763 s) = (@IN real _68763 s).
Proof. exact (@lem5252787 (@IN real _68763 s)). Qed.
Lemma lem5252789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5252790 (_68763 : real) (s : real -> Prop) : (term411 _68763 s) = (term412 _68763 s).
Proof. exact (MK_COMB (@lem5252789) (@lem5252788 _68763 s)). Qed.
Lemma lem5252791 (a : real) (_68763 : real) : (real_le a _68763) = (real_le a _68763).
Proof. exact (eq_refl (real_le a _68763)). Qed.
Lemma lem5252792 (s : real -> Prop) (a : real) (_68763 : real) : (term408 s a _68763) = (term89 s a _68763).
Proof. exact (MK_COMB (@lem5252790 _68763 s) (@lem5252791 a _68763)). Qed.
Lemma lem5252793 (s : real -> Prop) (a : real) (_68763 : real) : (term404 a _68763 s) = (term89 s a _68763).
Proof. exact (TRANS (@lem5252785 s a _68763) (@lem5252792 s a _68763)). Qed.
Lemma lem5252796 (_68763 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term89 s a _68763.
Proof. exact (EQ_MP (@lem5252793 s a _68763) (@lem5252782 _68763 x s a h1)). Qed.
Lemma lem5252797 (x : real) (s : real -> Prop) (a : real) (h1 : term249 x s a) : term89 s a x.
Proof. exact (@lem5252796 x x s a h1). Qed.
Lemma lem5252800 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : real_le a x.
Proof. exact (@lem5252797 x s a h2 (@lem5252753 s a x h1)). Qed.
Lemma lem5252801 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : term402 a x.
Proof. exact (fun h0 : term390 a x => @lem5252800 x s a h1 h2). Qed.
Lemma lem5252803 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252804 (a : real) (x : real) : (term402 a x) = (real_le a x).
Proof. exact (@lem5252803 (real_le a x)). Qed.
Lemma lem5252805 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : real_le a x.
Proof. exact (EQ_MP (@lem5252804 a x) (@lem5252801 x s a h1 h2)). Qed.
Lemma lem5252808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5252810 (a : real) (x : real) : (term390 a x) = (term462 a x).
Proof. exact (@lem5252808 (real_le a x)). Qed.
Lemma lem5252813 (s : real -> Prop) (a : real) (x : real) (h1 : term107 s a x) : term462 a x.
Proof. exact (EQ_MP (@lem5252810 a x) (@lem5252040 s a x h1)). Qed.
Lemma lem5252816 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : False.
Proof. exact (@lem5252813 s a x h1 (@lem5252805 x s a h1 h2)). Qed.
Lemma lem5252817 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : term461.
Proof. exact (fun h0 : ~ False => @lem5252816 x s a h1 h2). Qed.
Lemma lem5252819 (p : Prop) : (term401 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5252820 : term461 = False.
Proof. exact (@lem5252819 False). Qed.
Lemma lem5252821 (x : real) (s : real -> Prop) (a : real) (h1 : term107 s a x) (h2 : term249 x s a) : False.
Proof. exact (EQ_MP (@lem5252820) (@lem5252817 x s a h1 h2)). Qed.
Lemma lem5252822 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : (term181 a s) = False.
Proof. exact (prop_ext (fun h4 : term181 a s => @lem5252474 x s a y h1 h2 h3) (fun h4 : False => @lem5251874 a s h2)). Qed.
Lemma lem5252823 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : False.
Proof. exact (EQ_MP (@lem5252822 x s a y h1 h2 h3) (@lem5251874 a s h2)). Qed.
Lemma lem5252824 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : (term181 a s) = False.
Proof. exact (prop_ext (fun h4 : term181 a s => @lem5252823 x s a y h1 h2 h3) (fun h4 : False => @lem5251365 a s h2)). Qed.
Lemma lem5252825 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : False.
Proof. exact (EQ_MP (@lem5252824 x s a y h1 h2 h3) (@lem5251365 a s h2)). Qed.
Lemma lem5252826 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : (term105 s a) = False.
Proof. exact (prop_ext (fun h4 : term105 s a => @lem5252692 x s a h1 h2 h3) (fun h4 : False => @lem5251600 s a h1)). Qed.
Lemma lem5252827 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : False.
Proof. exact (EQ_MP (@lem5252826 x s a h1 h2 h3) (@lem5251600 s a h1)). Qed.
Lemma lem5252828 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5252827 x s a h1 h2 h3) (fun h4 : False => @lem5251514 h2)). Qed.
Lemma lem5252829 (x : real) (s : real -> Prop) (a : real) (h1 : term105 s a) (h2 : term68) (h3 : term249 x s a) : False.
Proof. exact (EQ_MP (@lem5252828 x s a h1 h2 h3) (@lem5251514 h2)). Qed.
Lemma lem5252830 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : (term181 a s) = False.
Proof. exact (prop_ext (fun h4 : term181 a s => @lem5252825 x s a y h1 h2 h3) (fun h4 : False => @lem5251365 a s h2)). Qed.
Lemma lem5252831 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term181 a s) (h3 : term220 x s a y) : False.
Proof. exact (EQ_MP (@lem5252830 x s a y h1 h2 h3) (@lem5251365 a s h2)). Qed.
Lemma lem5252832 (x : real) (s : real -> Prop) (a : real) (h1 : term68) (h2 : term249 x s a) : False.
Proof. exact (or_elim (@lem5251246 x s a h2) (fun h0 : term105 s a => @lem5252829 x s a h0 h1 h2) (fun h0 : term107 s a x => @lem5252821 x s a h0 h2)). Qed.
Lemma lem5252833 (x : real) (s : real -> Prop) (a : real) (y : real) (h1 : term14) (h2 : term220 x s a y) : False.
Proof. exact (or_elim (@lem5251235 x s a y h2) (fun h0 : term181 a s => @lem5252831 x s a y h1 h0 h2) (fun h0 : term107 s a y => @lem5252603 x s a y h2 h0)). Qed.
Lemma lem5252834 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term318 y x s a) : False.
Proof. exact (or_elim (@lem5251227 y x s a h3) (fun h0 : term220 x s a y => @lem5252833 x s a y h1 h0) (fun h0 : term249 x s a => @lem5252832 x s a h2 h0)). Qed.
Lemma lem5252835 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term318 y x s a) : (term318 y x s a) = False.
Proof. exact (prop_ext (fun h4 : term318 y x s a => @lem5252834 y x s a h1 h2 h3) (fun h4 : False => @lem5251226 y x s a h3)). Qed.
Lemma lem5252836 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term318 y x s a) : False.
Proof. exact (EQ_MP (@lem5252835 y x s a h1 h2 h3) (@lem5251226 y x s a h3)). Qed.
Lemma lem5252837 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term318 y x s a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5252836 y x s a h1 h2 h3) (fun h4 : False => @lem5251077 h2)). Qed.
Lemma lem5252838 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term318 y x s a) : False.
Proof. exact (EQ_MP (@lem5252837 y x s a h1 h2 h3) (@lem5251077 h2)). Qed.
Lemma lem5252839 (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term321 x s a) : False.
Proof. exact (ex_elim (@lem5250968 x s a h3) (fun y : real => fun h0 : term320 x s a y => @lem5252838 y x s a h1 h2 h0)). Qed.
Lemma lem5252840 (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term323 s a) : False.
Proof. exact (ex_elim (@lem5250967 s a h3) (fun x : real => fun h0 : term322 s a x => @lem5252839 x s a h1 h2 h0)). Qed.
Lemma lem5252841 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : False.
Proof. exact (ex_elim (@lem5250573 a h3) (fun s : real -> Prop => fun h0 : term324 a s => @lem5252840 s a h1 h2 h0)). Qed.
Lemma lem5252842 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5252841 a h1 h2 h3) (fun h4 : False => @lem5250966 h2)). Qed.
Lemma lem5252843 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem5252842 a h1 h2 h3) (@lem5250966 h2)). Qed.
Lemma lem5252844 (a : real) (h1 : term14) (h2 : term61 a) : term66.
Proof. exact (fun h0 : term68 => @lem5252843 a h1 h0 h2). Qed.
Lemma lem5252845 : term66 = term67.
Proof. exact (@lem69 term68). Qed.
Lemma lem5252846 (a : real) (h1 : term14) (h2 : term61 a) : term67.
Proof. exact (EQ_MP (@lem5252845) (@lem5252844 a h1 h2)). Qed.
Lemma lem5252847 (a : real) (h1 : term14) (h2 : term61 a) : term71.
Proof. exact (fun h0 : term88 => @lem5252846 a h1 h2). Qed.
Lemma lem5252848 (a : real) (h1 : term61 a) : term74.
Proof. exact (fun h0 : term14 => @lem5252847 a h0 h1). Qed.
Lemma lem5252849 (a : real) : term76 a.
Proof. exact (fun h0 : term61 a => @lem5252848 a h0). Qed.
Lemma lem5252854 : term80.
Proof. exact (fun a : real => @lem5252849 a). Qed.
Lemma lem5252855 : term79.
Proof. exact (EQ_MP (@lem5249847) (@lem5252854)). Qed.
Lemma lem5252856 (a : real) : term470 a.
Proof. exact (@lem5252855 a). Qed.
Lemma lem5252857 (a : real) : (term470 a) = (term62 a).
Proof. exact (eq_refl (term470 a)). Qed.
Lemma lem5252858 (a : real) : term62 a.
Proof. exact (EQ_MP (@lem5252857 a) (@lem5252856 a)). Qed.
Lemma lem5252860 (a : real) : term62 a.
Proof. exact (@lem5249511 a (@lem5252858 a)). Qed.
Lemma lem5252861 (a : real) (h1 : term61 a) : term73.
Proof. exact (@lem5252860 a (@lem5249496 a h1)). Qed.
Lemma lem5252862 (a : real) (h1 : term61 a) : term70.
Proof. exact (@lem5252861 a h1 (@lem1339379)). Qed.
Lemma lem5252863 (a : real) (h1 : term61 a) : term66.
Proof. exact (@lem5252862 a h1 (@lem1339577)). Qed.
Lemma lem5252864 (a : real) (h1 : term61 a) : False.
Proof. exact (@lem5252863 a h1 (@lem1339240)). Qed.
Lemma lem5252865 (a : real) (h1 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h2 : term61 a => @lem5252864 a h1) (fun h2 : False => @lem5249496 a h1)). Qed.
Lemma lem5252866 (a : real) (h1 : term61 a) : False.
Proof. exact (EQ_MP (@lem5252865 a h1) (@lem5249496 a h1)). Qed.
Lemma lem5252867 (a : real) : term60 a.
Proof. exact (fun h0 : term61 a => @lem5252866 a h0). Qed.
Lemma lem5252868 (a : real) : term58 a.
Proof. exact (EQ_MP (@lem5249495 a) (@lem5252867 a)). Qed.
Lemma lem5252869 (a : real) : term57 a.
Proof. exact (EQ_MP (@lem5249491 a) (@lem5252868 a)). Qed.
