Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LMUL_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_LMUL_EQ_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1602518 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (term0 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1602519 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (real_lt y x) = (term0 x y).
Proof. exact (SYM (@lem1602518 y x h1)). Qed.
Lemma lem1602520 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (real_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1602521 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (term0 x y) = (real_lt y x).
Proof. exact (SYM (@lem1602520 x y h1)). Qed.
Lemma lem1602522 (x : real) (y : real) : ((term0 x y) = (real_lt y x)) = ((real_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_lt y x) => @lem1602519 y x h1) (fun h1 : (real_lt y x) = (term0 x y) => @lem1602521 x y h1)). Qed.
Lemma lem1602523 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1602522 x y)). Qed.
Lemma lem1602524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602525 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1602524) (@lem1602523 x)). Qed.
Lemma lem1602526 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1602525 x)). Qed.
Lemma lem1602527 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602528 : term7 = term8.
Proof. exact (MK_COMB (@lem1602527) (@lem1602526)). Qed.
Lemma lem1602529 : term8.
Proof. exact (EQ_MP (@lem1602528) (@lem1495933)). Qed.
Lemma lem1602530 (x : real) : term9 x.
Proof. exact (@lem1602377 x). Qed.
Lemma lem1602531 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1602532 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1602531 x) (@lem1602530 x)). Qed.
Lemma lem1602533 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1602532 x y). Qed.
Lemma lem1602534 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1602535 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1602534 x y) (@lem1602533 x y)). Qed.
Lemma lem1602536 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1602535 x y z). Qed.
Lemma lem1602537 (z : real) (x : real) (y : real) : (term13 x y z) = (term14 z x y).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1602538 (z : real) (x : real) (y : real) : term14 z x y.
Proof. exact (EQ_MP (@lem1602537 z x y) (@lem1602536 x y z)). Qed.
Lemma lem1602539 (z : real) (h1 : term15 z) : term15 z.
Proof. exact (h1). Qed.
Lemma lem1602540 (x : real) (y : real) (z : real) (h1 : term15 z) : (term16 x z y) = (real_le x y).
Proof. exact (@lem1602538 z x y (@lem1602539 z h1)). Qed.
Lemma lem1602546 (x : real) : term17 x.
Proof. exact (@lem1602529 x). Qed.
Lemma lem1602547 (x : real) : (term17 x) = (term4 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1602548 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1602547 x) (@lem1602546 x)). Qed.
Lemma lem1602549 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1602548 x y). Qed.
Lemma lem1602550 (x : real) (y : real) : (term18 x y) = ((real_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1602567 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1602568 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem1602567 p q p' q'). Qed.
Lemma lem1602569 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem1602568 p q p'). Qed.
Lemma lem1602570 (z : real) (x : real) (y : real) : term22 z x y.
Proof. exact (@lem1602569 (term15 z) ((term23 x z y) = (real_lt x y))). Qed.
Lemma lem1602571 (z : real) (x : real) (y : real) (p' : Prop) : term24 z x y p'.
Proof. exact (@lem1602570 z x y p'). Qed.
Lemma lem1602572 (z : real) (x : real) (y : real) (p' : Prop) : (term24 z x y p') = (term25 z x y p').
Proof. exact (eq_refl (term24 z x y p')). Qed.
Lemma lem1602573 (z : real) (x : real) (y : real) (p' : Prop) : term25 z x y p'.
Proof. exact (EQ_MP (@lem1602572 z x y p') (@lem1602571 z x y p')). Qed.
Lemma lem1602574 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term26 z x y p' q'.
Proof. exact (@lem1602573 z x y p' q'). Qed.
Lemma lem1602575 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term26 z x y p' q') = (term27 z x y p' q').
Proof. exact (eq_refl (term26 z x y p' q')). Qed.
Lemma lem1602576 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term27 z x y p' q'.
Proof. exact (EQ_MP (@lem1602575 z x y p' q') (@lem1602574 z x y p' q')). Qed.
Lemma lem1602578 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602550 x y) (@lem1602549 x y)). Qed.
Lemma lem1602579 (z : real) : (term15 z) = (term28 z).
Proof. exact (@lem1602578 z term29). Qed.
Lemma lem1602580 (x : real) (y : real) (z : real) (q' : Prop) : term30 x y z q'.
Proof. exact (@lem1602576 z x y (term28 z) q'). Qed.
Lemma lem1602581 (x : real) (y : real) (z : real) (q' : Prop) : term31 x y z q'.
Proof. exact (@lem1602580 x y z q' (@lem1602579 z)). Qed.
Lemma lem1602582 (z : real) (h1 : term28 z) : term28 z.
Proof. exact (h1). Qed.
Lemma lem1602583 (z : real) : term32 z.
Proof. exact (@lem82 (term33 z)). Qed.
Lemma lem1602588 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602550 x y) (@lem1602549 x y)). Qed.
Lemma lem1602589 (y : real) (z : real) (x : real) : (term23 x z y) = (term34 y z x).
Proof. exact (@lem1602588 (real_mul z y) (real_mul z x)). Qed.
Lemma lem1602591 (z : real) (x : real) (y : real) : term14 z x y.
Proof. exact (fun h0 : term15 z => @lem1602540 x y z h0). Qed.
Lemma lem1602592 (z : real) (y : real) (x : real) : term14 z y x.
Proof. exact (@lem1602591 z y x). Qed.
Lemma lem1602594 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602550 x y) (@lem1602549 x y)). Qed.
Lemma lem1602595 (z : real) : (term15 z) = (term28 z).
Proof. exact (@lem1602594 z term29). Qed.
Lemma lem1602597 (z : real) (h1 : term28 z) : (term33 z) = False.
Proof. exact (@lem1602583 z (@lem1602582 z h1)). Qed.
Lemma lem1602598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602599 (z : real) (h1 : term28 z) : (term28 z) = (~ False).
Proof. exact (MK_COMB (@lem1602598) (@lem1602597 z h1)). Qed.
Lemma lem1602601 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1602602 (z : real) (h1 : term28 z) : (term28 z) = True.
Proof. exact (TRANS (@lem1602599 z h1) (@lem1602601)). Qed.
Lemma lem1602603 (z : real) (h1 : term28 z) : (term15 z) = True.
Proof. exact (TRANS (@lem1602595 z) (@lem1602602 z h1)). Qed.
Lemma lem1602604 (z : real) (h1 : term28 z) : True = (term15 z).
Proof. exact (SYM (@lem1602603 z h1)). Qed.
Lemma lem1602605 (z : real) (h1 : term28 z) : term15 z.
Proof. exact (EQ_MP (@lem1602604 z h1) (@lem0)). Qed.
Lemma lem1602606 (y : real) (x : real) (z : real) (h1 : term28 z) : (term16 y z x) = (real_le y x).
Proof. exact (@lem1602592 z y x (@lem1602605 z h1)). Qed.
Lemma lem1602607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602608 (y : real) (x : real) (z : real) (h1 : term28 z) : (term34 y z x) = (term0 y x).
Proof. exact (MK_COMB (@lem1602607) (@lem1602606 y x z h1)). Qed.
Lemma lem1602609 (y : real) (x : real) (z : real) (h1 : term28 z) : (term23 x z y) = (term0 y x).
Proof. exact (TRANS (@lem1602589 y z x) (@lem1602608 y x z h1)). Qed.
Lemma lem1602610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1602611 (y : real) (x : real) (z : real) (h1 : term28 z) : (term35 x z y) = (term36 y x).
Proof. exact (MK_COMB (@lem1602610) (@lem1602609 y x z h1)). Qed.
Lemma lem1602613 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602550 x y) (@lem1602549 x y)). Qed.
Lemma lem1602614 (y : real) (x : real) : (real_lt x y) = (term0 y x).
Proof. exact (@lem1602613 y x). Qed.
Lemma lem1602615 (y : real) (x : real) (z : real) (h1 : term28 z) : ((term23 x z y) = (real_lt x y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem1602611 y x z h1) (@lem1602614 y x)). Qed.
Lemma lem1602617 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1602618 (x : Prop) : (x = x) = True.
Proof. exact (@lem1602617 Prop x). Qed.
Lemma lem1602619 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem1602618 (term0 y x)). Qed.
Lemma lem1602620 (x : real) (y : real) (z : real) (h1 : term28 z) : ((term23 x z y) = (real_lt x y)) = True.
Proof. exact (TRANS (@lem1602615 y x z h1) (@lem1602619 y x)). Qed.
Lemma lem1602621 (z : real) (x : real) (y : real) : term37 z x y.
Proof. exact (fun h0 : term28 z => @lem1602620 x y z h0). Qed.
Lemma lem1602622 (x : real) (y : real) (z : real) : term38 x y z.
Proof. exact (@lem1602581 x y z True). Qed.
Lemma lem1602623 (x : real) (y : real) (z : real) : (term39 z x y) = (term40 z).
Proof. exact (@lem1602622 x y z (@lem1602621 z x y)). Qed.
Lemma lem1602625 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1602626 (z : real) : (term40 z) = True.
Proof. exact (@lem1602625 (term28 z)). Qed.
Lemma lem1602627 (z : real) (x : real) (y : real) : (term39 z x y) = True.
Proof. exact (TRANS (@lem1602623 x y z) (@lem1602626 z)). Qed.
Lemma lem1602628 (x : real) (y : real) : (term41 x y) = term42.
Proof. exact (fun_ext (fun z : real => @lem1602627 z x y)). Qed.
Lemma lem1602629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602630 (x : real) (y : real) : (term43 x y) = term44.
Proof. exact (MK_COMB (@lem1602629) (@lem1602628 x y)). Qed.
Lemma lem1602632 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602633 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602632 real t). Qed.
Lemma lem1602634 : term44 = True.
Proof. exact (@lem1602633 True). Qed.
Lemma lem1602635 (x : real) (y : real) : (term43 x y) = True.
Proof. exact (TRANS (@lem1602630 x y) (@lem1602634)). Qed.
Lemma lem1602636 (x : real) : (term47 x) = term42.
Proof. exact (fun_ext (fun y : real => @lem1602635 x y)). Qed.
Lemma lem1602637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602638 (x : real) : (term48 x) = term44.
Proof. exact (MK_COMB (@lem1602637) (@lem1602636 x)). Qed.
Lemma lem1602640 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602641 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602640 real t). Qed.
Lemma lem1602642 : term44 = True.
Proof. exact (@lem1602641 True). Qed.
Lemma lem1602643 (x : real) : (term48 x) = True.
Proof. exact (TRANS (@lem1602638 x) (@lem1602642)). Qed.
Lemma lem1602644 : term49 = term42.
Proof. exact (fun_ext (fun x : real => @lem1602643 x)). Qed.
Lemma lem1602645 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602646 : term50 = term44.
Proof. exact (MK_COMB (@lem1602645) (@lem1602644)). Qed.
Lemma lem1602648 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602649 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602648 real t). Qed.
Lemma lem1602650 : term44 = True.
Proof. exact (@lem1602649 True). Qed.
Lemma lem1602651 : term50 = True.
Proof. exact (TRANS (@lem1602646) (@lem1602650)). Qed.
Lemma lem1602652 : True = term50.
Proof. exact (SYM (@lem1602651)). Qed.
Lemma lem1602653 : term50.
Proof. exact (EQ_MP (@lem1602652) (@lem0)). Qed.
