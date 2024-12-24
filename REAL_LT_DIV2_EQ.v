Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_DIV2_EQ_term_abbrevs.
Require Import REAL_LT_INV_EQ_spec.
Require Import REAL_LT_RMUL_EQ_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1629490 (x : real) : term0 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1629491 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1629493 (x : real) : term3 x.
Proof. exact (@lem1602515 x). Qed.
Lemma lem1629494 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1629495 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1629494 x) (@lem1629493 x)). Qed.
Lemma lem1629496 (x : real) (y : real) : term5 x y.
Proof. exact (@lem1629495 x y). Qed.
Lemma lem1629497 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1629498 (x : real) (y : real) : term6 x y.
Proof. exact (EQ_MP (@lem1629497 x y) (@lem1629496 x y)). Qed.
Lemma lem1629499 (x : real) (y : real) (z : real) : term7 x y z.
Proof. exact (@lem1629498 x y z). Qed.
Lemma lem1629500 (z : real) (x : real) (y : real) : (term7 x y z) = (term8 z x y).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1629501 (z : real) (x : real) (y : real) : term8 z x y.
Proof. exact (EQ_MP (@lem1629500 z x y) (@lem1629499 x y z)). Qed.
Lemma lem1629502 (z : real) (h1 : term2 z) : term2 z.
Proof. exact (h1). Qed.
Lemma lem1629503 (x : real) (y : real) (z : real) (h1 : term2 z) : (term9 x y z) = (real_lt x y).
Proof. exact (@lem1629501 z x y (@lem1629502 z h1)). Qed.
Lemma lem1629509 (x : real) : term10 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1629510 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1629511 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1629510 x) (@lem1629509 x)). Qed.
Lemma lem1629512 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1629511 x y). Qed.
Lemma lem1629513 (x : real) (y : real) : (term12 x y) = ((real_div x y) = (term13 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1629530 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1629531 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem1629530 p q p' q'). Qed.
Lemma lem1629532 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem1629531 p q p'). Qed.
Lemma lem1629533 (z : real) (x : real) (y : real) : term17 z x y.
Proof. exact (@lem1629532 (term2 z) ((term18 x y z) = (real_lt x y))). Qed.
Lemma lem1629534 (z : real) (x : real) (y : real) (p' : Prop) : term19 z x y p'.
Proof. exact (@lem1629533 z x y p'). Qed.
Lemma lem1629535 (z : real) (x : real) (y : real) (p' : Prop) : (term19 z x y p') = (term20 z x y p').
Proof. exact (eq_refl (term19 z x y p')). Qed.
Lemma lem1629536 (z : real) (x : real) (y : real) (p' : Prop) : term20 z x y p'.
Proof. exact (EQ_MP (@lem1629535 z x y p') (@lem1629534 z x y p')). Qed.
Lemma lem1629537 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term21 z x y p' q'.
Proof. exact (@lem1629536 z x y p' q'). Qed.
Lemma lem1629538 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term21 z x y p' q') = (term22 z x y p' q').
Proof. exact (eq_refl (term21 z x y p' q')). Qed.
Lemma lem1629539 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term22 z x y p' q'.
Proof. exact (EQ_MP (@lem1629538 z x y p' q') (@lem1629537 z x y p' q')). Qed.
Lemma lem1629540 (z : real) : (term2 z) = (term2 z).
Proof. exact (eq_refl (term2 z)). Qed.
Lemma lem1629541 (x : real) (y : real) (z : real) (q' : Prop) : term23 x y z q'.
Proof. exact (@lem1629539 z x y (term2 z) q'). Qed.
Lemma lem1629542 (x : real) (y : real) (z : real) (q' : Prop) : term24 x y z q'.
Proof. exact (@lem1629541 x y z q' (@lem1629540 z)). Qed.
Lemma lem1629543 (z : real) (h1 : term2 z) : term2 z.
Proof. exact (h1). Qed.
Lemma lem1629544 (z : real) : (term2 z) = ((term2 z) = True).
Proof. exact (@lem7 (term2 z)). Qed.
Lemma lem1629549 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1629513 x y) (@lem1629512 x y)). Qed.
Lemma lem1629550 (x : real) (z : real) : (real_div x z) = (term13 x z).
Proof. exact (@lem1629549 x z). Qed.
Lemma lem1629551 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1629552 (x : real) (z : real) : (term25 x z) = (term26 x z).
Proof. exact (MK_COMB (@lem1629551) (@lem1629550 x z)). Qed.
Lemma lem1629554 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1629513 x y) (@lem1629512 x y)). Qed.
Lemma lem1629555 (y : real) (z : real) : (real_div y z) = (term13 y z).
Proof. exact (@lem1629554 y z). Qed.
Lemma lem1629556 (x : real) (y : real) (z : real) : (term18 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem1629552 x z) (@lem1629555 y z)). Qed.
Lemma lem1629558 (z : real) (x : real) (y : real) : term8 z x y.
Proof. exact (fun h0 : term2 z => @lem1629503 x y z h0). Qed.
Lemma lem1629559 (z : real) (x : real) (y : real) : term28 z x y.
Proof. exact (@lem1629558 (real_inv z) x y). Qed.
Lemma lem1629561 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1629491 x) (@lem1629490 x)). Qed.
Lemma lem1629562 (z : real) : (term1 z) = (term2 z).
Proof. exact (@lem1629561 z). Qed.
Lemma lem1629564 (z : real) (h1 : term2 z) : (term2 z) = True.
Proof. exact (EQ_MP (@lem1629544 z) (@lem1629543 z h1)). Qed.
Lemma lem1629565 (z : real) (h1 : term2 z) : (term1 z) = True.
Proof. exact (TRANS (@lem1629562 z) (@lem1629564 z h1)). Qed.
Lemma lem1629566 (z : real) (h1 : term2 z) : True = (term1 z).
Proof. exact (SYM (@lem1629565 z h1)). Qed.
Lemma lem1629567 (z : real) (h1 : term2 z) : term1 z.
Proof. exact (EQ_MP (@lem1629566 z h1) (@lem0)). Qed.
Lemma lem1629568 (x : real) (y : real) (z : real) (h1 : term2 z) : (term27 x y z) = (real_lt x y).
Proof. exact (@lem1629559 z x y (@lem1629567 z h1)). Qed.
Lemma lem1629569 (x : real) (y : real) (z : real) (h1 : term2 z) : (term18 x y z) = (real_lt x y).
Proof. exact (TRANS (@lem1629556 x y z) (@lem1629568 x y z h1)). Qed.
Lemma lem1629570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629571 (x : real) (y : real) (z : real) (h1 : term2 z) : (term29 x y z) = (term30 x y).
Proof. exact (MK_COMB (@lem1629570) (@lem1629569 x y z h1)). Qed.
Lemma lem1629572 (x : real) (y : real) : (real_lt x y) = (real_lt x y).
Proof. exact (eq_refl (real_lt x y)). Qed.
Lemma lem1629573 (x : real) (y : real) (z : real) (h1 : term2 z) : ((term18 x y z) = (real_lt x y)) = ((real_lt x y) = (real_lt x y)).
Proof. exact (MK_COMB (@lem1629571 x y z h1) (@lem1629572 x y)). Qed.
Lemma lem1629575 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1629576 (x : Prop) : (x = x) = True.
Proof. exact (@lem1629575 Prop x). Qed.
Lemma lem1629577 (x : real) (y : real) : ((real_lt x y) = (real_lt x y)) = True.
Proof. exact (@lem1629576 (real_lt x y)). Qed.
Lemma lem1629578 (x : real) (y : real) (z : real) (h1 : term2 z) : ((term18 x y z) = (real_lt x y)) = True.
Proof. exact (TRANS (@lem1629573 x y z h1) (@lem1629577 x y)). Qed.
Lemma lem1629579 (z : real) (x : real) (y : real) : term31 z x y.
Proof. exact (fun h0 : term2 z => @lem1629578 x y z h0). Qed.
Lemma lem1629580 (x : real) (y : real) (z : real) : term32 x y z.
Proof. exact (@lem1629542 x y z True). Qed.
Lemma lem1629581 (x : real) (y : real) (z : real) : (term33 z x y) = (term34 z).
Proof. exact (@lem1629580 x y z (@lem1629579 z x y)). Qed.
Lemma lem1629583 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1629584 (z : real) : (term34 z) = True.
Proof. exact (@lem1629583 (term2 z)). Qed.
Lemma lem1629585 (z : real) (x : real) (y : real) : (term33 z x y) = True.
Proof. exact (TRANS (@lem1629581 x y z) (@lem1629584 z)). Qed.
Lemma lem1629586 (x : real) (y : real) : (term35 x y) = term36.
Proof. exact (fun_ext (fun z : real => @lem1629585 z x y)). Qed.
Lemma lem1629587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629588 (x : real) (y : real) : (term37 x y) = term38.
Proof. exact (MK_COMB (@lem1629587) (@lem1629586 x y)). Qed.
Lemma lem1629590 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629591 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629590 real t). Qed.
Lemma lem1629592 : term38 = True.
Proof. exact (@lem1629591 True). Qed.
Lemma lem1629593 (x : real) (y : real) : (term37 x y) = True.
Proof. exact (TRANS (@lem1629588 x y) (@lem1629592)). Qed.
Lemma lem1629594 (x : real) : (term41 x) = term36.
Proof. exact (fun_ext (fun y : real => @lem1629593 x y)). Qed.
Lemma lem1629595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629596 (x : real) : (term42 x) = term38.
Proof. exact (MK_COMB (@lem1629595) (@lem1629594 x)). Qed.
Lemma lem1629598 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629599 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629598 real t). Qed.
Lemma lem1629600 : term38 = True.
Proof. exact (@lem1629599 True). Qed.
Lemma lem1629601 (x : real) : (term42 x) = True.
Proof. exact (TRANS (@lem1629596 x) (@lem1629600)). Qed.
Lemma lem1629602 : term43 = term36.
Proof. exact (fun_ext (fun x : real => @lem1629601 x)). Qed.
Lemma lem1629603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629604 : term44 = term38.
Proof. exact (MK_COMB (@lem1629603) (@lem1629602)). Qed.
Lemma lem1629606 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629607 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629606 real t). Qed.
Lemma lem1629608 : term38 = True.
Proof. exact (@lem1629607 True). Qed.
Lemma lem1629609 : term44 = True.
Proof. exact (TRANS (@lem1629604) (@lem1629608)). Qed.
Lemma lem1629610 : True = term44.
Proof. exact (SYM (@lem1629609)). Qed.
Lemma lem1629611 : term44.
Proof. exact (EQ_MP (@lem1629610) (@lem0)). Qed.
