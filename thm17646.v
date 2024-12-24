Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17646_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17513 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17514 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17515 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17514 p) (@lem17513 p)). Qed.
Lemma lem17516 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17517 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17530 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17531 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17530 q) (@lem17516 p h1)). Qed.
Lemma lem17532 (q : Prop) : (term4 q) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17533 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17534 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17533 q p) (@lem17532 q)). Qed.
Lemma lem17535 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17537 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17536) (@lem17535 p q)). Qed.
Lemma lem17538 (q : Prop) : ((term5 q) = (term6 q)) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl ((term5 q) = (term6 q))). Qed.
Lemma lem17539 (p : Prop) (q : Prop) : ((term3 q p) = ((term5 q) = (term6 q))) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17537 p q) (@lem17538 q)). Qed.
Lemma lem17540 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (TRANS (@lem17534 p q) (@lem17539 p q)). Qed.
Lemma lem17541 (q : Prop) (p : Prop) (h1 : p = True) : ((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q)).
Proof. exact (EQ_MP (@lem17540 p q) (@lem17531 q p h1)). Qed.
Lemma lem17542 (q : Prop) (p : Prop) (h1 : p = True) : ((term5 q) = (term6 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17541 q p h1)). Qed.
Lemma lem17543 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17544 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term11 q).
Proof. exact (MK_COMB (@lem17543 q) (@lem17517 p h1)). Qed.
Lemma lem17545 (q : Prop) : (term11 q) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem17546 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17547 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = ((term3 q p) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17546 q p) (@lem17545 q)). Qed.
Lemma lem17548 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17549 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17550 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17549) (@lem17548 p q)). Qed.
Lemma lem17551 (q : Prop) : ((term12 q) = (term13 q)) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl ((term12 q) = (term13 q))). Qed.
Lemma lem17552 (p : Prop) (q : Prop) : ((term3 q p) = ((term12 q) = (term13 q))) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17550 p q) (@lem17551 q)). Qed.
Lemma lem17553 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (TRANS (@lem17547 p q) (@lem17552 p q)). Qed.
Lemma lem17554 (q : Prop) (p : Prop) (h1 : p = False) : ((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q)).
Proof. exact (EQ_MP (@lem17553 p q) (@lem17544 q p h1)). Qed.
Lemma lem17555 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 q) = (term13 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17554 q p h1)). Qed.
Lemma lem17559 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17560 (q : Prop) : (True = q) = q.
Proof. exact (@lem17559 q). Qed.
Lemma lem17561 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17562 (q : Prop) : (term5 q) = (~ q).
Proof. exact (MK_COMB (@lem17561) (@lem17560 q)). Qed.
Lemma lem17563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17564 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem17563) (@lem17562 q)). Qed.
Lemma lem17568 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17569 (q : Prop) : (term16 q) = (~ q).
Proof. exact (@lem17568 (~ q)). Qed.
Lemma lem17570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17571 (q : Prop) : (term17 q) = (term18 q).
Proof. exact (MK_COMB (@lem17570) (@lem17569 q)). Qed.
Lemma lem17575 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17577 : term19 = (and False).
Proof. exact (MK_COMB (@lem17576) (@lem17575)). Qed.
Lemma lem17578 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17579 (q : Prop) : (term20 q) = (False /\ q).
Proof. exact (MK_COMB (@lem17577) (@lem17578 q)). Qed.
Lemma lem17581 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17582 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem17581 q). Qed.
Lemma lem17583 (q : Prop) : (term20 q) = False.
Proof. exact (TRANS (@lem17579 q) (@lem17582 q)). Qed.
Lemma lem17584 (q : Prop) : (term6 q) = (term21 q).
Proof. exact (MK_COMB (@lem17571 q) (@lem17583 q)). Qed.
Lemma lem17586 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem17587 (q : Prop) : (term21 q) = (~ q).
Proof. exact (@lem17586 (~ q)). Qed.
Lemma lem17588 (q : Prop) : (term6 q) = (~ q).
Proof. exact (TRANS (@lem17584 q) (@lem17587 q)). Qed.
Lemma lem17589 (q : Prop) : ((term5 q) = (term6 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17564 q) (@lem17588 q)). Qed.
Lemma lem17591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17592 (x : Prop) : (x = x) = True.
Proof. exact (@lem17591 Prop x). Qed.
Lemma lem17593 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17592 (~ q)). Qed.
Lemma lem17594 (q : Prop) : ((term5 q) = (term6 q)) = True.
Proof. exact (TRANS (@lem17589 q) (@lem17593 q)). Qed.
Lemma lem17595 (q : Prop) : True = ((term5 q) = (term6 q)).
Proof. exact (SYM (@lem17594 q)). Qed.
Lemma lem17596 (q : Prop) : (term5 q) = (term6 q).
Proof. exact (EQ_MP (@lem17595 q) (@lem0)). Qed.
Lemma lem17600 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17601 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem17600 q). Qed.
Lemma lem17602 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17603 (q : Prop) : (term12 q) = (term22 q).
Proof. exact (MK_COMB (@lem17602) (@lem17601 q)). Qed.
Lemma lem17605 (t : Prop) : (term22 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem17606 (q : Prop) : (term22 q) = q.
Proof. exact (@lem17605 q). Qed.
Lemma lem17607 (q : Prop) : (term12 q) = q.
Proof. exact (TRANS (@lem17603 q) (@lem17606 q)). Qed.
Lemma lem17608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17609 (q : Prop) : (term23 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem17608) (@lem17607 q)). Qed.
Lemma lem17613 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17614 (q : Prop) : (term24 q) = False.
Proof. exact (@lem17613 (~ q)). Qed.
Lemma lem17615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17616 (q : Prop) : (term25 q) = (or False).
Proof. exact (MK_COMB (@lem17615) (@lem17614 q)). Qed.
Lemma lem17620 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17622 : term26 = (and True).
Proof. exact (MK_COMB (@lem17621) (@lem17620)). Qed.
Lemma lem17623 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17624 (q : Prop) : (term27 q) = (True /\ q).
Proof. exact (MK_COMB (@lem17622) (@lem17623 q)). Qed.
Lemma lem17626 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17627 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem17626 q). Qed.
Lemma lem17628 (q : Prop) : (term27 q) = q.
Proof. exact (TRANS (@lem17624 q) (@lem17627 q)). Qed.
Lemma lem17629 (q : Prop) : (term13 q) = (False \/ q).
Proof. exact (MK_COMB (@lem17616 q) (@lem17628 q)). Qed.
Lemma lem17631 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17632 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem17631 q). Qed.
Lemma lem17633 (q : Prop) : (term13 q) = q.
Proof. exact (TRANS (@lem17629 q) (@lem17632 q)). Qed.
Lemma lem17634 (q : Prop) : ((term12 q) = (term13 q)) = (q = q).
Proof. exact (MK_COMB (@lem17609 q) (@lem17633 q)). Qed.
Lemma lem17636 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17637 (x : Prop) : (x = x) = True.
Proof. exact (@lem17636 Prop x). Qed.
Lemma lem17638 (q : Prop) : (q = q) = True.
Proof. exact (@lem17637 q). Qed.
Lemma lem17639 (q : Prop) : ((term12 q) = (term13 q)) = True.
Proof. exact (TRANS (@lem17634 q) (@lem17638 q)). Qed.
Lemma lem17640 (q : Prop) : True = ((term12 q) = (term13 q)).
Proof. exact (SYM (@lem17639 q)). Qed.
Lemma lem17641 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (EQ_MP (@lem17640 q) (@lem0)). Qed.
Lemma lem17642 (q : Prop) (p : Prop) (h1 : p = False) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17555 q p h1) (@lem17641 q)). Qed.
Lemma lem17643 (q : Prop) (p : Prop) (h1 : p = True) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17542 q p h1) (@lem17596 q)). Qed.
Lemma lem17646 (p : Prop) (q : Prop) : (term8 p q) = (term9 p q).
Proof. exact (or_elim (@lem17515 p) (fun h0 : p = True => @lem17643 q p h0) (fun h0 : p = False => @lem17642 q p h0)). Qed.
