Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRANSITIVE_STEPWISE_LT_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import TRANSITIVE_STEPWISE_LT_EQ_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Lemma lem286498 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem286499 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem286500 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem286499 a) (@lem286498 a)). Qed.
Lemma lem286501 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem286502 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem286515 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem286516 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem286515 b c) (@lem286501 a h1)). Qed.
Lemma lem286517 (b : Prop) (c : Prop) : (term4 b c) = (term5 b c).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem286518 (b : Prop) (c : Prop) (a : Prop) : (term6 b c a) = (term6 b c a).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem286519 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = (term5 b c)).
Proof. exact (MK_COMB (@lem286518 b c a) (@lem286517 b c)). Qed.
Lemma lem286520 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = (term7 a b c).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem286521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem286522 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = (term8 a b c).
Proof. exact (MK_COMB (@lem286521) (@lem286520 a b c)). Qed.
Lemma lem286523 (b : Prop) (c : Prop) : (term5 b c) = (term5 b c).
Proof. exact (eq_refl (term5 b c)). Qed.
Lemma lem286524 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term5 b c)) = ((term7 a b c) = (term5 b c)).
Proof. exact (MK_COMB (@lem286522 a b c) (@lem286523 b c)). Qed.
Lemma lem286525 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term7 a b c) = (term5 b c)).
Proof. exact (TRANS (@lem286519 a b c) (@lem286524 a b c)). Qed.
Lemma lem286526 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term7 a b c) = (term5 b c).
Proof. exact (EQ_MP (@lem286525 a b c) (@lem286516 b c a h1)). Qed.
Lemma lem286527 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term5 b c) = (term7 a b c).
Proof. exact (SYM (@lem286526 b c a h1)). Qed.
Lemma lem286528 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem286529 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term9 b c).
Proof. exact (MK_COMB (@lem286528 b c) (@lem286502 a h1)). Qed.
Lemma lem286530 (b : Prop) (c : Prop) : (term9 b c) = (term10 b c).
Proof. exact (eq_refl (term9 b c)). Qed.
Lemma lem286531 (b : Prop) (c : Prop) (a : Prop) : (term6 b c a) = (term6 b c a).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem286532 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term9 b c)) = ((term3 b c a) = (term10 b c)).
Proof. exact (MK_COMB (@lem286531 b c a) (@lem286530 b c)). Qed.
Lemma lem286533 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = (term7 a b c).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem286534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem286535 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = (term8 a b c).
Proof. exact (MK_COMB (@lem286534) (@lem286533 a b c)). Qed.
Lemma lem286536 (b : Prop) (c : Prop) : (term10 b c) = (term10 b c).
Proof. exact (eq_refl (term10 b c)). Qed.
Lemma lem286537 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term10 b c)) = ((term7 a b c) = (term10 b c)).
Proof. exact (MK_COMB (@lem286535 a b c) (@lem286536 b c)). Qed.
Lemma lem286538 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term9 b c)) = ((term7 a b c) = (term10 b c)).
Proof. exact (TRANS (@lem286532 a b c) (@lem286537 a b c)). Qed.
Lemma lem286539 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term7 a b c) = (term10 b c).
Proof. exact (EQ_MP (@lem286538 a b c) (@lem286529 b c a h1)). Qed.
Lemma lem286540 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term10 b c) = (term7 a b c).
Proof. exact (SYM (@lem286539 b c a h1)). Qed.
Lemma lem286544 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem286545 (c : Prop) (b : Prop) : (term11 c b) = (c = b).
Proof. exact (@lem286544 (c = b)). Qed.
Lemma lem286548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286549 (c : Prop) (b : Prop) : (term12 c b) = (term13 c b).
Proof. exact (MK_COMB (@lem286548) (@lem286545 c b)). Qed.
Lemma lem286553 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem286554 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem286553 b). Qed.
Lemma lem286555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286556 (b : Prop) : (term14 b) = (imp b).
Proof. exact (MK_COMB (@lem286555) (@lem286554 b)). Qed.
Lemma lem286557 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem286558 (b : Prop) (c : Prop) : (term15 b c) = (b -> c).
Proof. exact (MK_COMB (@lem286556 b) (@lem286557 c)). Qed.
Lemma lem286561 (b : Prop) (c : Prop) : (term5 b c) = (term16 b c).
Proof. exact (MK_COMB (@lem286549 c b) (@lem286558 b c)). Qed.
Lemma lem286566 (b : Prop) (c : Prop) : (term16 b c) = (term5 b c).
Proof. exact (SYM (@lem286561 b c)). Qed.
Lemma lem286567 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem286568 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem286569 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem286568 c) (@lem286567 c)). Qed.
Lemma lem286570 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem286571 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem286582 (b : Prop) : (term17 b) = (term17 b).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem286583 (b : Prop) (c : Prop) (h1 : c = True) : (term18 b c) = (term19 b).
Proof. exact (MK_COMB (@lem286582 b) (@lem286570 c h1)). Qed.
Lemma lem286584 (b : Prop) : (term19 b) = (term20 b).
Proof. exact (eq_refl (term19 b)). Qed.
Lemma lem286585 (b : Prop) (c : Prop) : (term21 b c) = (term21 b c).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem286586 (c : Prop) (b : Prop) : ((term18 b c) = (term19 b)) = ((term18 b c) = (term20 b)).
Proof. exact (MK_COMB (@lem286585 b c) (@lem286584 b)). Qed.
Lemma lem286587 (b : Prop) (c : Prop) : (term18 b c) = (term16 b c).
Proof. exact (eq_refl (term18 b c)). Qed.
Lemma lem286588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem286589 (b : Prop) (c : Prop) : (term21 b c) = (term22 b c).
Proof. exact (MK_COMB (@lem286588) (@lem286587 b c)). Qed.
Lemma lem286590 (b : Prop) : (term20 b) = (term20 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem286591 (c : Prop) (b : Prop) : ((term18 b c) = (term20 b)) = ((term16 b c) = (term20 b)).
Proof. exact (MK_COMB (@lem286589 b c) (@lem286590 b)). Qed.
Lemma lem286592 (c : Prop) (b : Prop) : ((term18 b c) = (term19 b)) = ((term16 b c) = (term20 b)).
Proof. exact (TRANS (@lem286586 c b) (@lem286591 c b)). Qed.
Lemma lem286593 (b : Prop) (c : Prop) (h1 : c = True) : (term16 b c) = (term20 b).
Proof. exact (EQ_MP (@lem286592 c b) (@lem286583 b c h1)). Qed.
Lemma lem286594 (b : Prop) (c : Prop) (h1 : c = True) : (term20 b) = (term16 b c).
Proof. exact (SYM (@lem286593 b c h1)). Qed.
Lemma lem286595 (b : Prop) : (term17 b) = (term17 b).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem286596 (b : Prop) (c : Prop) (h1 : c = False) : (term18 b c) = (term23 b).
Proof. exact (MK_COMB (@lem286595 b) (@lem286571 c h1)). Qed.
Lemma lem286597 (b : Prop) : (term23 b) = (term24 b).
Proof. exact (eq_refl (term23 b)). Qed.
Lemma lem286598 (b : Prop) (c : Prop) : (term21 b c) = (term21 b c).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem286599 (c : Prop) (b : Prop) : ((term18 b c) = (term23 b)) = ((term18 b c) = (term24 b)).
Proof. exact (MK_COMB (@lem286598 b c) (@lem286597 b)). Qed.
Lemma lem286600 (b : Prop) (c : Prop) : (term18 b c) = (term16 b c).
Proof. exact (eq_refl (term18 b c)). Qed.
Lemma lem286601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem286602 (b : Prop) (c : Prop) : (term21 b c) = (term22 b c).
Proof. exact (MK_COMB (@lem286601) (@lem286600 b c)). Qed.
Lemma lem286603 (b : Prop) : (term24 b) = (term24 b).
Proof. exact (eq_refl (term24 b)). Qed.
Lemma lem286604 (c : Prop) (b : Prop) : ((term18 b c) = (term24 b)) = ((term16 b c) = (term24 b)).
Proof. exact (MK_COMB (@lem286602 b c) (@lem286603 b)). Qed.
Lemma lem286605 (c : Prop) (b : Prop) : ((term18 b c) = (term23 b)) = ((term16 b c) = (term24 b)).
Proof. exact (TRANS (@lem286599 c b) (@lem286604 c b)). Qed.
Lemma lem286606 (b : Prop) (c : Prop) (h1 : c = False) : (term16 b c) = (term24 b).
Proof. exact (EQ_MP (@lem286605 c b) (@lem286596 b c h1)). Qed.
Lemma lem286607 (b : Prop) (c : Prop) (h1 : c = False) : (term24 b) = (term16 b c).
Proof. exact (SYM (@lem286606 b c h1)). Qed.
Lemma lem286613 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem286614 (b : Prop) : (True = b) = b.
Proof. exact (@lem286613 b). Qed.
Lemma lem286615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286616 (b : Prop) : (term25 b) = (imp b).
Proof. exact (MK_COMB (@lem286615) (@lem286614 b)). Qed.
Lemma lem286618 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem286619 (b : Prop) : (b -> True) = True.
Proof. exact (@lem286618 b). Qed.
Lemma lem286620 (b : Prop) : (term20 b) = (b -> True).
Proof. exact (MK_COMB (@lem286616 b) (@lem286619 b)). Qed.
Lemma lem286622 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem286623 (b : Prop) : (b -> True) = True.
Proof. exact (@lem286622 b). Qed.
Lemma lem286624 (b : Prop) : (term20 b) = True.
Proof. exact (TRANS (@lem286620 b) (@lem286623 b)). Qed.
Lemma lem286625 (b : Prop) : True = (term20 b).
Proof. exact (SYM (@lem286624 b)). Qed.
Lemma lem286626 (b : Prop) : term20 b.
Proof. exact (EQ_MP (@lem286625 b) (@lem0)). Qed.
Lemma lem286632 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem286633 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem286632 b). Qed.
Lemma lem286634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286635 (b : Prop) : (term26 b) = (term27 b).
Proof. exact (MK_COMB (@lem286634) (@lem286633 b)). Qed.
Lemma lem286637 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem286638 (b : Prop) : (b -> False) = (~ b).
Proof. exact (@lem286637 b). Qed.
Lemma lem286639 (b : Prop) : (term24 b) = (term28 b).
Proof. exact (MK_COMB (@lem286635 b) (@lem286638 b)). Qed.
Lemma lem286641 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem286642 (b : Prop) : (term28 b) = True.
Proof. exact (@lem286641 (~ b)). Qed.
Lemma lem286643 (b : Prop) : (term24 b) = True.
Proof. exact (TRANS (@lem286639 b) (@lem286642 b)). Qed.
Lemma lem286644 (b : Prop) : True = (term24 b).
Proof. exact (SYM (@lem286643 b)). Qed.
Lemma lem286645 (b : Prop) : term24 b.
Proof. exact (EQ_MP (@lem286644 b) (@lem0)). Qed.
Lemma lem286646 (b : Prop) (c : Prop) (h1 : c = False) : term16 b c.
Proof. exact (EQ_MP (@lem286607 b c h1) (@lem286645 b)). Qed.
Lemma lem286647 (b : Prop) (c : Prop) (h1 : c = True) : term16 b c.
Proof. exact (EQ_MP (@lem286594 b c h1) (@lem286626 b)). Qed.
Lemma lem286649 (b : Prop) (c : Prop) : term16 b c.
Proof. exact (or_elim (@lem286569 c) (fun h0 : c = True => @lem286647 b c h0) (fun h0 : c = False => @lem286646 b c h0)). Qed.
Lemma lem286650 (b : Prop) (c : Prop) : term5 b c.
Proof. exact (EQ_MP (@lem286566 b c) (@lem286649 b c)). Qed.
Lemma lem286654 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem286655 (c : Prop) (b : Prop) : (term29 c b) = True.
Proof. exact (@lem286654 (c = b)). Qed.
Lemma lem286656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286657 (c : Prop) (b : Prop) : (term30 c b) = (imp True).
Proof. exact (MK_COMB (@lem286656) (@lem286655 c b)). Qed.
Lemma lem286661 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem286662 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem286661 b). Qed.
Lemma lem286663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286664 (b : Prop) : (term31 b) = (imp False).
Proof. exact (MK_COMB (@lem286663) (@lem286662 b)). Qed.
Lemma lem286665 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem286666 (b : Prop) (c : Prop) : (term32 b c) = (False -> c).
Proof. exact (MK_COMB (@lem286664 b) (@lem286665 c)). Qed.
Lemma lem286668 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem286669 (c : Prop) : (False -> c) = True.
Proof. exact (@lem286668 c). Qed.
Lemma lem286670 (b : Prop) (c : Prop) : (term32 b c) = True.
Proof. exact (TRANS (@lem286666 b c) (@lem286669 c)). Qed.
Lemma lem286671 (b : Prop) (c : Prop) : (term10 b c) = (True -> True).
Proof. exact (MK_COMB (@lem286657 c b) (@lem286670 b c)). Qed.
Lemma lem286673 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem286674 : (True -> True) = True.
Proof. exact (@lem286673 True). Qed.
Lemma lem286675 (b : Prop) (c : Prop) : (term10 b c) = True.
Proof. exact (TRANS (@lem286671 b c) (@lem286674)). Qed.
Lemma lem286676 (b : Prop) (c : Prop) : True = (term10 b c).
Proof. exact (SYM (@lem286675 b c)). Qed.
Lemma lem286677 (b : Prop) (c : Prop) : term10 b c.
Proof. exact (EQ_MP (@lem286676 b c) (@lem0)). Qed.
Lemma lem286678 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : term7 a b c.
Proof. exact (EQ_MP (@lem286540 b c a h1) (@lem286677 b c)). Qed.
Lemma lem286679 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : term7 a b c.
Proof. exact (EQ_MP (@lem286527 b c a h1) (@lem286650 b c)). Qed.
Lemma lem286682 (a : Prop) (b : Prop) (c : Prop) : term7 a b c.
Proof. exact (or_elim (@lem286500 a) (fun h0 : a = True => @lem286679 b c a h0) (fun h0 : a = False => @lem286678 b c a h0)). Qed.
Lemma lem286683 (a : Prop) (b : Prop) (c : Prop) (h1 : term7 a b c) : term7 a b c.
Proof. exact (h1). Qed.
Lemma lem286684 (a : Prop) (c : Prop) (b : Prop) (h1 : term33 a c b) : term33 a c b.
Proof. exact (h1). Qed.
Lemma lem286685 (a : Prop) (b : Prop) (c : Prop) (h1 : term33 a c b) (h2 : term7 a b c) : term34 a b c.
Proof. exact (@lem286683 a b c h2 (@lem286684 a c b h1)). Qed.
Lemma lem286686 (a : Prop) (c : Prop) (b : Prop) (h1 : term33 a c b) : term35 a b c.
Proof. exact (fun h0 : term7 a b c => @lem286685 a b c h1 h0). Qed.
Lemma lem286687 (a : Prop) (b : Prop) (c : Prop) (h1 : term7 a b c) : term7 a b c.
Proof. exact (h1). Qed.
Lemma lem286688 (a : Prop) (b : Prop) (c : Prop) (h1 : term33 a c b) (h2 : term7 a b c) : term34 a b c.
Proof. exact (@lem286686 a c b h1 (@lem286687 a b c h2)). Qed.
Lemma lem286689 (a : Prop) (b : Prop) (c : Prop) (h1 : term7 a b c) : term7 a b c.
Proof. exact (fun h0 : term33 a c b => @lem286688 a b c h0 h1). Qed.
Lemma lem286690 (a : Prop) (b : Prop) (c : Prop) : term36 a b c.
Proof. exact (fun h0 : term7 a b c => @lem286689 a b c h0). Qed.
Lemma lem286693 (a : Prop) (b : Prop) (c : Prop) : term7 a b c.
Proof. exact (@lem286690 a b c (@lem286682 a b c)). Qed.
Lemma lem286694 (R : type1605) : term37 R.
Proof. exact (@lem286693 (term38 R) (term39 R) (term40 R)). Qed.
Lemma lem286695 (R : type1605) : term41 R.
Proof. exact (@lem286485 R). Qed.
Lemma lem286696 (R : type1605) : (term41 R) = (term42 R).
Proof. exact (eq_refl (term41 R)). Qed.
Lemma lem286699 (R : type1605) : term42 R.
Proof. exact (EQ_MP (@lem286696 R) (@lem286695 R)). Qed.
Lemma lem286700 (R : type1605) : term43 R.
Proof. exact (@lem286694 R (@lem286699 R)). Qed.
Lemma lem286705 : term44.
Proof. exact (fun R : type1605 => @lem286700 R). Qed.
