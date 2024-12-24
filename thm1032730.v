Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032730_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Lemma lem1032628 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem1032629 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem1032630 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem1032629 p) (@lem1032628 p)). Qed.
Lemma lem1032631 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1032632 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1032643 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem1032644 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem1032643 q) (@lem1032631 p h1)). Qed.
Lemma lem1032645 (q : Prop) : (term4 q) = (term5 q).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem1032646 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem1032647 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = (term5 q)).
Proof. exact (MK_COMB (@lem1032646 q p) (@lem1032645 q)). Qed.
Lemma lem1032648 (p : Prop) (q : Prop) : (term3 q p) = (term7 p q).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem1032649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1032650 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem1032649) (@lem1032648 p q)). Qed.
Lemma lem1032651 (q : Prop) : (term5 q) = (term5 q).
Proof. exact (eq_refl (term5 q)). Qed.
Lemma lem1032652 (p : Prop) (q : Prop) : ((term3 q p) = (term5 q)) = ((term7 p q) = (term5 q)).
Proof. exact (MK_COMB (@lem1032650 p q) (@lem1032651 q)). Qed.
Lemma lem1032653 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term7 p q) = (term5 q)).
Proof. exact (TRANS (@lem1032647 p q) (@lem1032652 p q)). Qed.
Lemma lem1032654 (q : Prop) (p : Prop) (h1 : p = True) : (term7 p q) = (term5 q).
Proof. exact (EQ_MP (@lem1032653 p q) (@lem1032644 q p h1)). Qed.
Lemma lem1032655 (q : Prop) (p : Prop) (h1 : p = True) : (term5 q) = (term7 p q).
Proof. exact (SYM (@lem1032654 q p h1)). Qed.
Lemma lem1032656 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem1032657 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term9 q).
Proof. exact (MK_COMB (@lem1032656 q) (@lem1032632 p h1)). Qed.
Lemma lem1032658 (q : Prop) : (term9 q) = (term10 q).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem1032659 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem1032660 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = ((term3 q p) = (term10 q)).
Proof. exact (MK_COMB (@lem1032659 q p) (@lem1032658 q)). Qed.
Lemma lem1032661 (p : Prop) (q : Prop) : (term3 q p) = (term7 p q).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem1032662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1032663 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem1032662) (@lem1032661 p q)). Qed.
Lemma lem1032664 (q : Prop) : (term10 q) = (term10 q).
Proof. exact (eq_refl (term10 q)). Qed.
Lemma lem1032665 (p : Prop) (q : Prop) : ((term3 q p) = (term10 q)) = ((term7 p q) = (term10 q)).
Proof. exact (MK_COMB (@lem1032663 p q) (@lem1032664 q)). Qed.
Lemma lem1032666 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = ((term7 p q) = (term10 q)).
Proof. exact (TRANS (@lem1032660 p q) (@lem1032665 p q)). Qed.
Lemma lem1032667 (q : Prop) (p : Prop) (h1 : p = False) : (term7 p q) = (term10 q).
Proof. exact (EQ_MP (@lem1032666 p q) (@lem1032657 q p h1)). Qed.
Lemma lem1032668 (q : Prop) (p : Prop) (h1 : p = False) : (term10 q) = (term7 p q).
Proof. exact (SYM (@lem1032667 q p h1)). Qed.
Lemma lem1032672 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1032673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1032674 : term11 = (imp False).
Proof. exact (MK_COMB (@lem1032673) (@lem1032672)). Qed.
Lemma lem1032680 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1032681 (q : Prop) : ((~ q) = True) = (~ q).
Proof. exact (@lem1032680 (~ q)). Qed.
Lemma lem1032682 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1032683 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (MK_COMB (@lem1032682) (@lem1032681 q)). Qed.
Lemma lem1032684 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1032685 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem1032683 q) (@lem1032684 q)). Qed.
Lemma lem1032688 (q : Prop) : (term5 q) = (term16 q).
Proof. exact (MK_COMB (@lem1032674) (@lem1032685 q)). Qed.
Lemma lem1032690 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1032691 (q : Prop) : (term16 q) = True.
Proof. exact (@lem1032690 (term15 q)). Qed.
Lemma lem1032692 (q : Prop) : (term5 q) = True.
Proof. exact (TRANS (@lem1032688 q) (@lem1032691 q)). Qed.
Lemma lem1032693 (q : Prop) : True = (term5 q).
Proof. exact (SYM (@lem1032692 q)). Qed.
Lemma lem1032694 (q : Prop) : term5 q.
Proof. exact (EQ_MP (@lem1032693 q) (@lem0)). Qed.
Lemma lem1032698 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1032699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1032700 : term17 = (imp True).
Proof. exact (MK_COMB (@lem1032699) (@lem1032698)). Qed.
Lemma lem1032706 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1032707 (q : Prop) : ((~ q) = False) = (term18 q).
Proof. exact (@lem1032706 (~ q)). Qed.
Lemma lem1032709 (t : Prop) : (term18 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1032710 (q : Prop) : (term18 q) = q.
Proof. exact (@lem1032709 q). Qed.
Lemma lem1032711 (q : Prop) : ((~ q) = False) = q.
Proof. exact (TRANS (@lem1032707 q) (@lem1032710 q)). Qed.
Lemma lem1032712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1032713 (q : Prop) : (term19 q) = (imp q).
Proof. exact (MK_COMB (@lem1032712) (@lem1032711 q)). Qed.
Lemma lem1032714 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1032715 (q : Prop) : (term20 q) = (q -> q).
Proof. exact (MK_COMB (@lem1032713 q) (@lem1032714 q)). Qed.
Lemma lem1032717 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1032718 (q : Prop) : (q -> q) = True.
Proof. exact (@lem1032717 q). Qed.
Lemma lem1032719 (q : Prop) : (term20 q) = True.
Proof. exact (TRANS (@lem1032715 q) (@lem1032718 q)). Qed.
Lemma lem1032720 (q : Prop) : (term10 q) = (True -> True).
Proof. exact (MK_COMB (@lem1032700) (@lem1032719 q)). Qed.
Lemma lem1032722 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1032723 : (True -> True) = True.
Proof. exact (@lem1032722 True). Qed.
Lemma lem1032724 (q : Prop) : (term10 q) = True.
Proof. exact (TRANS (@lem1032720 q) (@lem1032723)). Qed.
Lemma lem1032725 (q : Prop) : True = (term10 q).
Proof. exact (SYM (@lem1032724 q)). Qed.
Lemma lem1032726 (q : Prop) : term10 q.
Proof. exact (EQ_MP (@lem1032725 q) (@lem0)). Qed.
Lemma lem1032727 (q : Prop) (p : Prop) (h1 : p = False) : term7 p q.
Proof. exact (EQ_MP (@lem1032668 q p h1) (@lem1032726 q)). Qed.
Lemma lem1032728 (q : Prop) (p : Prop) (h1 : p = True) : term7 p q.
Proof. exact (EQ_MP (@lem1032655 q p h1) (@lem1032694 q)). Qed.
Lemma lem1032730 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (or_elim (@lem1032630 p) (fun h0 : p = True => @lem1032728 q p h0) (fun h0 : p = False => @lem1032727 q p h0)). Qed.
