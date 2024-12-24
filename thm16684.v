Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16684_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Lemma lem16604 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem16605 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem16606 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem16605 a) (@lem16604 a)). Qed.
Lemma lem16607 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem16608 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem16615 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16616 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem16615 b) (@lem16607 a h1)). Qed.
Lemma lem16617 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem16618 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16619 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem16618 b a) (@lem16617 b)). Qed.
Lemma lem16620 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16622 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16621) (@lem16620 a b)). Qed.
Lemma lem16623 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem16624 (a : Prop) (b : Prop) : ((term3 b a) = (term5 b)) = ((term7 a b) = (term5 b)).
Proof. exact (MK_COMB (@lem16622 a b) (@lem16623 b)). Qed.
Lemma lem16625 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term7 a b) = (term5 b)).
Proof. exact (TRANS (@lem16619 a b) (@lem16624 a b)). Qed.
Lemma lem16626 (b : Prop) (a : Prop) (h1 : a = True) : (term7 a b) = (term5 b).
Proof. exact (EQ_MP (@lem16625 a b) (@lem16616 b a h1)). Qed.
Lemma lem16627 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b) = (term7 a b).
Proof. exact (SYM (@lem16626 b a h1)). Qed.
Lemma lem16628 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16629 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem16628 b) (@lem16608 a h1)). Qed.
Lemma lem16630 (b : Prop) : (term9 b) = (term10 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem16631 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16632 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem16631 b a) (@lem16630 b)). Qed.
Lemma lem16633 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16635 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16634) (@lem16633 a b)). Qed.
Lemma lem16636 (b : Prop) : (term10 b) = (term10 b).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem16637 (a : Prop) (b : Prop) : ((term3 b a) = (term10 b)) = ((term7 a b) = (term10 b)).
Proof. exact (MK_COMB (@lem16635 a b) (@lem16636 b)). Qed.
Lemma lem16638 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term7 a b) = (term10 b)).
Proof. exact (TRANS (@lem16632 a b) (@lem16637 a b)). Qed.
Lemma lem16639 (b : Prop) (a : Prop) (h1 : a = False) : (term7 a b) = (term10 b).
Proof. exact (EQ_MP (@lem16638 a b) (@lem16629 b a h1)). Qed.
Lemma lem16640 (b : Prop) (a : Prop) (h1 : a = False) : (term10 b) = (term7 a b).
Proof. exact (SYM (@lem16639 b a h1)). Qed.
Lemma lem16644 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem16645 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem16644 b). Qed.
Lemma lem16646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16647 (b : Prop) : (term11 b) = (~ True).
Proof. exact (MK_COMB (@lem16646) (@lem16645 b)). Qed.
Lemma lem16649 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16650 (b : Prop) : (term11 b) = False.
Proof. exact (TRANS (@lem16647 b) (@lem16649)). Qed.
Lemma lem16651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16652 (b : Prop) : (term12 b) = (imp False).
Proof. exact (MK_COMB (@lem16651) (@lem16650 b)). Qed.
Lemma lem16653 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem16654 (b : Prop) : (term5 b) = (term13 b).
Proof. exact (MK_COMB (@lem16652 b) (@lem16653 b)). Qed.
Lemma lem16656 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem16657 (b : Prop) : (term13 b) = True.
Proof. exact (@lem16656 (~ b)). Qed.
Lemma lem16658 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem16654 b) (@lem16657 b)). Qed.
Lemma lem16659 (b : Prop) : True = (term5 b).
Proof. exact (SYM (@lem16658 b)). Qed.
Lemma lem16660 (b : Prop) : term5 b.
Proof. exact (EQ_MP (@lem16659 b) (@lem0)). Qed.
Lemma lem16664 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem16665 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem16664 b). Qed.
Lemma lem16666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16667 (b : Prop) : (term14 b) = (~ b).
Proof. exact (MK_COMB (@lem16666) (@lem16665 b)). Qed.
Lemma lem16668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16669 (b : Prop) : (term15 b) = (term16 b).
Proof. exact (MK_COMB (@lem16668) (@lem16667 b)). Qed.
Lemma lem16670 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem16671 (b : Prop) : (term10 b) = (term17 b).
Proof. exact (MK_COMB (@lem16669 b) (@lem16670 b)). Qed.
Lemma lem16673 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem16674 (b : Prop) : (term17 b) = True.
Proof. exact (@lem16673 (~ b)). Qed.
Lemma lem16675 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem16671 b) (@lem16674 b)). Qed.
Lemma lem16676 (b : Prop) : True = (term10 b).
Proof. exact (SYM (@lem16675 b)). Qed.
Lemma lem16677 (b : Prop) : term10 b.
Proof. exact (EQ_MP (@lem16676 b) (@lem0)). Qed.
Lemma lem16678 (b : Prop) (a : Prop) (h1 : a = False) : term7 a b.
Proof. exact (EQ_MP (@lem16640 b a h1) (@lem16677 b)). Qed.
Lemma lem16679 (b : Prop) (a : Prop) (h1 : a = True) : term7 a b.
Proof. exact (EQ_MP (@lem16627 b a h1) (@lem16660 b)). Qed.
Lemma lem16682 (a : Prop) (b : Prop) : term7 a b.
Proof. exact (or_elim (@lem16606 a) (fun h0 : a = True => @lem16679 b a h0) (fun h0 : a = False => @lem16678 b a h0)). Qed.
Lemma lem16683 (a : Prop) (b : Prop) (h1 : term18 a b) : term18 a b.
Proof. exact (h1). Qed.
Lemma lem16684 (a : Prop) (b : Prop) (h1 : term18 a b) : ~ b.
Proof. exact (@lem16682 a b (@lem16683 a b h1)). Qed.
