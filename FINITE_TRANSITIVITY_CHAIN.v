Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_TRANSITIVITY_CHAIN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3735654 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3735655 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3735656 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3735655 t1) (@lem3735654 t1)). Qed.
Lemma lem3735657 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3735656 t1 t2). Qed.
Lemma lem3735658 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3735659 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3735658 t1 t2) (@lem3735657 t1 t2)). Qed.
Lemma lem3735660 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3735659 t1 t2 t3). Qed.
Lemma lem3735661 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3735662 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3735661 t1 t2 t3) (@lem3735660 t1 t2 t3)). Qed.
Lemma lem3735663 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3735662 t1 t2 t3)). Qed.
Lemma lem3735664 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3735665 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem3735666 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem3735665 A x) (@lem3735664 A x)). Qed.
Lemma lem3735667 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3735669 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3735670 {A : Type'} (P : type686 A) (h1 : term10 A) : term11 A P.
Proof. exact (@lem3735669 A h1 P). Qed.
Lemma lem3735671 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem3735672 {A : Type'} (P : type686 A) (h1 : term10 A) : term12 A P.
Proof. exact (EQ_MP (@lem3735671 A P) (@lem3735670 A P h1)). Qed.
Lemma lem3735673 {A : Type'} (P : type686 A) (h1 : term13 A P) : term13 A P.
Proof. exact (h1). Qed.
Lemma lem3735674 {A : Type'} (P : type686 A) (h1 : term10 A) (h2 : term13 A P) : term14 A P.
Proof. exact (@lem3735672 A P h1 (@lem3735673 A P h2)). Qed.
Lemma lem3735675 {A : Type'} (P : type686 A) (h1 : term13 A P) : term15 A P.
Proof. exact (fun h0 : term10 A => @lem3735674 A P h0 h1). Qed.
Lemma lem3735676 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3735677 {A : Type'} (P : type686 A) (h1 : term10 A) (h2 : term13 A P) : term14 A P.
Proof. exact (@lem3735675 A P h2 (@lem3735676 A h1)). Qed.
Lemma lem3735678 {A : Type'} (P : type686 A) (h1 : term10 A) : term12 A P.
Proof. exact (fun h0 : term13 A P => @lem3735677 A P h1 h0). Qed.
Lemma lem3735679 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (fun P : type686 A => @lem3735678 A P h1). Qed.
Lemma lem3735680 {A : Type'} : term16 A.
Proof. exact (fun h0 : term10 A => @lem3735679 A h0). Qed.
Lemma lem3735681 {A : Type'} : term10 A.
Proof. exact (@lem3735680 A (@lem3558722 A)). Qed.
Lemma lem3735682 {A : Type'} (P : type686 A) : term11 A P.
Proof. exact (@lem3735681 A P). Qed.
Lemma lem3735683 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem3735690 (p : Prop) (q : Prop) (r : Prop) : (term17 p q r) = (term18 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3735691 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term19 A R s) = (term20 A R s).
Proof. exact (@lem3735690 (@FINITE A s) (term21 A s R) (s = (@EMPTY A))). Qed.
Lemma lem3735692 {A : Type'} (R : type1402 A) : (term22 A R) = (term23 A R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3735691 A R s)). Qed.
Lemma lem3735693 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3735694 {A : Type'} (R : type1402 A) : (term24 A R) = (term25 A R).
Proof. exact (MK_COMB (@lem3735693 A) (@lem3735692 A R)). Qed.
Lemma lem3735695 {A : Type'} (R : type1402 A) : (term25 A R) = (term24 A R).
Proof. exact (SYM (@lem3735694 A R)). Qed.
Lemma lem3735697 {A : Type'} (P : type686 A) : term12 A P.
Proof. exact (EQ_MP (@lem3735683 A P) (@lem3735682 A P)). Qed.
Lemma lem3735698 {A : Type'} (P : type686 A) : term12 A P.
Proof. exact (@lem3735697 A P). Qed.
Lemma lem3735699 {A : Type'} (R : type1402 A) : term26 A R.
Proof. exact (@lem3735698 A (term27 A R)). Qed.
Lemma lem3735700 {A : Type'} (R : type1402 A) : (term28 A R) = (term29 A R).
Proof. exact (eq_refl (term28 A R)). Qed.
Lemma lem3735701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3735702 {A : Type'} (R : type1402 A) : (term30 A R) = (term31 A R).
Proof. exact (MK_COMB (@lem3735701) (@lem3735700 A R)). Qed.
Lemma lem3735703 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term32 A R s) = (term33 A R s).
Proof. exact (eq_refl (term32 A R s)). Qed.
Lemma lem3735704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3735705 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term34 A R s) = (term35 A R s).
Proof. exact (MK_COMB (@lem3735704) (@lem3735703 A R s)). Qed.
Lemma lem3735706 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term36 A x s).
Proof. exact (eq_refl (term36 A x s)). Qed.
Lemma lem3735707 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term37 A R x s) = (term38 A R x s).
Proof. exact (MK_COMB (@lem3735705 A R s) (@lem3735706 A x s)). Qed.
Lemma lem3735708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735709 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term39 A R x s) = (term40 A R x s).
Proof. exact (MK_COMB (@lem3735708) (@lem3735707 A R x s)). Qed.
Lemma lem3735710 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term41 A R x s) = (term42 A R x s).
Proof. exact (eq_refl (term41 A R x s)). Qed.
Lemma lem3735711 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term43 A R x s) = (term44 A R x s).
Proof. exact (MK_COMB (@lem3735709 A R x s) (@lem3735710 A R x s)). Qed.
Lemma lem3735712 {A : Type'} (R : type1402 A) (x : A) : (term45 A R x) = (term46 A R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3735711 A R x s)). Qed.
Lemma lem3735713 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3735714 {A : Type'} (R : type1402 A) (x : A) : (term47 A R x) = (term48 A R x).
Proof. exact (MK_COMB (@lem3735713 A) (@lem3735712 A R x)). Qed.
Lemma lem3735715 {A : Type'} (R : type1402 A) : (term49 A R) = (term50 A R).
Proof. exact (fun_ext (fun x : A => @lem3735714 A R x)). Qed.
Lemma lem3735716 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3735717 {A : Type'} (R : type1402 A) : (term51 A R) = (term52 A R).
Proof. exact (MK_COMB (@lem3735716 A) (@lem3735715 A R)). Qed.
Lemma lem3735718 {A : Type'} (R : type1402 A) : (term53 A R) = (term54 A R).
Proof. exact (MK_COMB (@lem3735702 A R) (@lem3735717 A R)). Qed.
Lemma lem3735719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735720 {A : Type'} (R : type1402 A) : (term55 A R) = (term56 A R).
Proof. exact (MK_COMB (@lem3735719) (@lem3735718 A R)). Qed.
Lemma lem3735721 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term32 A R s) = (term33 A R s).
Proof. exact (eq_refl (term32 A R s)). Qed.
Lemma lem3735722 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem3735723 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term58 A R s) = (term20 A R s).
Proof. exact (MK_COMB (@lem3735722 A s) (@lem3735721 A R s)). Qed.
Lemma lem3735724 {A : Type'} (R : type1402 A) : (term59 A R) = (term23 A R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3735723 A R s)). Qed.
Lemma lem3735725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3735726 {A : Type'} (R : type1402 A) : (term60 A R) = (term25 A R).
Proof. exact (MK_COMB (@lem3735725 A) (@lem3735724 A R)). Qed.
Lemma lem3735727 {A : Type'} (R : type1402 A) : (term26 A R) = (term61 A R).
Proof. exact (MK_COMB (@lem3735720 A R) (@lem3735726 A R)). Qed.
Lemma lem3735728 {A : Type'} (R : type1402 A) : term61 A R.
Proof. exact (EQ_MP (@lem3735727 A R) (@lem3735699 A R)). Qed.
Lemma lem3735764 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3735667 A x (@lem3735666 A x)). Qed.
Lemma lem3735765 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3735764 A x). Qed.
Lemma lem3735766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735767 {A : Type'} (x : A) : (term62 A x) = (imp False).
Proof. exact (MK_COMB (@lem3735766) (@lem3735765 A x)). Qed.
Lemma lem3735775 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3735667 A x (@lem3735666 A x)). Qed.
Lemma lem3735776 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3735775 A x). Qed.
Lemma lem3735777 {A : Type'} (y : A) : (@IN A y (@EMPTY A)) = False.
Proof. exact (@lem3735776 A y). Qed.
Lemma lem3735778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3735779 {A : Type'} (y : A) : (term63 A y) = (and False).
Proof. exact (MK_COMB (@lem3735778) (@lem3735777 A y)). Qed.
Lemma lem3735780 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem3735781 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term64 A R x y) = (term65 A R x y).
Proof. exact (MK_COMB (@lem3735779 A y) (@lem3735780 A R x y)). Qed.
Lemma lem3735783 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3735784 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term65 A R x y) = False.
Proof. exact (@lem3735783 (R x y)). Qed.
Lemma lem3735785 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term64 A R x y) = False.
Proof. exact (TRANS (@lem3735781 A R x y) (@lem3735784 A R x y)). Qed.
Lemma lem3735786 {A : Type'} (R : type1402 A) (x : A) : (term66 A R x) = (term67 A).
Proof. exact (fun_ext (fun y : A => @lem3735785 A R x y)). Qed.
Lemma lem3735787 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3735788 {A : Type'} (R : type1402 A) (x : A) : (term68 A R x) = (term69 A).
Proof. exact (MK_COMB (@lem3735787 A) (@lem3735786 A R x)). Qed.
Lemma lem3735790 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3735791 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (@lem3735790 A t). Qed.
Lemma lem3735792 {A : Type'} : (term69 A) = False.
Proof. exact (@lem3735791 A False). Qed.
Lemma lem3735793 {A : Type'} (R : type1402 A) (x : A) : (term68 A R x) = False.
Proof. exact (TRANS (@lem3735788 A R x) (@lem3735792 A)). Qed.
Lemma lem3735794 {A : Type'} (R : type1402 A) (x : A) : (term71 A R x) = (False -> False).
Proof. exact (MK_COMB (@lem3735767 A x) (@lem3735793 A R x)). Qed.
Lemma lem3735796 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3735797 : (False -> False) = True.
Proof. exact (@lem3735796 False). Qed.
Lemma lem3735798 {A : Type'} (R : type1402 A) (x : A) : (term71 A R x) = True.
Proof. exact (TRANS (@lem3735794 A R x) (@lem3735797)). Qed.
Lemma lem3735799 {A : Type'} (R : type1402 A) : (term72 A R) = (term73 A).
Proof. exact (fun_ext (fun x : A => @lem3735798 A R x)). Qed.
Lemma lem3735800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3735801 {A : Type'} (R : type1402 A) : (term74 A R) = (term75 A).
Proof. exact (MK_COMB (@lem3735800 A) (@lem3735799 A R)). Qed.
Lemma lem3735803 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3735804 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (@lem3735803 A t). Qed.
Lemma lem3735805 {A : Type'} : (term75 A) = True.
Proof. exact (@lem3735804 A True). Qed.
Lemma lem3735806 {A : Type'} (R : type1402 A) : (term74 A R) = True.
Proof. exact (TRANS (@lem3735801 A R) (@lem3735805 A)). Qed.
Lemma lem3735807 {A : Type'} (R : type1402 A) : (term77 A R) = (term77 A R).
Proof. exact (eq_refl (term77 A R)). Qed.
Lemma lem3735808 {A : Type'} (R : type1402 A) : (term78 A R) = (term79 A R).
Proof. exact (MK_COMB (@lem3735807 A R) (@lem3735806 A R)). Qed.
Lemma lem3735810 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3735811 {A : Type'} (R : type1402 A) : (term79 A R) = (term80 A R).
Proof. exact (@lem3735810 (term80 A R)). Qed.
Lemma lem3735828 {A : Type'} (R : type1402 A) : (term78 A R) = (term80 A R).
Proof. exact (TRANS (@lem3735808 A R) (@lem3735811 A R)). Qed.
Lemma lem3735829 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3735830 {A : Type'} (R : type1402 A) : (term82 A R) = (term83 A R).
Proof. exact (MK_COMB (@lem3735829 A R) (@lem3735828 A R)). Qed.
Lemma lem3735833 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735834 {A : Type'} (R : type1402 A) : (term84 A R) = (term85 A R).
Proof. exact (MK_COMB (@lem3735833) (@lem3735830 A R)). Qed.
Lemma lem3735836 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3735837 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3735836 (A -> Prop) x). Qed.
Lemma lem3735838 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3735837 A (@EMPTY A)). Qed.
Lemma lem3735839 {A : Type'} (R : type1402 A) : (term29 A R) = (term86 A R).
Proof. exact (MK_COMB (@lem3735834 A R) (@lem3735838 A)). Qed.
Lemma lem3735841 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3735842 {A : Type'} (R : type1402 A) : (term86 A R) = True.
Proof. exact (@lem3735841 (term83 A R)). Qed.
Lemma lem3735843 {A : Type'} (R : type1402 A) : (term29 A R) = True.
Proof. exact (TRANS (@lem3735839 A R) (@lem3735842 A R)). Qed.
Lemma lem3735844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3735845 {A : Type'} (R : type1402 A) : (term31 A R) = (and True).
Proof. exact (MK_COMB (@lem3735844) (@lem3735843 A R)). Qed.
Lemma lem3735940 {A : Type'} (R : type1402 A) : (term52 A R) = (term52 A R).
Proof. exact (eq_refl (term52 A R)). Qed.
Lemma lem3735941 {A : Type'} (R : type1402 A) : (term54 A R) = (term87 A R).
Proof. exact (MK_COMB (@lem3735845 A R) (@lem3735940 A R)). Qed.
Lemma lem3735943 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3735944 {A : Type'} (R : type1402 A) : (term87 A R) = (term52 A R).
Proof. exact (@lem3735943 (term52 A R)). Qed.
Lemma lem3736039 {A : Type'} (R : type1402 A) : (term54 A R) = (term52 A R).
Proof. exact (TRANS (@lem3735941 A R) (@lem3735944 A R)). Qed.
Lemma lem3736040 {A : Type'} (R : type1402 A) : (term52 A R) = (term54 A R).
Proof. exact (SYM (@lem3736039 A R)). Qed.
Lemma lem3736094 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term88 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3736095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term88 A s t).
Proof. exact (@lem3736094 A s t). Qed.
Lemma lem3736096 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term89 A s).
Proof. exact (@lem3736095 A s (@EMPTY A)). Qed.
Lemma lem3736105 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term90 A s R) = (term90 A s R).
Proof. exact (eq_refl (term90 A s R)). Qed.
Lemma lem3736106 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term33 A R s) = (term91 A R s).
Proof. exact (MK_COMB (@lem3736105 A s R) (@lem3736096 A s)). Qed.
Lemma lem3736109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736110 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term35 A R s) = (term92 A R s).
Proof. exact (MK_COMB (@lem3736109) (@lem3736106 A R s)). Qed.
Lemma lem3736113 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term36 A x s).
Proof. exact (eq_refl (term36 A x s)). Qed.
Lemma lem3736114 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term38 A R x s) = (term93 A R x s).
Proof. exact (MK_COMB (@lem3736110 A R s) (@lem3736113 A x s)). Qed.
Lemma lem3736117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736118 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term40 A R x s) = (term94 A R x s).
Proof. exact (MK_COMB (@lem3736117) (@lem3736114 A R x s)). Qed.
Lemma lem3736160 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term88 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3736161 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term88 A s t).
Proof. exact (@lem3736160 A s t). Qed.
Lemma lem3736162 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = (term95 A x s).
Proof. exact (@lem3736161 A (@INSERT A x s) (@EMPTY A)). Qed.
Lemma lem3736171 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term96 A x s R) = (term96 A x s R).
Proof. exact (eq_refl (term96 A x s R)). Qed.
Lemma lem3736172 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term42 A R x s) = (term97 A R x s).
Proof. exact (MK_COMB (@lem3736171 A x s R) (@lem3736162 A x s)). Qed.
Lemma lem3736175 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term44 A R x s) = (term98 A R x s).
Proof. exact (MK_COMB (@lem3736118 A R x s) (@lem3736172 A R x s)). Qed.
Lemma lem3736178 {A : Type'} (R : type1402 A) (x : A) : (term46 A R x) = (term99 A R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3736175 A R x s)). Qed.
Lemma lem3736179 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3736180 {A : Type'} (R : type1402 A) (x : A) : (term48 A R x) = (term100 A R x).
Proof. exact (MK_COMB (@lem3736179 A) (@lem3736178 A R x)). Qed.
Lemma lem3736185 {A : Type'} (R : type1402 A) : (term50 A R) = (term101 A R).
Proof. exact (fun_ext (fun x : A => @lem3736180 A R x)). Qed.
Lemma lem3736186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736187 {A : Type'} (R : type1402 A) : (term52 A R) = (term102 A R).
Proof. exact (MK_COMB (@lem3736186 A) (@lem3736185 A R)). Qed.
Lemma lem3736192 {A : Type'} (R : type1402 A) : (term102 A R) = (term52 A R).
Proof. exact (SYM (@lem3736187 A R)). Qed.
Lemma lem3736238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736239 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736238 A P x). Qed.
Lemma lem3736240 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3736239 A s x). Qed.
Lemma lem3736241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736242 {A : Type'} (s : A -> Prop) (x : A) : (term103 A x s) = (term104 A s x).
Proof. exact (MK_COMB (@lem3736241) (@lem3736240 A s x)). Qed.
Lemma lem3736250 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736251 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736250 A P x). Qed.
Lemma lem3736252 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem3736251 A s y). Qed.
Lemma lem3736253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736254 {A : Type'} (s : A -> Prop) (y : A) : (term105 A y s) = (term106 A s y).
Proof. exact (MK_COMB (@lem3736253) (@lem3736252 A s y)). Qed.
Lemma lem3736255 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem3736256 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term107 A s R x y) = (term108 A s R x y).
Proof. exact (MK_COMB (@lem3736254 A s y) (@lem3736255 A R x y)). Qed.
Lemma lem3736259 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term109 A s R x) = (term110 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3736256 A s R x y)). Qed.
Lemma lem3736260 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3736261 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term111 A s R x) = (term112 A s R x).
Proof. exact (MK_COMB (@lem3736260 A) (@lem3736259 A s R x)). Qed.
Lemma lem3736266 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term113 A s R x) = (term114 A s R x).
Proof. exact (MK_COMB (@lem3736242 A s x) (@lem3736261 A s R x)). Qed.
Lemma lem3736269 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term115 A s R) = (term116 A s R).
Proof. exact (fun_ext (fun x : A => @lem3736266 A s R x)). Qed.
Lemma lem3736270 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736271 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term117 A s R) = (term118 A s R).
Proof. exact (MK_COMB (@lem3736270 A) (@lem3736269 A s R)). Qed.
Lemma lem3736276 {A : Type'} (R : type1402 A) : (term77 A R) = (term77 A R).
Proof. exact (eq_refl (term77 A R)). Qed.
Lemma lem3736277 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term119 A s R) = (term120 A s R).
Proof. exact (MK_COMB (@lem3736276 A R) (@lem3736271 A s R)). Qed.
Lemma lem3736280 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3736281 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term21 A s R) = (term121 A s R).
Proof. exact (MK_COMB (@lem3736280 A R) (@lem3736277 A s R)). Qed.
Lemma lem3736284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736285 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term90 A s R) = (term122 A s R).
Proof. exact (MK_COMB (@lem3736284) (@lem3736281 A s R)). Qed.
Lemma lem3736293 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736294 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736293 A P x). Qed.
Lemma lem3736295 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3736294 A s x). Qed.
Lemma lem3736296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3736297 {A : Type'} (s : A -> Prop) (x : A) : (term123 A x s) = (term124 A s x).
Proof. exact (MK_COMB (@lem3736296) (@lem3736295 A s x)). Qed.
Lemma lem3736299 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3736300 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3736299 A x). Qed.
Lemma lem3736301 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3736297 A s x) (@lem3736300 A x)). Qed.
Lemma lem3736303 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3736304 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term125 A s x).
Proof. exact (@lem3736303 (s x)). Qed.
Lemma lem3736305 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term125 A s x).
Proof. exact (TRANS (@lem3736301 A s x) (@lem3736304 A s x)). Qed.
Lemma lem3736306 {A : Type'} (s : A -> Prop) : (term126 A s) = (term127 A s).
Proof. exact (fun_ext (fun x : A => @lem3736305 A s x)). Qed.
Lemma lem3736307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736308 {A : Type'} (s : A -> Prop) : (term89 A s) = (term128 A s).
Proof. exact (MK_COMB (@lem3736307 A) (@lem3736306 A s)). Qed.
Lemma lem3736313 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term91 A R s) = (term129 A R s).
Proof. exact (MK_COMB (@lem3736285 A s R) (@lem3736308 A s)). Qed.
Lemma lem3736316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736317 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term92 A R s) = (term130 A R s).
Proof. exact (MK_COMB (@lem3736316) (@lem3736313 A R s)). Qed.
Lemma lem3736321 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736322 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736321 A P x). Qed.
Lemma lem3736323 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3736322 A s x). Qed.
Lemma lem3736324 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3736325 {A : Type'} (s : A -> Prop) (x : A) : (term131 A x s) = (term125 A s x).
Proof. exact (MK_COMB (@lem3736324) (@lem3736323 A s x)). Qed.
Lemma lem3736326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736327 {A : Type'} (s : A -> Prop) (x : A) : (term132 A x s) = (term133 A s x).
Proof. exact (MK_COMB (@lem3736326) (@lem3736325 A s x)). Qed.
Lemma lem3736328 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3736329 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term134 A x s).
Proof. exact (MK_COMB (@lem3736327 A s x) (@lem3736328 A s)). Qed.
Lemma lem3736332 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term93 A R x s) = (term135 A R x s).
Proof. exact (MK_COMB (@lem3736317 A R s) (@lem3736329 A x s)). Qed.
Lemma lem3736335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736336 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term94 A R x s) = (term136 A R x s).
Proof. exact (MK_COMB (@lem3736335) (@lem3736332 A R x s)). Qed.
Lemma lem3736370 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3736371 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (@lem3736370 A y x s). Qed.
Lemma lem3736372 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term137 A x' x s) = (term138 A x x' s).
Proof. exact (@lem3736371 A x x' s). Qed.
Lemma lem3736378 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736379 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736378 A P x). Qed.
Lemma lem3736380 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3736379 A s x'). Qed.
Lemma lem3736381 {A : Type'} (x' : A) (x : A) : (term139 A x' x) = (term139 A x' x).
Proof. exact (eq_refl (term139 A x' x)). Qed.
Lemma lem3736382 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term138 A x x' s) = (term140 A x s x').
Proof. exact (MK_COMB (@lem3736381 A x' x) (@lem3736380 A s x')). Qed.
Lemma lem3736385 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term137 A x' x s) = (term140 A x s x').
Proof. exact (TRANS (@lem3736372 A x x' s) (@lem3736382 A x s x')). Qed.
Lemma lem3736386 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736387 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term141 A x' x s) = (term142 A x s x').
Proof. exact (MK_COMB (@lem3736386) (@lem3736385 A x s x')). Qed.
Lemma lem3736395 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3736396 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (@lem3736395 A y x s). Qed.
Lemma lem3736397 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term137 A y x s) = (term138 A x y s).
Proof. exact (@lem3736396 A x y s). Qed.
Lemma lem3736403 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736404 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736403 A P x). Qed.
Lemma lem3736405 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem3736404 A s y). Qed.
Lemma lem3736406 {A : Type'} (y : A) (x : A) : (term139 A y x) = (term139 A y x).
Proof. exact (eq_refl (term139 A y x)). Qed.
Lemma lem3736407 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term138 A x y s) = (term140 A x s y).
Proof. exact (MK_COMB (@lem3736406 A y x) (@lem3736405 A s y)). Qed.
Lemma lem3736410 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term137 A y x s) = (term140 A x s y).
Proof. exact (TRANS (@lem3736397 A x y s) (@lem3736407 A x s y)). Qed.
Lemma lem3736411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736412 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term143 A y x s) = (term144 A x s y).
Proof. exact (MK_COMB (@lem3736411) (@lem3736410 A x s y)). Qed.
Lemma lem3736413 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (R x' y) = (R x' y).
Proof. exact (eq_refl (R x' y)). Qed.
Lemma lem3736414 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term145 A x s R x' y) = (term146 A x s R x' y).
Proof. exact (MK_COMB (@lem3736412 A x s y) (@lem3736413 A R x' y)). Qed.
Lemma lem3736417 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term147 A x s R x') = (term148 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3736414 A x s R x' y)). Qed.
Lemma lem3736418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3736419 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term149 A x s R x') = (term150 A x s R x').
Proof. exact (MK_COMB (@lem3736418 A) (@lem3736417 A x s R x')). Qed.
Lemma lem3736424 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term151 A x s R x') = (term152 A x s R x').
Proof. exact (MK_COMB (@lem3736387 A x s x') (@lem3736419 A x s R x')). Qed.
Lemma lem3736427 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term153 A x s R) = (term154 A x s R).
Proof. exact (fun_ext (fun x' : A => @lem3736424 A x s R x')). Qed.
Lemma lem3736428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736429 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term155 A x s R) = (term156 A x s R).
Proof. exact (MK_COMB (@lem3736428 A) (@lem3736427 A x s R)). Qed.
Lemma lem3736434 {A : Type'} (R : type1402 A) : (term77 A R) = (term77 A R).
Proof. exact (eq_refl (term77 A R)). Qed.
Lemma lem3736435 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term157 A x s R) = (term158 A x s R).
Proof. exact (MK_COMB (@lem3736434 A R) (@lem3736429 A x s R)). Qed.
Lemma lem3736438 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3736439 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term159 A x s R) = (term160 A x s R).
Proof. exact (MK_COMB (@lem3736438 A R) (@lem3736435 A x s R)). Qed.
Lemma lem3736442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736443 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term96 A x s R) = (term161 A x s R).
Proof. exact (MK_COMB (@lem3736442) (@lem3736439 A x s R)). Qed.
Lemma lem3736451 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3736452 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term137 A x y s) = (term138 A y x s).
Proof. exact (@lem3736451 A y x s). Qed.
Lemma lem3736453 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term137 A x' x s) = (term138 A x x' s).
Proof. exact (@lem3736452 A x x' s). Qed.
Lemma lem3736459 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3736460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3736459 A P x). Qed.
Lemma lem3736461 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3736460 A s x'). Qed.
Lemma lem3736462 {A : Type'} (x' : A) (x : A) : (term139 A x' x) = (term139 A x' x).
Proof. exact (eq_refl (term139 A x' x)). Qed.
Lemma lem3736463 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term138 A x x' s) = (term140 A x s x').
Proof. exact (MK_COMB (@lem3736462 A x' x) (@lem3736461 A s x')). Qed.
Lemma lem3736466 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term137 A x' x s) = (term140 A x s x').
Proof. exact (TRANS (@lem3736453 A x x' s) (@lem3736463 A x s x')). Qed.
Lemma lem3736467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3736468 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term162 A x' x s) = (term163 A x s x').
Proof. exact (MK_COMB (@lem3736467) (@lem3736466 A x s x')). Qed.
Lemma lem3736470 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3736471 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3736470 A x). Qed.
Lemma lem3736472 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3736471 A x'). Qed.
Lemma lem3736473 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term137 A x' x s) = (@IN A x' (@EMPTY A))) = ((term140 A x s x') = False).
Proof. exact (MK_COMB (@lem3736468 A x s x') (@lem3736472 A x')). Qed.
Lemma lem3736475 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3736476 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term140 A x s x') = False) = (term164 A x s x').
Proof. exact (@lem3736475 (term140 A x s x')). Qed.
Lemma lem3736481 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term137 A x' x s) = (@IN A x' (@EMPTY A))) = (term164 A x s x').
Proof. exact (TRANS (@lem3736473 A x s x') (@lem3736476 A x s x')). Qed.
Lemma lem3736482 {A : Type'} (x : A) (s : A -> Prop) : (term165 A x s) = (term166 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3736481 A x s x')). Qed.
Lemma lem3736483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736484 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term167 A x s).
Proof. exact (MK_COMB (@lem3736483 A) (@lem3736482 A x s)). Qed.
Lemma lem3736489 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term97 A R x s) = (term168 A R x s).
Proof. exact (MK_COMB (@lem3736443 A x s R) (@lem3736484 A x s)). Qed.
Lemma lem3736492 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term98 A R x s) = (term169 A R x s).
Proof. exact (MK_COMB (@lem3736336 A R x s) (@lem3736489 A R x s)). Qed.
Lemma lem3736495 {A : Type'} (R : type1402 A) (x : A) : (term99 A R x) = (term170 A R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3736492 A R x s)). Qed.
Lemma lem3736496 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3736497 {A : Type'} (R : type1402 A) (x : A) : (term100 A R x) = (term171 A R x).
Proof. exact (MK_COMB (@lem3736496 A) (@lem3736495 A R x)). Qed.
Lemma lem3736502 {A : Type'} (R : type1402 A) : (term101 A R) = (term172 A R).
Proof. exact (fun_ext (fun x : A => @lem3736497 A R x)). Qed.
Lemma lem3736503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736504 {A : Type'} (R : type1402 A) : (term102 A R) = (term173 A R).
Proof. exact (MK_COMB (@lem3736503 A) (@lem3736502 A R)). Qed.
Lemma lem3736509 {A : Type'} (R : type1402 A) : (term173 A R) = (term102 A R).
Proof. exact (SYM (@lem3736504 A R)). Qed.
Lemma lem3736511 (p : Prop) : p = (term174 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3736512 {A : Type'} (R : type1402 A) : (term173 A R) = (term175 A R).
Proof. exact (@lem3736511 (term173 A R)). Qed.
Lemma lem3736513 {A : Type'} (R : type1402 A) : (term175 A R) = (term173 A R).
Proof. exact (SYM (@lem3736512 A R)). Qed.
Lemma lem3736514 {A : Type'} (R : type1402 A) (h1 : term176 A R) : term176 A R.
Proof. exact (h1). Qed.
Lemma lem3736517 {A : Type'} (R : type1402 A) (h1 : term175 A R) : term175 A R.
Proof. exact (h1). Qed.
Lemma lem3736518 {A : Type'} (R : type1402 A) : term177 A R.
Proof. exact (fun h0 : term175 A R => @lem3736517 A R h0). Qed.
Lemma lem3736519 {A : Type'} (R : type1402 A) (h1 : term177 A R) : term177 A R.
Proof. exact (h1). Qed.
Lemma lem3736520 {A : Type'} (R : type1402 A) (h1 : term175 A R) : term175 A R.
Proof. exact (h1). Qed.
Lemma lem3736521 {A : Type'} (R : type1402 A) (h1 : term175 A R) (h2 : term177 A R) : term175 A R.
Proof. exact (@lem3736519 A R h2 (@lem3736520 A R h1)). Qed.
Lemma lem3736522 {A : Type'} (R : type1402 A) (h1 : term175 A R) : term178 A R.
Proof. exact (fun h0 : term177 A R => @lem3736521 A R h1 h0). Qed.
Lemma lem3736523 {A : Type'} (R : type1402 A) (h1 : term177 A R) : term177 A R.
Proof. exact (h1). Qed.
Lemma lem3736524 {A : Type'} (R : type1402 A) (h1 : term175 A R) (h2 : term177 A R) : term175 A R.
Proof. exact (@lem3736522 A R h1 (@lem3736523 A R h2)). Qed.
Lemma lem3736525 {A : Type'} (R : type1402 A) (h1 : term177 A R) : term177 A R.
Proof. exact (fun h0 : term175 A R => @lem3736524 A R h0 h1). Qed.
Lemma lem3736526 {A : Type'} (R : type1402 A) : term179 A R.
Proof. exact (fun h0 : term177 A R => @lem3736525 A R h0). Qed.
Lemma lem3736529 {A : Type'} (R : type1402 A) : term177 A R.
Proof. exact (@lem3736526 A R (@lem3736518 A R)). Qed.
Lemma lem3736530 {A : Type'} (R : type1402 A) : term177 A R.
Proof. exact (@lem3736529 A R). Qed.
Lemma lem3736536 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3736537 {A : Type'} (R : type1402 A) : (term175 A R) = (term180 A R).
Proof. exact (@lem3736536 (term176 A R)). Qed.
Lemma lem3736539 (t : Prop) : (term181 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3736540 {A : Type'} (R : type1402 A) : (term180 A R) = (term173 A R).
Proof. exact (@lem3736539 (term173 A R)). Qed.
Lemma lem3736545 {A : Type'} (R : type1402 A) : (term175 A R) = (term173 A R).
Proof. exact (TRANS (@lem3736537 A R) (@lem3736540 A R)). Qed.
Lemma lem3736714 {A : Type'} : (term182 A) = (term183 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem3736545 A R)). Qed.
Lemma lem3736715 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem3736724 {A : Type'} : (term184 A) = (term185 A).
Proof. exact (MK_COMB (@lem3736715 A) (@lem3736714 A)). Qed.
Lemma lem3736731 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term164 A x s x') = (term164 A x s x').
Proof. exact (eq_refl (term164 A x s x')). Qed.
Lemma lem3736732 {A : Type'} (x : A) (s : A -> Prop) : (term166 A x s) = (term166 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3736731 A x s x')). Qed.
Lemma lem3736733 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736734 {A : Type'} (x : A) (s : A -> Prop) : (term167 A x s) = (term167 A x s).
Proof. exact (MK_COMB (@lem3736733 A) (@lem3736732 A x s)). Qed.
Lemma lem3736743 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term146 A x s R x' y) = (term146 A x s R x' y).
Proof. exact (eq_refl (term146 A x s R x' y)). Qed.
Lemma lem3736744 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term148 A x s R x') = (term148 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3736743 A x s R x' y)). Qed.
Lemma lem3736745 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3736746 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term150 A x s R x') = (term150 A x s R x').
Proof. exact (MK_COMB (@lem3736745 A) (@lem3736744 A x s R x')). Qed.
Lemma lem3736753 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term142 A x s x') = (term142 A x s x').
Proof. exact (eq_refl (term142 A x s x')). Qed.
Lemma lem3736754 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term152 A x s R x') = (term152 A x s R x').
Proof. exact (MK_COMB (@lem3736753 A x s x') (@lem3736746 A x s R x')). Qed.
Lemma lem3736755 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term154 A x s R) = (term154 A x s R).
Proof. exact (fun_ext (fun x' : A => @lem3736754 A x s R x')). Qed.
Lemma lem3736756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736757 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term156 A x s R) = (term156 A x s R).
Proof. exact (MK_COMB (@lem3736756 A) (@lem3736755 A x s R)). Qed.
Lemma lem3736766 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term186 A y R x z) = (term186 A y R x z).
Proof. exact (eq_refl (term186 A y R x z)). Qed.
Lemma lem3736767 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term187 A y R x) = (term187 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3736766 A y R x z)). Qed.
Lemma lem3736768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736769 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term188 A y R x) = (term188 A y R x).
Proof. exact (MK_COMB (@lem3736768 A) (@lem3736767 A y R x)). Qed.
Lemma lem3736770 {A : Type'} (R : type1402 A) (x : A) : (term189 A R x) = (term189 A R x).
Proof. exact (fun_ext (fun y : A => @lem3736769 A y R x)). Qed.
Lemma lem3736771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736772 {A : Type'} (R : type1402 A) (x : A) : (term190 A R x) = (term190 A R x).
Proof. exact (MK_COMB (@lem3736771 A) (@lem3736770 A R x)). Qed.
Lemma lem3736773 {A : Type'} (R : type1402 A) : (term191 A R) = (term191 A R).
Proof. exact (fun_ext (fun x : A => @lem3736772 A R x)). Qed.
Lemma lem3736774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736775 {A : Type'} (R : type1402 A) : (term80 A R) = (term80 A R).
Proof. exact (MK_COMB (@lem3736774 A) (@lem3736773 A R)). Qed.
Lemma lem3736776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736777 {A : Type'} (R : type1402 A) : (term77 A R) = (term77 A R).
Proof. exact (MK_COMB (@lem3736776) (@lem3736775 A R)). Qed.
Lemma lem3736778 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term158 A x s R) = (term158 A x s R).
Proof. exact (MK_COMB (@lem3736777 A R) (@lem3736757 A x s R)). Qed.
Lemma lem3736781 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3736782 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3736781 A R x)). Qed.
Lemma lem3736783 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736784 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3736783 A) (@lem3736782 A R)). Qed.
Lemma lem3736785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736786 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (MK_COMB (@lem3736785) (@lem3736784 A R)). Qed.
Lemma lem3736787 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term160 A x s R) = (term160 A x s R).
Proof. exact (MK_COMB (@lem3736786 A R) (@lem3736778 A x s R)). Qed.
Lemma lem3736788 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736789 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term161 A x s R) = (term161 A x s R).
Proof. exact (MK_COMB (@lem3736788) (@lem3736787 A x s R)). Qed.
Lemma lem3736790 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term168 A R x s) = (term168 A R x s).
Proof. exact (MK_COMB (@lem3736789 A x s R) (@lem3736734 A x s)). Qed.
Lemma lem3736797 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3736800 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term125 A s x).
Proof. exact (eq_refl (term125 A s x)). Qed.
Lemma lem3736801 {A : Type'} (s : A -> Prop) : (term127 A s) = (term127 A s).
Proof. exact (fun_ext (fun x : A => @lem3736800 A s x)). Qed.
Lemma lem3736802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736803 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (MK_COMB (@lem3736802 A) (@lem3736801 A s)). Qed.
Lemma lem3736808 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term108 A s R x y) = (term108 A s R x y).
Proof. exact (eq_refl (term108 A s R x y)). Qed.
Lemma lem3736809 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term110 A s R x) = (term110 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3736808 A s R x y)). Qed.
Lemma lem3736810 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3736811 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term112 A s R x) = (term112 A s R x).
Proof. exact (MK_COMB (@lem3736810 A) (@lem3736809 A s R x)). Qed.
Lemma lem3736814 {A : Type'} (s : A -> Prop) (x : A) : (term104 A s x) = (term104 A s x).
Proof. exact (eq_refl (term104 A s x)). Qed.
Lemma lem3736815 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term114 A s R x) = (term114 A s R x).
Proof. exact (MK_COMB (@lem3736814 A s x) (@lem3736811 A s R x)). Qed.
Lemma lem3736816 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term116 A s R) = (term116 A s R).
Proof. exact (fun_ext (fun x : A => @lem3736815 A s R x)). Qed.
Lemma lem3736817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736818 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term118 A s R) = (term118 A s R).
Proof. exact (MK_COMB (@lem3736817 A) (@lem3736816 A s R)). Qed.
Lemma lem3736827 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term186 A y R x z) = (term186 A y R x z).
Proof. exact (eq_refl (term186 A y R x z)). Qed.
Lemma lem3736828 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term187 A y R x) = (term187 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3736827 A y R x z)). Qed.
Lemma lem3736829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736830 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term188 A y R x) = (term188 A y R x).
Proof. exact (MK_COMB (@lem3736829 A) (@lem3736828 A y R x)). Qed.
Lemma lem3736831 {A : Type'} (R : type1402 A) (x : A) : (term189 A R x) = (term189 A R x).
Proof. exact (fun_ext (fun y : A => @lem3736830 A y R x)). Qed.
Lemma lem3736832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736833 {A : Type'} (R : type1402 A) (x : A) : (term190 A R x) = (term190 A R x).
Proof. exact (MK_COMB (@lem3736832 A) (@lem3736831 A R x)). Qed.
Lemma lem3736834 {A : Type'} (R : type1402 A) : (term191 A R) = (term191 A R).
Proof. exact (fun_ext (fun x : A => @lem3736833 A R x)). Qed.
Lemma lem3736835 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736836 {A : Type'} (R : type1402 A) : (term80 A R) = (term80 A R).
Proof. exact (MK_COMB (@lem3736835 A) (@lem3736834 A R)). Qed.
Lemma lem3736837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736838 {A : Type'} (R : type1402 A) : (term77 A R) = (term77 A R).
Proof. exact (MK_COMB (@lem3736837) (@lem3736836 A R)). Qed.
Lemma lem3736839 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term120 A s R) = (term120 A s R).
Proof. exact (MK_COMB (@lem3736838 A R) (@lem3736818 A s R)). Qed.
Lemma lem3736842 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3736843 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3736842 A R x)). Qed.
Lemma lem3736844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736845 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3736844 A) (@lem3736843 A R)). Qed.
Lemma lem3736846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736847 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (MK_COMB (@lem3736846) (@lem3736845 A R)). Qed.
Lemma lem3736848 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term121 A s R) = (term121 A s R).
Proof. exact (MK_COMB (@lem3736847 A R) (@lem3736839 A s R)). Qed.
Lemma lem3736849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736850 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term122 A s R) = (term122 A s R).
Proof. exact (MK_COMB (@lem3736849) (@lem3736848 A s R)). Qed.
Lemma lem3736851 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term129 A R s) = (term129 A R s).
Proof. exact (MK_COMB (@lem3736850 A s R) (@lem3736803 A s)). Qed.
Lemma lem3736852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3736853 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term130 A R s) = (term130 A R s).
Proof. exact (MK_COMB (@lem3736852) (@lem3736851 A R s)). Qed.
Lemma lem3736854 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term135 A R x s) = (term135 A R x s).
Proof. exact (MK_COMB (@lem3736853 A R s) (@lem3736797 A x s)). Qed.
Lemma lem3736855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3736856 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term136 A R x s) = (term136 A R x s).
Proof. exact (MK_COMB (@lem3736855) (@lem3736854 A R x s)). Qed.
Lemma lem3736857 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term169 A R x s) = (term169 A R x s).
Proof. exact (MK_COMB (@lem3736856 A R x s) (@lem3736790 A R x s)). Qed.
Lemma lem3736858 {A : Type'} (R : type1402 A) (x : A) : (term170 A R x) = (term170 A R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3736857 A R x s)). Qed.
Lemma lem3736859 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3736860 {A : Type'} (R : type1402 A) (x : A) : (term171 A R x) = (term171 A R x).
Proof. exact (MK_COMB (@lem3736859 A) (@lem3736858 A R x)). Qed.
Lemma lem3736861 {A : Type'} (R : type1402 A) : (term172 A R) = (term172 A R).
Proof. exact (fun_ext (fun x : A => @lem3736860 A R x)). Qed.
Lemma lem3736862 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3736863 {A : Type'} (R : type1402 A) : (term173 A R) = (term173 A R).
Proof. exact (MK_COMB (@lem3736862 A) (@lem3736861 A R)). Qed.
Lemma lem3736864 {A : Type'} : (term183 A) = (term183 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem3736863 A R)). Qed.
Lemma lem3736865 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem3736866 {A : Type'} : (term185 A) = (term185 A).
Proof. exact (MK_COMB (@lem3736865 A) (@lem3736864 A)). Qed.
Lemma lem3737011 {A : Type'} : (term184 A) = (term185 A).
Proof. exact (TRANS (@lem3736724 A) (@lem3736866 A)). Qed.
Lemma lem3737012 {A : Type'} : (term185 A) = (term184 A).
Proof. exact (SYM (@lem3737011 A)). Qed.
Lemma lem3737013 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term135 A R x s) : term135 A R x s.
Proof. exact (h1). Qed.
Lemma lem3737014 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (h1 : term160 A x s R) : term160 A x s R.
Proof. exact (h1). Qed.
Lemma lem3737018 {A : Type'} (R : type1402 A) (x : A) : (term195 A R x) = (R x x).
Proof. exact (@lem16933 (R x x)). Qed.
Lemma lem3737019 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3737020 {A : Type'} (R : type1402 A) : (term198 A R) = (term199 A R).
Proof. exact (@lem3737019 A (term193 A R)). Qed.
Lemma lem3737021 {A : Type'} (R : type1402 A) (x : A) : (term200 A R x) = (term192 A R x).
Proof. exact (eq_refl (term200 A R x)). Qed.
Lemma lem3737022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737023 {A : Type'} (R : type1402 A) (x : A) : (term201 A R x) = (term195 A R x).
Proof. exact (MK_COMB (@lem3737022) (@lem3737021 A R x)). Qed.
Lemma lem3737024 {A : Type'} (R : type1402 A) (x : A) : (term201 A R x) = (R x x).
Proof. exact (TRANS (@lem3737023 A R x) (@lem3737018 A R x)). Qed.
Lemma lem3737025 {A : Type'} (R : type1402 A) : (term202 A R) = (term203 A R).
Proof. exact (fun_ext (fun x : A => @lem3737024 A R x)). Qed.
Lemma lem3737026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737027 {A : Type'} (R : type1402 A) : (term199 A R) = (term204 A R).
Proof. exact (MK_COMB (@lem3737026 A) (@lem3737025 A R)). Qed.
Lemma lem3737028 {A : Type'} (R : type1402 A) : (term198 A R) = (term204 A R).
Proof. exact (TRANS (@lem3737020 A R) (@lem3737027 A R)). Qed.
Lemma lem3737039 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term205 A y R x z) = (term206 A y R x z).
Proof. exact (@lem17362 (term207 A x R y z) (R x z)). Qed.
Lemma lem3737040 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3737041 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term208 A y R x) = (term209 A y R x).
Proof. exact (@lem3737040 A (term187 A y R x)). Qed.
Lemma lem3737042 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term210 A y R x z) = (term186 A y R x z).
Proof. exact (eq_refl (term210 A y R x z)). Qed.
Lemma lem3737043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737044 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term211 A y R x z) = (term205 A y R x z).
Proof. exact (MK_COMB (@lem3737043) (@lem3737042 A y R x z)). Qed.
Lemma lem3737045 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term211 A y R x z) = (term206 A y R x z).
Proof. exact (TRANS (@lem3737044 A y R x z) (@lem3737039 A y R x z)). Qed.
Lemma lem3737046 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term212 A y R x) = (term213 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3737045 A y R x z)). Qed.
Lemma lem3737047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737048 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term209 A y R x) = (term214 A y R x).
Proof. exact (MK_COMB (@lem3737047 A) (@lem3737046 A y R x)). Qed.
Lemma lem3737049 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term208 A y R x) = (term214 A y R x).
Proof. exact (TRANS (@lem3737041 A y R x) (@lem3737048 A y R x)). Qed.
Lemma lem3737050 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3737051 {A : Type'} (R : type1402 A) (x : A) : (term215 A R x) = (term216 A R x).
Proof. exact (@lem3737050 A (term189 A R x)). Qed.
Lemma lem3737052 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term217 A R x y) = (term188 A y R x).
Proof. exact (eq_refl (term217 A R x y)). Qed.
Lemma lem3737053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737054 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term218 A R x y) = (term208 A y R x).
Proof. exact (MK_COMB (@lem3737053) (@lem3737052 A y R x)). Qed.
Lemma lem3737055 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term218 A R x y) = (term214 A y R x).
Proof. exact (TRANS (@lem3737054 A y R x) (@lem3737049 A y R x)). Qed.
Lemma lem3737056 {A : Type'} (R : type1402 A) (x : A) : (term219 A R x) = (term220 A R x).
Proof. exact (fun_ext (fun y : A => @lem3737055 A y R x)). Qed.
Lemma lem3737057 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737058 {A : Type'} (R : type1402 A) (x : A) : (term216 A R x) = (term221 A R x).
Proof. exact (MK_COMB (@lem3737057 A) (@lem3737056 A R x)). Qed.
Lemma lem3737059 {A : Type'} (R : type1402 A) (x : A) : (term215 A R x) = (term221 A R x).
Proof. exact (TRANS (@lem3737051 A R x) (@lem3737058 A R x)). Qed.
Lemma lem3737060 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3737061 {A : Type'} (R : type1402 A) : (term222 A R) = (term223 A R).
Proof. exact (@lem3737060 A (term191 A R)). Qed.
Lemma lem3737062 {A : Type'} (R : type1402 A) (x : A) : (term224 A R x) = (term190 A R x).
Proof. exact (eq_refl (term224 A R x)). Qed.
Lemma lem3737063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737064 {A : Type'} (R : type1402 A) (x : A) : (term225 A R x) = (term215 A R x).
Proof. exact (MK_COMB (@lem3737063) (@lem3737062 A R x)). Qed.
Lemma lem3737065 {A : Type'} (R : type1402 A) (x : A) : (term225 A R x) = (term221 A R x).
Proof. exact (TRANS (@lem3737064 A R x) (@lem3737059 A R x)). Qed.
Lemma lem3737066 {A : Type'} (R : type1402 A) : (term226 A R) = (term227 A R).
Proof. exact (fun_ext (fun x : A => @lem3737065 A R x)). Qed.
Lemma lem3737067 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737068 {A : Type'} (R : type1402 A) : (term223 A R) = (term228 A R).
Proof. exact (MK_COMB (@lem3737067 A) (@lem3737066 A R)). Qed.
Lemma lem3737069 {A : Type'} (R : type1402 A) : (term222 A R) = (term228 A R).
Proof. exact (TRANS (@lem3737061 A R) (@lem3737068 A R)). Qed.
Lemma lem3737077 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term229 A s R x y) = (term230 A s R x y).
Proof. exact (@lem17045 (s y) (R x y)). Qed.
Lemma lem3737078 {A : Type'} (P : A -> Prop) : (term231 A P) = (term128 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3737079 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term232 A s R x) = (term233 A s R x).
Proof. exact (@lem3737078 A (term110 A s R x)). Qed.
Lemma lem3737080 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term234 A s R x y) = (term108 A s R x y).
Proof. exact (eq_refl (term234 A s R x y)). Qed.
Lemma lem3737081 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737082 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term235 A s R x y) = (term229 A s R x y).
Proof. exact (MK_COMB (@lem3737081) (@lem3737080 A s R x y)). Qed.
Lemma lem3737083 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term235 A s R x y) = (term230 A s R x y).
Proof. exact (TRANS (@lem3737082 A s R x y) (@lem3737077 A s R x y)). Qed.
Lemma lem3737084 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term236 A s R x) = (term237 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737083 A s R x y)). Qed.
Lemma lem3737085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737086 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term233 A s R x) = (term238 A s R x).
Proof. exact (MK_COMB (@lem3737085 A) (@lem3737084 A s R x)). Qed.
Lemma lem3737087 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term232 A s R x) = (term238 A s R x).
Proof. exact (TRANS (@lem3737079 A s R x) (@lem3737086 A s R x)). Qed.
Lemma lem3737089 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem3737090 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term239 A s R x) = (term240 A s R x).
Proof. exact (MK_COMB (@lem3737089 A s x) (@lem3737087 A s R x)). Qed.
Lemma lem3737091 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term241 A s R x) = (term239 A s R x).
Proof. exact (@lem17362 (s x) (term112 A s R x)). Qed.
Lemma lem3737092 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term241 A s R x) = (term240 A s R x).
Proof. exact (TRANS (@lem3737091 A s R x) (@lem3737090 A s R x)). Qed.
Lemma lem3737093 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3737094 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term242 A s R) = (term243 A s R).
Proof. exact (@lem3737093 A (term116 A s R)). Qed.
Lemma lem3737095 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term244 A s R x) = (term114 A s R x).
Proof. exact (eq_refl (term244 A s R x)). Qed.
Lemma lem3737096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737097 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term245 A s R x) = (term241 A s R x).
Proof. exact (MK_COMB (@lem3737096) (@lem3737095 A s R x)). Qed.
Lemma lem3737098 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term245 A s R x) = (term240 A s R x).
Proof. exact (TRANS (@lem3737097 A s R x) (@lem3737092 A s R x)). Qed.
Lemma lem3737099 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term246 A s R) = (term247 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737098 A s R x)). Qed.
Lemma lem3737100 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737101 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term243 A s R) = (term248 A s R).
Proof. exact (MK_COMB (@lem3737100 A) (@lem3737099 A s R)). Qed.
Lemma lem3737102 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term242 A s R) = (term248 A s R).
Proof. exact (TRANS (@lem3737094 A s R) (@lem3737101 A s R)). Qed.
Lemma lem3737103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737104 {A : Type'} (R : type1402 A) : (term249 A R) = (term250 A R).
Proof. exact (MK_COMB (@lem3737103) (@lem3737069 A R)). Qed.
Lemma lem3737105 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term251 A s R) = (term252 A s R).
Proof. exact (MK_COMB (@lem3737104 A R) (@lem3737102 A s R)). Qed.
Lemma lem3737106 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term253 A s R) = (term251 A s R).
Proof. exact (@lem17045 (term80 A R) (term118 A s R)). Qed.
Lemma lem3737107 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term253 A s R) = (term252 A s R).
Proof. exact (TRANS (@lem3737106 A s R) (@lem3737105 A s R)). Qed.
Lemma lem3737108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737109 {A : Type'} (R : type1402 A) : (term254 A R) = (term255 A R).
Proof. exact (MK_COMB (@lem3737108) (@lem3737028 A R)). Qed.
Lemma lem3737110 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term256 A s R) = (term257 A s R).
Proof. exact (MK_COMB (@lem3737109 A R) (@lem3737107 A s R)). Qed.
Lemma lem3737111 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term258 A s R) = (term256 A s R).
Proof. exact (@lem17045 (term194 A R) (term120 A s R)). Qed.
Lemma lem3737112 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term258 A s R) = (term257 A s R).
Proof. exact (TRANS (@lem3737111 A s R) (@lem3737110 A s R)). Qed.
Lemma lem3737113 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term125 A s x).
Proof. exact (eq_refl (term125 A s x)). Qed.
Lemma lem3737114 {A : Type'} (s : A -> Prop) : (term127 A s) = (term127 A s).
Proof. exact (fun_ext (fun x : A => @lem3737113 A s x)). Qed.
Lemma lem3737115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737116 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (MK_COMB (@lem3737115 A) (@lem3737114 A s)). Qed.
Lemma lem3737117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737118 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term259 A s R) = (term260 A s R).
Proof. exact (MK_COMB (@lem3737117) (@lem3737112 A s R)). Qed.
Lemma lem3737119 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term261 A R s) = (term262 A R s).
Proof. exact (MK_COMB (@lem3737118 A s R) (@lem3737116 A s)). Qed.
Lemma lem3737120 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term129 A R s) = (term261 A R s).
Proof. exact (@lem17265 (term121 A s R) (term128 A s)). Qed.
Lemma lem3737121 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term129 A R s) = (term262 A R s).
Proof. exact (TRANS (@lem3737120 A R s) (@lem3737119 A R s)). Qed.
Lemma lem3737126 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737128 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term130 A R s) = (term263 A R s).
Proof. exact (MK_COMB (@lem3737127) (@lem3737121 A R s)). Qed.
Lemma lem3737129 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term135 A R x s) = (term264 A R x s).
Proof. exact (MK_COMB (@lem3737128 A R s) (@lem3737126 A x s)). Qed.
Lemma lem3737272 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3737273 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem3737272 A P Q). Qed.
Lemma lem3737274 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term267 A s R) = (term268 A s R).
Proof. exact (@lem3737273 A (term227 A R) (term247 A s R)). Qed.
Lemma lem3737275 {A : Type'} (R : type1402 A) (x : A) : (term269 A R x) = (term221 A R x).
Proof. exact (eq_refl (term269 A R x)). Qed.
Lemma lem3737276 {A : Type'} (R : type1402 A) : (term270 A R) = (term227 A R).
Proof. exact (fun_ext (fun x : A => @lem3737275 A R x)). Qed.
Lemma lem3737277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737278 {A : Type'} (R : type1402 A) : (term271 A R) = (term228 A R).
Proof. exact (MK_COMB (@lem3737277 A) (@lem3737276 A R)). Qed.
Lemma lem3737279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737280 {A : Type'} (R : type1402 A) : (term272 A R) = (term250 A R).
Proof. exact (MK_COMB (@lem3737279) (@lem3737278 A R)). Qed.
Lemma lem3737281 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term273 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term273 A s R x)). Qed.
Lemma lem3737282 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term274 A s R) = (term247 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737281 A s R x)). Qed.
Lemma lem3737283 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737284 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term275 A s R) = (term248 A s R).
Proof. exact (MK_COMB (@lem3737283 A) (@lem3737282 A s R)). Qed.
Lemma lem3737285 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term267 A s R) = (term252 A s R).
Proof. exact (MK_COMB (@lem3737280 A R) (@lem3737284 A s R)). Qed.
Lemma lem3737286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737287 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term276 A s R) = (term277 A s R).
Proof. exact (MK_COMB (@lem3737286) (@lem3737285 A s R)). Qed.
Lemma lem3737288 {A : Type'} (R : type1402 A) (x : A) : (term269 A R x) = (term221 A R x).
Proof. exact (eq_refl (term269 A R x)). Qed.
Lemma lem3737289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737290 {A : Type'} (R : type1402 A) (x : A) : (term278 A R x) = (term279 A R x).
Proof. exact (MK_COMB (@lem3737289) (@lem3737288 A R x)). Qed.
Lemma lem3737291 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term273 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term273 A s R x)). Qed.
Lemma lem3737292 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term280 A s R x) = (term281 A s R x).
Proof. exact (MK_COMB (@lem3737290 A R x) (@lem3737291 A s R x)). Qed.
Lemma lem3737293 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term282 A s R) = (term283 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737292 A s R x)). Qed.
Lemma lem3737294 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737295 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term268 A s R) = (term284 A s R).
Proof. exact (MK_COMB (@lem3737294 A) (@lem3737293 A s R)). Qed.
Lemma lem3737296 {A : Type'} (s : A -> Prop) (R : type1402 A) : ((term267 A s R) = (term268 A s R)) = ((term252 A s R) = (term284 A s R)).
Proof. exact (MK_COMB (@lem3737287 A s R) (@lem3737295 A s R)). Qed.
Lemma lem3737297 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term252 A s R) = (term284 A s R).
Proof. exact (EQ_MP (@lem3737296 A s R) (@lem3737274 A s R)). Qed.
Lemma lem3737299 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3737300 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem3737299 A P Q). Qed.
Lemma lem3737301 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term287 A s R x) = (term288 A s R x).
Proof. exact (@lem3737300 A (term220 A R x) (term240 A s R x)). Qed.
Lemma lem3737302 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term289 A R x y) = (term214 A y R x).
Proof. exact (eq_refl (term289 A R x y)). Qed.
Lemma lem3737303 {A : Type'} (R : type1402 A) (x : A) : (term290 A R x) = (term220 A R x).
Proof. exact (fun_ext (fun y : A => @lem3737302 A y R x)). Qed.
Lemma lem3737304 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737305 {A : Type'} (R : type1402 A) (x : A) : (term291 A R x) = (term221 A R x).
Proof. exact (MK_COMB (@lem3737304 A) (@lem3737303 A R x)). Qed.
Lemma lem3737306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737307 {A : Type'} (R : type1402 A) (x : A) : (term292 A R x) = (term279 A R x).
Proof. exact (MK_COMB (@lem3737306) (@lem3737305 A R x)). Qed.
Lemma lem3737308 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term240 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term240 A s R x)). Qed.
Lemma lem3737309 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term287 A s R x) = (term281 A s R x).
Proof. exact (MK_COMB (@lem3737307 A R x) (@lem3737308 A s R x)). Qed.
Lemma lem3737310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737311 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term293 A s R x) = (term294 A s R x).
Proof. exact (MK_COMB (@lem3737310) (@lem3737309 A s R x)). Qed.
Lemma lem3737312 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term289 A R x y) = (term214 A y R x).
Proof. exact (eq_refl (term289 A R x y)). Qed.
Lemma lem3737313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737314 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term295 A R x y) = (term296 A y R x).
Proof. exact (MK_COMB (@lem3737313) (@lem3737312 A y R x)). Qed.
Lemma lem3737315 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term240 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term240 A s R x)). Qed.
Lemma lem3737316 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term297 A y s R x) = (term298 A y s R x).
Proof. exact (MK_COMB (@lem3737314 A y R x) (@lem3737315 A s R x)). Qed.
Lemma lem3737317 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term299 A s R x) = (term300 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737316 A y s R x)). Qed.
Lemma lem3737318 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737319 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term288 A s R x) = (term301 A s R x).
Proof. exact (MK_COMB (@lem3737318 A) (@lem3737317 A s R x)). Qed.
Lemma lem3737320 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : ((term287 A s R x) = (term288 A s R x)) = ((term281 A s R x) = (term301 A s R x)).
Proof. exact (MK_COMB (@lem3737311 A s R x) (@lem3737319 A s R x)). Qed.
Lemma lem3737321 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term281 A s R x) = (term301 A s R x).
Proof. exact (EQ_MP (@lem3737320 A s R x) (@lem3737301 A s R x)). Qed.
Lemma lem3737323 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3737324 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem3737323 A P Q). Qed.
Lemma lem3737325 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term302 A y s R x) = (term303 A y s R x).
Proof. exact (@lem3737324 A (term213 A y R x) (term240 A s R x)). Qed.
Lemma lem3737326 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term304 A y R x z) = (term206 A y R x z).
Proof. exact (eq_refl (term304 A y R x z)). Qed.
Lemma lem3737327 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term305 A y R x) = (term213 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3737326 A y R x z)). Qed.
Lemma lem3737328 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737329 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term306 A y R x) = (term214 A y R x).
Proof. exact (MK_COMB (@lem3737328 A) (@lem3737327 A y R x)). Qed.
Lemma lem3737330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737331 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term307 A y R x) = (term296 A y R x).
Proof. exact (MK_COMB (@lem3737330) (@lem3737329 A y R x)). Qed.
Lemma lem3737332 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term240 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term240 A s R x)). Qed.
Lemma lem3737333 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term302 A y s R x) = (term298 A y s R x).
Proof. exact (MK_COMB (@lem3737331 A y R x) (@lem3737332 A s R x)). Qed.
Lemma lem3737334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737335 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term308 A y s R x) = (term309 A y s R x).
Proof. exact (MK_COMB (@lem3737334) (@lem3737333 A y s R x)). Qed.
Lemma lem3737336 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term304 A y R x z) = (term206 A y R x z).
Proof. exact (eq_refl (term304 A y R x z)). Qed.
Lemma lem3737337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737338 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term310 A y R x z) = (term311 A y R x z).
Proof. exact (MK_COMB (@lem3737337) (@lem3737336 A y R x z)). Qed.
Lemma lem3737339 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term240 A s R x) = (term240 A s R x).
Proof. exact (eq_refl (term240 A s R x)). Qed.
Lemma lem3737340 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term312 A y z s R x) = (term313 A y z s R x).
Proof. exact (MK_COMB (@lem3737338 A y R x z) (@lem3737339 A s R x)). Qed.
Lemma lem3737341 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term314 A y s R x) = (term315 A y s R x).
Proof. exact (fun_ext (fun z : A => @lem3737340 A y z s R x)). Qed.
Lemma lem3737342 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737343 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term303 A y s R x) = (term316 A y s R x).
Proof. exact (MK_COMB (@lem3737342 A) (@lem3737341 A y s R x)). Qed.
Lemma lem3737344 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : ((term302 A y s R x) = (term303 A y s R x)) = ((term298 A y s R x) = (term316 A y s R x)).
Proof. exact (MK_COMB (@lem3737335 A y s R x) (@lem3737343 A y s R x)). Qed.
Lemma lem3737345 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term298 A y s R x) = (term316 A y s R x).
Proof. exact (EQ_MP (@lem3737344 A y s R x) (@lem3737325 A y s R x)). Qed.
Lemma lem3737346 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term300 A s R x) = (term317 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737345 A y s R x)). Qed.
Lemma lem3737347 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737348 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term301 A s R x) = (term318 A s R x).
Proof. exact (MK_COMB (@lem3737347 A) (@lem3737346 A s R x)). Qed.
Lemma lem3737349 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term281 A s R x) = (term318 A s R x).
Proof. exact (TRANS (@lem3737321 A s R x) (@lem3737348 A s R x)). Qed.
Lemma lem3737350 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term283 A s R) = (term319 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737349 A s R x)). Qed.
Lemma lem3737351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737352 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term284 A s R) = (term320 A s R).
Proof. exact (MK_COMB (@lem3737351 A) (@lem3737350 A s R)). Qed.
Lemma lem3737353 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term252 A s R) = (term320 A s R).
Proof. exact (TRANS (@lem3737297 A s R) (@lem3737352 A s R)). Qed.
Lemma lem3737354 {A : Type'} (R : type1402 A) : (term255 A R) = (term255 A R).
Proof. exact (eq_refl (term255 A R)). Qed.
Lemma lem3737355 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term257 A s R) = (term321 A s R).
Proof. exact (MK_COMB (@lem3737354 A R) (@lem3737353 A s R)). Qed.
Lemma lem3737357 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3737358 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem3737357 A P Q). Qed.
Lemma lem3737359 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term322 A s R) = (term323 A s R).
Proof. exact (@lem3737358 A (term203 A R) (term319 A s R)). Qed.
Lemma lem3737360 {A : Type'} (R : type1402 A) (x : A) : (term324 A R x) = (R x x).
Proof. exact (eq_refl (term324 A R x)). Qed.
Lemma lem3737361 {A : Type'} (R : type1402 A) : (term325 A R) = (term203 A R).
Proof. exact (fun_ext (fun x : A => @lem3737360 A R x)). Qed.
Lemma lem3737362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737363 {A : Type'} (R : type1402 A) : (term326 A R) = (term204 A R).
Proof. exact (MK_COMB (@lem3737362 A) (@lem3737361 A R)). Qed.
Lemma lem3737364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737365 {A : Type'} (R : type1402 A) : (term327 A R) = (term255 A R).
Proof. exact (MK_COMB (@lem3737364) (@lem3737363 A R)). Qed.
Lemma lem3737366 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term328 A s R x) = (term318 A s R x).
Proof. exact (eq_refl (term328 A s R x)). Qed.
Lemma lem3737367 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term329 A s R) = (term319 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737366 A s R x)). Qed.
Lemma lem3737368 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737369 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term330 A s R) = (term320 A s R).
Proof. exact (MK_COMB (@lem3737368 A) (@lem3737367 A s R)). Qed.
Lemma lem3737370 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term322 A s R) = (term321 A s R).
Proof. exact (MK_COMB (@lem3737365 A R) (@lem3737369 A s R)). Qed.
Lemma lem3737371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737372 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term331 A s R) = (term332 A s R).
Proof. exact (MK_COMB (@lem3737371) (@lem3737370 A s R)). Qed.
Lemma lem3737373 {A : Type'} (R : type1402 A) (x : A) : (term324 A R x) = (R x x).
Proof. exact (eq_refl (term324 A R x)). Qed.
Lemma lem3737374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737375 {A : Type'} (R : type1402 A) (x : A) : (term333 A R x) = (term334 A R x).
Proof. exact (MK_COMB (@lem3737374) (@lem3737373 A R x)). Qed.
Lemma lem3737376 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term328 A s R x) = (term318 A s R x).
Proof. exact (eq_refl (term328 A s R x)). Qed.
Lemma lem3737377 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term335 A s R x) = (term336 A s R x).
Proof. exact (MK_COMB (@lem3737375 A R x) (@lem3737376 A s R x)). Qed.
Lemma lem3737378 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term337 A s R) = (term338 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737377 A s R x)). Qed.
Lemma lem3737379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737380 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term323 A s R) = (term339 A s R).
Proof. exact (MK_COMB (@lem3737379 A) (@lem3737378 A s R)). Qed.
Lemma lem3737381 {A : Type'} (s : A -> Prop) (R : type1402 A) : ((term322 A s R) = (term323 A s R)) = ((term321 A s R) = (term339 A s R)).
Proof. exact (MK_COMB (@lem3737372 A s R) (@lem3737380 A s R)). Qed.
Lemma lem3737382 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term321 A s R) = (term339 A s R).
Proof. exact (EQ_MP (@lem3737381 A s R) (@lem3737359 A s R)). Qed.
Lemma lem3737384 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3737385 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem3737384 A P Q). Qed.
Lemma lem3737386 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term342 A s R x) = (term343 A s R x).
Proof. exact (@lem3737385 A (R x x) (term317 A s R x)). Qed.
Lemma lem3737387 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term344 A s R x y) = (term316 A y s R x).
Proof. exact (eq_refl (term344 A s R x y)). Qed.
Lemma lem3737388 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term345 A s R x) = (term317 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737387 A y s R x)). Qed.
Lemma lem3737389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737390 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term346 A s R x) = (term318 A s R x).
Proof. exact (MK_COMB (@lem3737389 A) (@lem3737388 A s R x)). Qed.
Lemma lem3737391 {A : Type'} (R : type1402 A) (x : A) : (term334 A R x) = (term334 A R x).
Proof. exact (eq_refl (term334 A R x)). Qed.
Lemma lem3737392 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term342 A s R x) = (term336 A s R x).
Proof. exact (MK_COMB (@lem3737391 A R x) (@lem3737390 A s R x)). Qed.
Lemma lem3737393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737394 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term347 A s R x) = (term348 A s R x).
Proof. exact (MK_COMB (@lem3737393) (@lem3737392 A s R x)). Qed.
Lemma lem3737395 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term344 A s R x y) = (term316 A y s R x).
Proof. exact (eq_refl (term344 A s R x y)). Qed.
Lemma lem3737396 {A : Type'} (R : type1402 A) (x : A) : (term334 A R x) = (term334 A R x).
Proof. exact (eq_refl (term334 A R x)). Qed.
Lemma lem3737397 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term349 A s R x y) = (term350 A y s R x).
Proof. exact (MK_COMB (@lem3737396 A R x) (@lem3737395 A y s R x)). Qed.
Lemma lem3737398 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term351 A s R x) = (term352 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737397 A y s R x)). Qed.
Lemma lem3737399 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737400 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term343 A s R x) = (term353 A s R x).
Proof. exact (MK_COMB (@lem3737399 A) (@lem3737398 A s R x)). Qed.
Lemma lem3737401 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : ((term342 A s R x) = (term343 A s R x)) = ((term336 A s R x) = (term353 A s R x)).
Proof. exact (MK_COMB (@lem3737394 A s R x) (@lem3737400 A s R x)). Qed.
Lemma lem3737402 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term336 A s R x) = (term353 A s R x).
Proof. exact (EQ_MP (@lem3737401 A s R x) (@lem3737386 A s R x)). Qed.
Lemma lem3737404 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3737405 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem3737404 A P Q). Qed.
Lemma lem3737406 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term354 A y s R x) = (term355 A y s R x).
Proof. exact (@lem3737405 A (R x x) (term315 A y s R x)). Qed.
Lemma lem3737407 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term356 A y s R x z) = (term313 A y z s R x).
Proof. exact (eq_refl (term356 A y s R x z)). Qed.
Lemma lem3737408 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term357 A y s R x) = (term315 A y s R x).
Proof. exact (fun_ext (fun z : A => @lem3737407 A y z s R x)). Qed.
Lemma lem3737409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737410 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term358 A y s R x) = (term316 A y s R x).
Proof. exact (MK_COMB (@lem3737409 A) (@lem3737408 A y s R x)). Qed.
Lemma lem3737411 {A : Type'} (R : type1402 A) (x : A) : (term334 A R x) = (term334 A R x).
Proof. exact (eq_refl (term334 A R x)). Qed.
Lemma lem3737412 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term354 A y s R x) = (term350 A y s R x).
Proof. exact (MK_COMB (@lem3737411 A R x) (@lem3737410 A y s R x)). Qed.
Lemma lem3737413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737414 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term359 A y s R x) = (term360 A y s R x).
Proof. exact (MK_COMB (@lem3737413) (@lem3737412 A y s R x)). Qed.
Lemma lem3737415 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term356 A y s R x z) = (term313 A y z s R x).
Proof. exact (eq_refl (term356 A y s R x z)). Qed.
Lemma lem3737416 {A : Type'} (R : type1402 A) (x : A) : (term334 A R x) = (term334 A R x).
Proof. exact (eq_refl (term334 A R x)). Qed.
Lemma lem3737417 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term361 A y s R x z) = (term362 A y z s R x).
Proof. exact (MK_COMB (@lem3737416 A R x) (@lem3737415 A y z s R x)). Qed.
Lemma lem3737418 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term363 A y s R x) = (term364 A y s R x).
Proof. exact (fun_ext (fun z : A => @lem3737417 A y z s R x)). Qed.
Lemma lem3737419 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737420 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term355 A y s R x) = (term365 A y s R x).
Proof. exact (MK_COMB (@lem3737419 A) (@lem3737418 A y s R x)). Qed.
Lemma lem3737421 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : ((term354 A y s R x) = (term355 A y s R x)) = ((term350 A y s R x) = (term365 A y s R x)).
Proof. exact (MK_COMB (@lem3737414 A y s R x) (@lem3737420 A y s R x)). Qed.
Lemma lem3737422 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term350 A y s R x) = (term365 A y s R x).
Proof. exact (EQ_MP (@lem3737421 A y s R x) (@lem3737406 A y s R x)). Qed.
Lemma lem3737423 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term352 A s R x) = (term366 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737422 A y s R x)). Qed.
Lemma lem3737424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737425 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term353 A s R x) = (term367 A s R x).
Proof. exact (MK_COMB (@lem3737424 A) (@lem3737423 A s R x)). Qed.
Lemma lem3737426 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term336 A s R x) = (term367 A s R x).
Proof. exact (TRANS (@lem3737402 A s R x) (@lem3737425 A s R x)). Qed.
Lemma lem3737427 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term338 A s R) = (term368 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737426 A s R x)). Qed.
Lemma lem3737428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737429 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term339 A s R) = (term369 A s R).
Proof. exact (MK_COMB (@lem3737428 A) (@lem3737427 A s R)). Qed.
Lemma lem3737430 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term321 A s R) = (term369 A s R).
Proof. exact (TRANS (@lem3737382 A s R) (@lem3737429 A s R)). Qed.
Lemma lem3737431 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term257 A s R) = (term369 A s R).
Proof. exact (TRANS (@lem3737355 A s R) (@lem3737430 A s R)). Qed.
Lemma lem3737432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737433 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term260 A s R) = (term370 A s R).
Proof. exact (MK_COMB (@lem3737432) (@lem3737431 A s R)). Qed.
Lemma lem3737434 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737435 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term262 A R s) = (term371 A R s).
Proof. exact (MK_COMB (@lem3737433 A s R) (@lem3737434 A s)). Qed.
Lemma lem3737437 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3737438 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem3737437 A P Q). Qed.
Lemma lem3737439 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term372 A R s) = (term373 A R s).
Proof. exact (@lem3737438 A (term368 A s R) (term128 A s)). Qed.
Lemma lem3737440 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term374 A s R x) = (term367 A s R x).
Proof. exact (eq_refl (term374 A s R x)). Qed.
Lemma lem3737441 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term375 A s R) = (term368 A s R).
Proof. exact (fun_ext (fun x : A => @lem3737440 A s R x)). Qed.
Lemma lem3737442 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737443 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term376 A s R) = (term369 A s R).
Proof. exact (MK_COMB (@lem3737442 A) (@lem3737441 A s R)). Qed.
Lemma lem3737444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737445 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term377 A s R) = (term370 A s R).
Proof. exact (MK_COMB (@lem3737444) (@lem3737443 A s R)). Qed.
Lemma lem3737446 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737447 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term372 A R s) = (term371 A R s).
Proof. exact (MK_COMB (@lem3737445 A s R) (@lem3737446 A s)). Qed.
Lemma lem3737448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737449 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term378 A R s) = (term379 A R s).
Proof. exact (MK_COMB (@lem3737448) (@lem3737447 A R s)). Qed.
Lemma lem3737450 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term374 A s R x) = (term367 A s R x).
Proof. exact (eq_refl (term374 A s R x)). Qed.
Lemma lem3737451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737452 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term380 A s R x) = (term381 A s R x).
Proof. exact (MK_COMB (@lem3737451) (@lem3737450 A s R x)). Qed.
Lemma lem3737453 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737454 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term382 A R x s) = (term383 A R x s).
Proof. exact (MK_COMB (@lem3737452 A s R x) (@lem3737453 A s)). Qed.
Lemma lem3737455 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term384 A R s) = (term385 A R s).
Proof. exact (fun_ext (fun x : A => @lem3737454 A R x s)). Qed.
Lemma lem3737456 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737457 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term373 A R s) = (term386 A R s).
Proof. exact (MK_COMB (@lem3737456 A) (@lem3737455 A R s)). Qed.
Lemma lem3737458 {A : Type'} (R : type1402 A) (s : A -> Prop) : ((term372 A R s) = (term373 A R s)) = ((term371 A R s) = (term386 A R s)).
Proof. exact (MK_COMB (@lem3737449 A R s) (@lem3737457 A R s)). Qed.
Lemma lem3737459 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term371 A R s) = (term386 A R s).
Proof. exact (EQ_MP (@lem3737458 A R s) (@lem3737439 A R s)). Qed.
Lemma lem3737461 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3737462 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem3737461 A P Q). Qed.
Lemma lem3737463 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term387 A R x s) = (term388 A R x s).
Proof. exact (@lem3737462 A (term366 A s R x) (term128 A s)). Qed.
Lemma lem3737464 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term389 A s R x y) = (term365 A y s R x).
Proof. exact (eq_refl (term389 A s R x y)). Qed.
Lemma lem3737465 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term390 A s R x) = (term366 A s R x).
Proof. exact (fun_ext (fun y : A => @lem3737464 A y s R x)). Qed.
Lemma lem3737466 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737467 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term391 A s R x) = (term367 A s R x).
Proof. exact (MK_COMB (@lem3737466 A) (@lem3737465 A s R x)). Qed.
Lemma lem3737468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737469 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term392 A s R x) = (term381 A s R x).
Proof. exact (MK_COMB (@lem3737468) (@lem3737467 A s R x)). Qed.
Lemma lem3737470 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737471 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term387 A R x s) = (term383 A R x s).
Proof. exact (MK_COMB (@lem3737469 A s R x) (@lem3737470 A s)). Qed.
Lemma lem3737472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737473 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term393 A R x s) = (term394 A R x s).
Proof. exact (MK_COMB (@lem3737472) (@lem3737471 A R x s)). Qed.
Lemma lem3737474 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term389 A s R x y) = (term365 A y s R x).
Proof. exact (eq_refl (term389 A s R x y)). Qed.
Lemma lem3737475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737476 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term395 A s R x y) = (term396 A y s R x).
Proof. exact (MK_COMB (@lem3737475) (@lem3737474 A y s R x)). Qed.
Lemma lem3737477 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737478 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term397 A R x y s) = (term398 A y R x s).
Proof. exact (MK_COMB (@lem3737476 A y s R x) (@lem3737477 A s)). Qed.
Lemma lem3737479 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term399 A R x s) = (term400 A R x s).
Proof. exact (fun_ext (fun y : A => @lem3737478 A y R x s)). Qed.
Lemma lem3737480 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737481 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term388 A R x s) = (term401 A R x s).
Proof. exact (MK_COMB (@lem3737480 A) (@lem3737479 A R x s)). Qed.
Lemma lem3737482 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : ((term387 A R x s) = (term388 A R x s)) = ((term383 A R x s) = (term401 A R x s)).
Proof. exact (MK_COMB (@lem3737473 A R x s) (@lem3737481 A R x s)). Qed.
Lemma lem3737483 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term383 A R x s) = (term401 A R x s).
Proof. exact (EQ_MP (@lem3737482 A R x s) (@lem3737463 A R x s)). Qed.
Lemma lem3737485 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3737486 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem3737485 A P Q). Qed.
Lemma lem3737487 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term402 A y R x s) = (term403 A y R x s).
Proof. exact (@lem3737486 A (term364 A y s R x) (term128 A s)). Qed.
Lemma lem3737488 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term404 A y s R x z) = (term362 A y z s R x).
Proof. exact (eq_refl (term404 A y s R x z)). Qed.
Lemma lem3737489 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term405 A y s R x) = (term364 A y s R x).
Proof. exact (fun_ext (fun z : A => @lem3737488 A y z s R x)). Qed.
Lemma lem3737490 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737491 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term406 A y s R x) = (term365 A y s R x).
Proof. exact (MK_COMB (@lem3737490 A) (@lem3737489 A y s R x)). Qed.
Lemma lem3737492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737493 {A : Type'} (y : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term407 A y s R x) = (term396 A y s R x).
Proof. exact (MK_COMB (@lem3737492) (@lem3737491 A y s R x)). Qed.
Lemma lem3737494 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737495 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term402 A y R x s) = (term398 A y R x s).
Proof. exact (MK_COMB (@lem3737493 A y s R x) (@lem3737494 A s)). Qed.
Lemma lem3737496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737497 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term408 A y R x s) = (term409 A y R x s).
Proof. exact (MK_COMB (@lem3737496) (@lem3737495 A y R x s)). Qed.
Lemma lem3737498 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term404 A y s R x z) = (term362 A y z s R x).
Proof. exact (eq_refl (term404 A y s R x z)). Qed.
Lemma lem3737499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737500 {A : Type'} (y : A) (z : A) (s : A -> Prop) (R : type1402 A) (x : A) : (term410 A y s R x z) = (term411 A y z s R x).
Proof. exact (MK_COMB (@lem3737499) (@lem3737498 A y z s R x)). Qed.
Lemma lem3737501 {A : Type'} (s : A -> Prop) : (term128 A s) = (term128 A s).
Proof. exact (eq_refl (term128 A s)). Qed.
Lemma lem3737502 {A : Type'} (y : A) (z : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term412 A y R x z s) = (term413 A y z R x s).
Proof. exact (MK_COMB (@lem3737500 A y z s R x) (@lem3737501 A s)). Qed.
Lemma lem3737503 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term414 A y R x s) = (term415 A y R x s).
Proof. exact (fun_ext (fun z : A => @lem3737502 A y z R x s)). Qed.
Lemma lem3737504 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737505 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term403 A y R x s) = (term416 A y R x s).
Proof. exact (MK_COMB (@lem3737504 A) (@lem3737503 A y R x s)). Qed.
Lemma lem3737506 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : ((term402 A y R x s) = (term403 A y R x s)) = ((term398 A y R x s) = (term416 A y R x s)).
Proof. exact (MK_COMB (@lem3737497 A y R x s) (@lem3737505 A y R x s)). Qed.
Lemma lem3737507 {A : Type'} (y : A) (R : type1402 A) (x : A) (s : A -> Prop) : (term398 A y R x s) = (term416 A y R x s).
Proof. exact (EQ_MP (@lem3737506 A y R x s) (@lem3737487 A y R x s)). Qed.
Lemma lem3737508 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term400 A R x s) = (term417 A R x s).
Proof. exact (fun_ext (fun y : A => @lem3737507 A y R x s)). Qed.
Lemma lem3737509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737510 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term401 A R x s) = (term418 A R x s).
Proof. exact (MK_COMB (@lem3737509 A) (@lem3737508 A R x s)). Qed.
Lemma lem3737511 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term383 A R x s) = (term418 A R x s).
Proof. exact (TRANS (@lem3737483 A R x s) (@lem3737510 A R x s)). Qed.
Lemma lem3737512 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term385 A R s) = (term419 A R s).
Proof. exact (fun_ext (fun x : A => @lem3737511 A R x s)). Qed.
Lemma lem3737513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737514 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term386 A R s) = (term420 A R s).
Proof. exact (MK_COMB (@lem3737513 A) (@lem3737512 A R s)). Qed.
Lemma lem3737515 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term371 A R s) = (term420 A R s).
Proof. exact (TRANS (@lem3737459 A R s) (@lem3737514 A R s)). Qed.
Lemma lem3737516 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term262 A R s) = (term420 A R s).
Proof. exact (TRANS (@lem3737435 A R s) (@lem3737515 A R s)). Qed.
Lemma lem3737517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737518 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term263 A R s) = (term421 A R s).
Proof. exact (MK_COMB (@lem3737517) (@lem3737516 A R s)). Qed.
Lemma lem3737519 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737520 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term264 A R x s) = (term422 A R x s).
Proof. exact (MK_COMB (@lem3737518 A R s) (@lem3737519 A x s)). Qed.
Lemma lem3737522 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3737523 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (@lem3737522 A P Q). Qed.
Lemma lem3737524 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term425 A R x s) = (term426 A R x s).
Proof. exact (@lem3737523 A (term419 A R s) (term134 A x s)). Qed.
Lemma lem3737525 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term427 A R s x) = (term418 A R x s).
Proof. exact (eq_refl (term427 A R s x)). Qed.
Lemma lem3737526 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term428 A R s) = (term419 A R s).
Proof. exact (fun_ext (fun x : A => @lem3737525 A R x s)). Qed.
Lemma lem3737527 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737528 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term429 A R s) = (term420 A R s).
Proof. exact (MK_COMB (@lem3737527 A) (@lem3737526 A R s)). Qed.
Lemma lem3737529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737530 {A : Type'} (R : type1402 A) (s : A -> Prop) : (term430 A R s) = (term421 A R s).
Proof. exact (MK_COMB (@lem3737529) (@lem3737528 A R s)). Qed.
Lemma lem3737531 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737532 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term425 A R x s) = (term422 A R x s).
Proof. exact (MK_COMB (@lem3737530 A R s) (@lem3737531 A x s)). Qed.
Lemma lem3737533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737534 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term431 A R x s) = (term432 A R x s).
Proof. exact (MK_COMB (@lem3737533) (@lem3737532 A R x s)). Qed.
Lemma lem3737535 {A : Type'} (R : type1402 A) (x' : A) (s : A -> Prop) : (term427 A R s x') = (term418 A R x' s).
Proof. exact (eq_refl (term427 A R s x')). Qed.
Lemma lem3737536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737537 {A : Type'} (R : type1402 A) (x' : A) (s : A -> Prop) : (term433 A R s x') = (term434 A R x' s).
Proof. exact (MK_COMB (@lem3737536) (@lem3737535 A R x' s)). Qed.
Lemma lem3737538 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737539 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term435 A R x' x s) = (term436 A R x' x s).
Proof. exact (MK_COMB (@lem3737537 A R x' s) (@lem3737538 A x s)). Qed.
Lemma lem3737540 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term437 A R x s) = (term438 A R x s).
Proof. exact (fun_ext (fun x' : A => @lem3737539 A R x' x s)). Qed.
Lemma lem3737541 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737542 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term426 A R x s) = (term439 A R x s).
Proof. exact (MK_COMB (@lem3737541 A) (@lem3737540 A R x s)). Qed.
Lemma lem3737543 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : ((term425 A R x s) = (term426 A R x s)) = ((term422 A R x s) = (term439 A R x s)).
Proof. exact (MK_COMB (@lem3737534 A R x s) (@lem3737542 A R x s)). Qed.
Lemma lem3737544 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term422 A R x s) = (term439 A R x s).
Proof. exact (EQ_MP (@lem3737543 A R x s) (@lem3737524 A R x s)). Qed.
Lemma lem3737546 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3737547 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (@lem3737546 A P Q). Qed.
Lemma lem3737548 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term440 A R x' x s) = (term441 A R x' x s).
Proof. exact (@lem3737547 A (term417 A R x' s) (term134 A x s)). Qed.
Lemma lem3737549 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term442 A R x' s y) = (term416 A y R x' s).
Proof. exact (eq_refl (term442 A R x' s y)). Qed.
Lemma lem3737550 {A : Type'} (R : type1402 A) (x' : A) (s : A -> Prop) : (term443 A R x' s) = (term417 A R x' s).
Proof. exact (fun_ext (fun y : A => @lem3737549 A y R x' s)). Qed.
Lemma lem3737551 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737552 {A : Type'} (R : type1402 A) (x' : A) (s : A -> Prop) : (term444 A R x' s) = (term418 A R x' s).
Proof. exact (MK_COMB (@lem3737551 A) (@lem3737550 A R x' s)). Qed.
Lemma lem3737553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737554 {A : Type'} (R : type1402 A) (x' : A) (s : A -> Prop) : (term445 A R x' s) = (term434 A R x' s).
Proof. exact (MK_COMB (@lem3737553) (@lem3737552 A R x' s)). Qed.
Lemma lem3737555 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737556 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term440 A R x' x s) = (term436 A R x' x s).
Proof. exact (MK_COMB (@lem3737554 A R x' s) (@lem3737555 A x s)). Qed.
Lemma lem3737557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737558 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term446 A R x' x s) = (term447 A R x' x s).
Proof. exact (MK_COMB (@lem3737557) (@lem3737556 A R x' x s)). Qed.
Lemma lem3737559 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term442 A R x' s y) = (term416 A y R x' s).
Proof. exact (eq_refl (term442 A R x' s y)). Qed.
Lemma lem3737560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737561 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term448 A R x' s y) = (term449 A y R x' s).
Proof. exact (MK_COMB (@lem3737560) (@lem3737559 A y R x' s)). Qed.
Lemma lem3737562 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737563 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term450 A R x' y x s) = (term451 A y R x' x s).
Proof. exact (MK_COMB (@lem3737561 A y R x' s) (@lem3737562 A x s)). Qed.
Lemma lem3737564 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term452 A R x' x s) = (term453 A R x' x s).
Proof. exact (fun_ext (fun y : A => @lem3737563 A y R x' x s)). Qed.
Lemma lem3737565 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737566 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term441 A R x' x s) = (term454 A R x' x s).
Proof. exact (MK_COMB (@lem3737565 A) (@lem3737564 A R x' x s)). Qed.
Lemma lem3737567 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : ((term440 A R x' x s) = (term441 A R x' x s)) = ((term436 A R x' x s) = (term454 A R x' x s)).
Proof. exact (MK_COMB (@lem3737558 A R x' x s) (@lem3737566 A R x' x s)). Qed.
Lemma lem3737568 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term436 A R x' x s) = (term454 A R x' x s).
Proof. exact (EQ_MP (@lem3737567 A R x' x s) (@lem3737548 A R x' x s)). Qed.
Lemma lem3737570 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3737571 {A : Type'} (P : A -> Prop) (Q : Prop) : (term423 A P Q) = (term424 A P Q).
Proof. exact (@lem3737570 A P Q). Qed.
Lemma lem3737572 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term455 A y R x' x s) = (term456 A y R x' x s).
Proof. exact (@lem3737571 A (term415 A y R x' s) (term134 A x s)). Qed.
Lemma lem3737573 {A : Type'} (y : A) (z : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term457 A y R x' s z) = (term413 A y z R x' s).
Proof. exact (eq_refl (term457 A y R x' s z)). Qed.
Lemma lem3737574 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term458 A y R x' s) = (term415 A y R x' s).
Proof. exact (fun_ext (fun z : A => @lem3737573 A y z R x' s)). Qed.
Lemma lem3737575 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737576 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term459 A y R x' s) = (term416 A y R x' s).
Proof. exact (MK_COMB (@lem3737575 A) (@lem3737574 A y R x' s)). Qed.
Lemma lem3737577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737578 {A : Type'} (y : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term460 A y R x' s) = (term449 A y R x' s).
Proof. exact (MK_COMB (@lem3737577) (@lem3737576 A y R x' s)). Qed.
Lemma lem3737579 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737580 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term455 A y R x' x s) = (term451 A y R x' x s).
Proof. exact (MK_COMB (@lem3737578 A y R x' s) (@lem3737579 A x s)). Qed.
Lemma lem3737581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737582 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term461 A y R x' x s) = (term462 A y R x' x s).
Proof. exact (MK_COMB (@lem3737581) (@lem3737580 A y R x' x s)). Qed.
Lemma lem3737583 {A : Type'} (y : A) (z : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term457 A y R x' s z) = (term413 A y z R x' s).
Proof. exact (eq_refl (term457 A y R x' s z)). Qed.
Lemma lem3737584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737585 {A : Type'} (y : A) (z : A) (R : type1402 A) (x' : A) (s : A -> Prop) : (term463 A y R x' s z) = (term464 A y z R x' s).
Proof. exact (MK_COMB (@lem3737584) (@lem3737583 A y z R x' s)). Qed.
Lemma lem3737586 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term134 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3737587 {A : Type'} (y : A) (z : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term465 A y R x' z x s) = (term466 A y z R x' x s).
Proof. exact (MK_COMB (@lem3737585 A y z R x' s) (@lem3737586 A x s)). Qed.
Lemma lem3737588 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term467 A y R x' x s) = (term468 A y R x' x s).
Proof. exact (fun_ext (fun z : A => @lem3737587 A y z R x' x s)). Qed.
Lemma lem3737589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737590 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term456 A y R x' x s) = (term469 A y R x' x s).
Proof. exact (MK_COMB (@lem3737589 A) (@lem3737588 A y R x' x s)). Qed.
Lemma lem3737591 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : ((term455 A y R x' x s) = (term456 A y R x' x s)) = ((term451 A y R x' x s) = (term469 A y R x' x s)).
Proof. exact (MK_COMB (@lem3737582 A y R x' x s) (@lem3737590 A y R x' x s)). Qed.
Lemma lem3737592 {A : Type'} (y : A) (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term451 A y R x' x s) = (term469 A y R x' x s).
Proof. exact (EQ_MP (@lem3737591 A y R x' x s) (@lem3737572 A y R x' x s)). Qed.
Lemma lem3737593 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term453 A R x' x s) = (term470 A R x' x s).
Proof. exact (fun_ext (fun y : A => @lem3737592 A y R x' x s)). Qed.
Lemma lem3737594 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737595 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term454 A R x' x s) = (term471 A R x' x s).
Proof. exact (MK_COMB (@lem3737594 A) (@lem3737593 A R x' x s)). Qed.
Lemma lem3737596 {A : Type'} (R : type1402 A) (x' : A) (x : A) (s : A -> Prop) : (term436 A R x' x s) = (term471 A R x' x s).
Proof. exact (TRANS (@lem3737568 A R x' x s) (@lem3737595 A R x' x s)). Qed.
Lemma lem3737597 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term438 A R x s) = (term472 A R x s).
Proof. exact (fun_ext (fun x' : A => @lem3737596 A R x' x s)). Qed.
Lemma lem3737598 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737599 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term439 A R x s) = (term473 A R x s).
Proof. exact (MK_COMB (@lem3737598 A) (@lem3737597 A R x s)). Qed.
Lemma lem3737600 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term422 A R x s) = (term473 A R x s).
Proof. exact (TRANS (@lem3737544 A R x s) (@lem3737599 A R x s)). Qed.
Lemma lem3737602 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term264 A R x s) = (term473 A R x s).
Proof. exact (TRANS (@lem3737520 A R x s) (@lem3737600 A R x s)). Qed.
Lemma lem3737603 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : (term135 A R x s) = (term473 A R x s).
Proof. exact (TRANS (@lem3737129 A R x s) (@lem3737602 A R x s)). Qed.
Lemma lem3737604 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term135 A R x s) : term473 A R x s.
Proof. exact (EQ_MP (@lem3737603 A R x s) (@lem3737013 A R x s h1)). Qed.
Lemma lem3737605 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3737606 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3737605 A R x)). Qed.
Lemma lem3737607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737608 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3737607 A) (@lem3737606 A R)). Qed.
Lemma lem3737615 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term474 A x R y z) = (term475 A x R y z).
Proof. exact (@lem17045 (R x y) (R y z)). Qed.
Lemma lem3737616 {A : Type'} (R : type1402 A) (x : A) (z : A) : (R x z) = (R x z).
Proof. exact (eq_refl (R x z)). Qed.
Lemma lem3737617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737618 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term476 A x R y z) = (term477 A x R y z).
Proof. exact (MK_COMB (@lem3737617) (@lem3737615 A x R y z)). Qed.
Lemma lem3737619 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term478 A y R x z) = (term479 A y R x z).
Proof. exact (MK_COMB (@lem3737618 A x R y z) (@lem3737616 A R x z)). Qed.
Lemma lem3737620 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term186 A y R x z) = (term478 A y R x z).
Proof. exact (@lem17265 (term207 A x R y z) (R x z)). Qed.
Lemma lem3737621 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term186 A y R x z) = (term479 A y R x z).
Proof. exact (TRANS (@lem3737620 A y R x z) (@lem3737619 A y R x z)). Qed.
Lemma lem3737622 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term187 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3737621 A y R x z)). Qed.
Lemma lem3737623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737624 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term188 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3737623 A) (@lem3737622 A y R x)). Qed.
Lemma lem3737625 {A : Type'} (R : type1402 A) (x : A) : (term189 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3737624 A y R x)). Qed.
Lemma lem3737626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737627 {A : Type'} (R : type1402 A) (x : A) : (term190 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3737626 A) (@lem3737625 A R x)). Qed.
Lemma lem3737628 {A : Type'} (R : type1402 A) : (term191 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3737627 A R x)). Qed.
Lemma lem3737629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737630 {A : Type'} (R : type1402 A) : (term80 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3737629 A) (@lem3737628 A R)). Qed.
Lemma lem3737637 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term164 A x s x') = (term486 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3737646 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term146 A x s R x' y) = (term146 A x s R x' y).
Proof. exact (eq_refl (term146 A x s R x' y)). Qed.
Lemma lem3737647 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term148 A x s R x') = (term148 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3737646 A x s R x' y)). Qed.
Lemma lem3737648 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737649 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term150 A x s R x') = (term150 A x s R x').
Proof. exact (MK_COMB (@lem3737648 A) (@lem3737647 A x s R x')). Qed.
Lemma lem3737650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3737651 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term487 A x s x') = (term488 A x s x').
Proof. exact (MK_COMB (@lem3737650) (@lem3737637 A x s x')). Qed.
Lemma lem3737652 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term489 A x s R x') = (term490 A x s R x').
Proof. exact (MK_COMB (@lem3737651 A x s x') (@lem3737649 A x s R x')). Qed.
Lemma lem3737653 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term152 A x s R x') = (term489 A x s R x').
Proof. exact (@lem17265 (term140 A x s x') (term150 A x s R x')). Qed.
Lemma lem3737654 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term152 A x s R x') = (term490 A x s R x').
Proof. exact (TRANS (@lem3737653 A x s R x') (@lem3737652 A x s R x')). Qed.
Lemma lem3737655 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term154 A x s R) = (term491 A x s R).
Proof. exact (fun_ext (fun x' : A => @lem3737654 A x s R x')). Qed.
Lemma lem3737656 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737657 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term156 A x s R) = (term492 A x s R).
Proof. exact (MK_COMB (@lem3737656 A) (@lem3737655 A x s R)). Qed.
Lemma lem3737658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737659 {A : Type'} (R : type1402 A) : (term77 A R) = (term493 A R).
Proof. exact (MK_COMB (@lem3737658) (@lem3737630 A R)). Qed.
Lemma lem3737660 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term158 A x s R) = (term494 A x s R).
Proof. exact (MK_COMB (@lem3737659 A R) (@lem3737657 A x s R)). Qed.
Lemma lem3737661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737662 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (MK_COMB (@lem3737661) (@lem3737608 A R)). Qed.
Lemma lem3737663 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term160 A x s R) = (term495 A x s R).
Proof. exact (MK_COMB (@lem3737662 A R) (@lem3737660 A x s R)). Qed.
Lemma lem3737822 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3737823 {A : Type'} (P : Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem3737822 A P Q). Qed.
Lemma lem3737824 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term496 A x s R x') = (term497 A x s R x').
Proof. exact (@lem3737823 A (term486 A x s x') (term148 A x s R x')). Qed.
Lemma lem3737825 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term498 A x s R x' y) = (term146 A x s R x' y).
Proof. exact (eq_refl (term498 A x s R x' y)). Qed.
Lemma lem3737826 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term499 A x s R x') = (term148 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3737825 A x s R x' y)). Qed.
Lemma lem3737827 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737828 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term500 A x s R x') = (term150 A x s R x').
Proof. exact (MK_COMB (@lem3737827 A) (@lem3737826 A x s R x')). Qed.
Lemma lem3737829 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term488 A x s x') = (term488 A x s x').
Proof. exact (eq_refl (term488 A x s x')). Qed.
Lemma lem3737830 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term496 A x s R x') = (term490 A x s R x').
Proof. exact (MK_COMB (@lem3737829 A x s x') (@lem3737828 A x s R x')). Qed.
Lemma lem3737831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737832 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term501 A x s R x') = (term502 A x s R x').
Proof. exact (MK_COMB (@lem3737831) (@lem3737830 A x s R x')). Qed.
Lemma lem3737833 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term498 A x s R x' y) = (term146 A x s R x' y).
Proof. exact (eq_refl (term498 A x s R x' y)). Qed.
Lemma lem3737834 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term488 A x s x') = (term488 A x s x').
Proof. exact (eq_refl (term488 A x s x')). Qed.
Lemma lem3737835 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term503 A x s R x' y) = (term504 A x s R x' y).
Proof. exact (MK_COMB (@lem3737834 A x s x') (@lem3737833 A x s R x' y)). Qed.
Lemma lem3737836 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term505 A x s R x') = (term506 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3737835 A x s R x' y)). Qed.
Lemma lem3737837 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737838 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term497 A x s R x') = (term507 A x s R x').
Proof. exact (MK_COMB (@lem3737837 A) (@lem3737836 A x s R x')). Qed.
Lemma lem3737839 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : ((term496 A x s R x') = (term497 A x s R x')) = ((term490 A x s R x') = (term507 A x s R x')).
Proof. exact (MK_COMB (@lem3737832 A x s R x') (@lem3737838 A x s R x')). Qed.
Lemma lem3737840 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term490 A x s R x') = (term507 A x s R x').
Proof. exact (EQ_MP (@lem3737839 A x s R x') (@lem3737824 A x s R x')). Qed.
Lemma lem3737841 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term491 A x s R) = (term508 A x s R).
Proof. exact (fun_ext (fun x' : A => @lem3737840 A x s R x')). Qed.
Lemma lem3737842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737843 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term492 A x s R) = (term509 A x s R).
Proof. exact (MK_COMB (@lem3737842 A) (@lem3737841 A x s R)). Qed.
Lemma lem3737845 {A B : Type'} (P : type1413 A B) : (term510 A B P) = (term511 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3737846 {A : Type'} (P : type1402 A) : (term512 A P) = (term513 A P).
Proof. exact (@lem3737845 A A P). Qed.
Lemma lem3737847 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term514 A x s R) = (term515 A x s R).
Proof. exact (@lem3737846 A (term516 A x s R)). Qed.
Lemma lem3737848 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term517 A x s R x') = (term506 A x s R x').
Proof. exact (eq_refl (term517 A x s R x')). Qed.
Lemma lem3737849 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3737850 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term518 A x s R x' y) = (term519 A x s R x' y).
Proof. exact (MK_COMB (@lem3737848 A x s R x') (@lem3737849 A y)). Qed.
Lemma lem3737851 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term519 A x s R x' y) = (term504 A x s R x' y).
Proof. exact (eq_refl (term519 A x s R x' y)). Qed.
Lemma lem3737852 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) (y : A) : (term518 A x s R x' y) = (term504 A x s R x' y).
Proof. exact (TRANS (@lem3737850 A x s R x' y) (@lem3737851 A x s R x' y)). Qed.
Lemma lem3737853 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term520 A x s R x') = (term506 A x s R x').
Proof. exact (fun_ext (fun y : A => @lem3737852 A x s R x' y)). Qed.
Lemma lem3737854 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3737855 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term521 A x s R x') = (term507 A x s R x').
Proof. exact (MK_COMB (@lem3737854 A) (@lem3737853 A x s R x')). Qed.
Lemma lem3737856 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term522 A x s R) = (term508 A x s R).
Proof. exact (fun_ext (fun x' : A => @lem3737855 A x s R x')). Qed.
Lemma lem3737857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737858 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term514 A x s R) = (term509 A x s R).
Proof. exact (MK_COMB (@lem3737857 A) (@lem3737856 A x s R)). Qed.
Lemma lem3737859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737860 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term523 A x s R) = (term524 A x s R).
Proof. exact (MK_COMB (@lem3737859) (@lem3737858 A x s R)). Qed.
Lemma lem3737861 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (x' : A) : (term517 A x s R x') = (term506 A x s R x').
Proof. exact (eq_refl (term517 A x s R x')). Qed.
Lemma lem3737862 {A : Type'} (y : A -> A) (x' : A) : (y x') = (y x').
Proof. exact (eq_refl (y x')). Qed.
Lemma lem3737863 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term525 A x s R y x') = (term526 A x s R y x').
Proof. exact (MK_COMB (@lem3737861 A x s R x') (@lem3737862 A y x')). Qed.
Lemma lem3737864 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term526 A x s R y x') = (term527 A x s R y x').
Proof. exact (eq_refl (term526 A x s R y x')). Qed.
Lemma lem3737865 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term525 A x s R y x') = (term527 A x s R y x').
Proof. exact (TRANS (@lem3737863 A x s R y x') (@lem3737864 A x s R y x')). Qed.
Lemma lem3737866 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term528 A x s R y) = (term529 A x s R y).
Proof. exact (fun_ext (fun x' : A => @lem3737865 A x s R y x')). Qed.
Lemma lem3737867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3737868 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term530 A x s R y) = (term531 A x s R y).
Proof. exact (MK_COMB (@lem3737867 A) (@lem3737866 A x s R y)). Qed.
Lemma lem3737869 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term532 A x s R) = (term533 A x s R).
Proof. exact (fun_ext (fun y : A -> A => @lem3737868 A x s R y)). Qed.
Lemma lem3737870 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3737871 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term515 A x s R) = (term534 A x s R).
Proof. exact (MK_COMB (@lem3737870 A) (@lem3737869 A x s R)). Qed.
Lemma lem3737872 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : ((term514 A x s R) = (term515 A x s R)) = ((term509 A x s R) = (term534 A x s R)).
Proof. exact (MK_COMB (@lem3737860 A x s R) (@lem3737871 A x s R)). Qed.
Lemma lem3737873 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term509 A x s R) = (term534 A x s R).
Proof. exact (EQ_MP (@lem3737872 A x s R) (@lem3737847 A x s R)). Qed.
Lemma lem3737874 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term492 A x s R) = (term534 A x s R).
Proof. exact (TRANS (@lem3737843 A x s R) (@lem3737873 A x s R)). Qed.
Lemma lem3737875 {A : Type'} (R : type1402 A) : (term493 A R) = (term493 A R).
Proof. exact (eq_refl (term493 A R)). Qed.
Lemma lem3737876 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term494 A x s R) = (term535 A x s R).
Proof. exact (MK_COMB (@lem3737875 A R) (@lem3737874 A x s R)). Qed.
Lemma lem3737878 {A : Type'} (P : Prop) (Q : A -> Prop) : (term536 A P Q) = (term537 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3737879 {A : Type'} (P : Prop) (Q : type488 A) : (term538 A P Q) = (term539 A P Q).
Proof. exact (@lem3737878 (A -> A) P Q). Qed.
Lemma lem3737880 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term540 A x s R) = (term541 A x s R).
Proof. exact (@lem3737879 A (term485 A R) (term533 A x s R)). Qed.
Lemma lem3737881 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term542 A x s R y) = (term531 A x s R y).
Proof. exact (eq_refl (term542 A x s R y)). Qed.
Lemma lem3737882 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term543 A x s R) = (term533 A x s R).
Proof. exact (fun_ext (fun y : A -> A => @lem3737881 A x s R y)). Qed.
Lemma lem3737883 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3737884 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term544 A x s R) = (term534 A x s R).
Proof. exact (MK_COMB (@lem3737883 A) (@lem3737882 A x s R)). Qed.
Lemma lem3737885 {A : Type'} (R : type1402 A) : (term493 A R) = (term493 A R).
Proof. exact (eq_refl (term493 A R)). Qed.
Lemma lem3737886 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term540 A x s R) = (term535 A x s R).
Proof. exact (MK_COMB (@lem3737885 A R) (@lem3737884 A x s R)). Qed.
Lemma lem3737887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737888 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term545 A x s R) = (term546 A x s R).
Proof. exact (MK_COMB (@lem3737887) (@lem3737886 A x s R)). Qed.
Lemma lem3737889 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term542 A x s R y) = (term531 A x s R y).
Proof. exact (eq_refl (term542 A x s R y)). Qed.
Lemma lem3737890 {A : Type'} (R : type1402 A) : (term493 A R) = (term493 A R).
Proof. exact (eq_refl (term493 A R)). Qed.
Lemma lem3737891 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term547 A x s R y) = (term548 A x s R y).
Proof. exact (MK_COMB (@lem3737890 A R) (@lem3737889 A x s R y)). Qed.
Lemma lem3737892 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term549 A x s R) = (term550 A x s R).
Proof. exact (fun_ext (fun y : A -> A => @lem3737891 A x s R y)). Qed.
Lemma lem3737893 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3737894 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term541 A x s R) = (term551 A x s R).
Proof. exact (MK_COMB (@lem3737893 A) (@lem3737892 A x s R)). Qed.
Lemma lem3737895 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : ((term540 A x s R) = (term541 A x s R)) = ((term535 A x s R) = (term551 A x s R)).
Proof. exact (MK_COMB (@lem3737888 A x s R) (@lem3737894 A x s R)). Qed.
Lemma lem3737896 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term535 A x s R) = (term551 A x s R).
Proof. exact (EQ_MP (@lem3737895 A x s R) (@lem3737880 A x s R)). Qed.
Lemma lem3737897 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term494 A x s R) = (term551 A x s R).
Proof. exact (TRANS (@lem3737876 A x s R) (@lem3737896 A x s R)). Qed.
Lemma lem3737898 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3737899 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term495 A x s R) = (term552 A x s R).
Proof. exact (MK_COMB (@lem3737898 A R) (@lem3737897 A x s R)). Qed.
Lemma lem3737901 {A : Type'} (P : Prop) (Q : A -> Prop) : (term536 A P Q) = (term537 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3737902 {A : Type'} (P : Prop) (Q : type488 A) : (term538 A P Q) = (term539 A P Q).
Proof. exact (@lem3737901 (A -> A) P Q). Qed.
Lemma lem3737903 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term553 A x s R) = (term554 A x s R).
Proof. exact (@lem3737902 A (term194 A R) (term550 A x s R)). Qed.
Lemma lem3737904 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term555 A x s R y) = (term548 A x s R y).
Proof. exact (eq_refl (term555 A x s R y)). Qed.
Lemma lem3737905 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term556 A x s R) = (term550 A x s R).
Proof. exact (fun_ext (fun y : A -> A => @lem3737904 A x s R y)). Qed.
Lemma lem3737906 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3737907 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term557 A x s R) = (term551 A x s R).
Proof. exact (MK_COMB (@lem3737906 A) (@lem3737905 A x s R)). Qed.
Lemma lem3737908 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3737909 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term553 A x s R) = (term552 A x s R).
Proof. exact (MK_COMB (@lem3737908 A R) (@lem3737907 A x s R)). Qed.
Lemma lem3737910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3737911 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term558 A x s R) = (term559 A x s R).
Proof. exact (MK_COMB (@lem3737910) (@lem3737909 A x s R)). Qed.
Lemma lem3737912 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term555 A x s R y) = (term548 A x s R y).
Proof. exact (eq_refl (term555 A x s R y)). Qed.
Lemma lem3737913 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (eq_refl (term81 A R)). Qed.
Lemma lem3737914 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term560 A x s R y) = (term561 A x s R y).
Proof. exact (MK_COMB (@lem3737913 A R) (@lem3737912 A x s R y)). Qed.
Lemma lem3737915 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term562 A x s R) = (term563 A x s R).
Proof. exact (fun_ext (fun y : A -> A => @lem3737914 A x s R y)). Qed.
Lemma lem3737916 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3737917 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term554 A x s R) = (term564 A x s R).
Proof. exact (MK_COMB (@lem3737916 A) (@lem3737915 A x s R)). Qed.
Lemma lem3737918 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : ((term553 A x s R) = (term554 A x s R)) = ((term552 A x s R) = (term564 A x s R)).
Proof. exact (MK_COMB (@lem3737911 A x s R) (@lem3737917 A x s R)). Qed.
Lemma lem3737919 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term552 A x s R) = (term564 A x s R).
Proof. exact (EQ_MP (@lem3737918 A x s R) (@lem3737903 A x s R)). Qed.
Lemma lem3737921 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term495 A x s R) = (term564 A x s R).
Proof. exact (TRANS (@lem3737899 A x s R) (@lem3737919 A x s R)). Qed.
Lemma lem3737922 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) : (term160 A x s R) = (term564 A x s R).
Proof. exact (TRANS (@lem3737663 A x s R) (@lem3737921 A x s R)). Qed.
Lemma lem3737923 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (h1 : term160 A x s R) : term564 A x s R.
Proof. exact (EQ_MP (@lem3737922 A x s R) (@lem3737014 A x s R h1)). Qed.
Lemma lem3737933 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term140 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3737934 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term561 A x s R y.
Proof. exact (h1). Qed.
Lemma lem3737935 {A : Type'} (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (h1 : term471 A R x'' x s) : term471 A R x'' x s.
Proof. exact (h1). Qed.
Lemma lem3737936 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (h1 : term469 A y' R x'' x s) : term469 A y' R x'' x s.
Proof. exact (h1). Qed.
Lemma lem3737937 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (h1 : term466 A y' z R x'' x s) : term466 A y' z R x'' x s.
Proof. exact (h1). Qed.
Lemma lem3737942 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3737943 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3737942 A Prop f x). Qed.
Lemma lem3737945 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3737943 A s x'). Qed.
Lemma lem3737952 {A : Type'} (x' : A) (x : A) : (term139 A x' x) = (term139 A x' x).
Proof. exact (eq_refl (term139 A x' x)). Qed.
Lemma lem3737953 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term140 A x s x') = (term565 A x s x').
Proof. exact (MK_COMB (@lem3737952 A x' x) (@lem3737945 A s x')). Qed.
Lemma lem3737954 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term565 A x s x'.
Proof. exact (EQ_MP (@lem3737953 A x s x') (@lem3737933 A x s x' h1)). Qed.
Lemma lem3737961 {A : Type'} (R : type1402 A) (y : A -> A) (x' : A) : (term566 A R y x') = (term566 A R y x').
Proof. exact (eq_refl (term566 A R y x')). Qed.
Lemma lem3737968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3737969 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3737968 A Prop f x). Qed.
Lemma lem3737971 {A : Type'} (s : A -> Prop) (y : A -> A) (x' : A) : (term567 A s y x') = (term568 A s y x').
Proof. exact (@lem3737969 A s (y x')). Qed.
Lemma lem3737980 {A : Type'} (y : A -> A) (x' : A) (x : A) : (term569 A y x' x) = (term569 A y x' x).
Proof. exact (eq_refl (term569 A y x' x)). Qed.
Lemma lem3737981 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term570 A x s y x') = (term571 A x s y x').
Proof. exact (MK_COMB (@lem3737980 A y x' x) (@lem3737971 A s y x')). Qed.
Lemma lem3737982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3737983 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term572 A x s y x') = (term573 A x s y x').
Proof. exact (MK_COMB (@lem3737982) (@lem3737981 A x s y x')). Qed.
Lemma lem3737984 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term574 A x s R y x') = (term575 A x s R y x').
Proof. exact (MK_COMB (@lem3737983 A x s y x') (@lem3737961 A R y x')). Qed.
Lemma lem3737985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3737990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3737991 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3737990 A Prop f x). Qed.
Lemma lem3737993 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3737991 A s x'). Qed.
Lemma lem3737994 {A : Type'} (s : A -> Prop) (x' : A) : (term125 A s x') = (term576 A s x').
Proof. exact (MK_COMB (@lem3737985) (@lem3737993 A s x')). Qed.
Lemma lem3738003 {A : Type'} (x' : A) (x : A) : (term577 A x' x) = (term577 A x' x).
Proof. exact (eq_refl (term577 A x' x)). Qed.
Lemma lem3738004 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term486 A x s x') = (term578 A x s x').
Proof. exact (MK_COMB (@lem3738003 A x' x) (@lem3737994 A s x')). Qed.
Lemma lem3738005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3738006 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term488 A x s x') = (term579 A x s x').
Proof. exact (MK_COMB (@lem3738005) (@lem3738004 A x s x')). Qed.
Lemma lem3738007 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term527 A x s R y x') = (term580 A x s R y x').
Proof. exact (MK_COMB (@lem3738006 A x s x') (@lem3737984 A x s R y x')). Qed.
Lemma lem3738008 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term529 A x s R y) = (term581 A x s R y).
Proof. exact (fun_ext (fun x' : A => @lem3738007 A x s R y x')). Qed.
Lemma lem3738009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738010 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term531 A x s R y) = (term582 A x s R y).
Proof. exact (MK_COMB (@lem3738009 A) (@lem3738008 A x s R y)). Qed.
Lemma lem3738035 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term479 A y R x z) = (term479 A y R x z).
Proof. exact (eq_refl (term479 A y R x z)). Qed.
Lemma lem3738036 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term480 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3738035 A y R x z)). Qed.
Lemma lem3738037 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738038 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term481 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3738037 A) (@lem3738036 A y R x)). Qed.
Lemma lem3738039 {A : Type'} (R : type1402 A) (x : A) : (term482 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3738038 A y R x)). Qed.
Lemma lem3738040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738041 {A : Type'} (R : type1402 A) (x : A) : (term483 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3738040 A) (@lem3738039 A R x)). Qed.
Lemma lem3738042 {A : Type'} (R : type1402 A) : (term484 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3738041 A R x)). Qed.
Lemma lem3738043 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738044 {A : Type'} (R : type1402 A) : (term485 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3738043 A) (@lem3738042 A R)). Qed.
Lemma lem3738045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738046 {A : Type'} (R : type1402 A) : (term493 A R) = (term493 A R).
Proof. exact (MK_COMB (@lem3738045) (@lem3738044 A R)). Qed.
Lemma lem3738047 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term548 A x s R y) = (term583 A x s R y).
Proof. exact (MK_COMB (@lem3738046 A R) (@lem3738010 A x s R y)). Qed.
Lemma lem3738054 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738055 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738054 A R x)). Qed.
Lemma lem3738056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738057 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738056 A) (@lem3738055 A R)). Qed.
Lemma lem3738058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738059 {A : Type'} (R : type1402 A) : (term81 A R) = (term81 A R).
Proof. exact (MK_COMB (@lem3738058) (@lem3738057 A R)). Qed.
Lemma lem3738060 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term561 A x s R y) = (term584 A x s R y).
Proof. exact (MK_COMB (@lem3738059 A R) (@lem3738047 A x s R y)). Qed.
Lemma lem3738061 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term584 A x s R y.
Proof. exact (EQ_MP (@lem3738060 A x s R y) (@lem3737934 A x s R y h1)). Qed.
Lemma lem3738064 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3738065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3738070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3738071 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3738070 A Prop f x). Qed.
Lemma lem3738073 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3738071 A s x). Qed.
Lemma lem3738074 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term576 A s x).
Proof. exact (MK_COMB (@lem3738065) (@lem3738073 A s x)). Qed.
Lemma lem3738075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738076 {A : Type'} (s : A -> Prop) (x : A) : (term133 A s x) = (term585 A s x).
Proof. exact (MK_COMB (@lem3738075) (@lem3738074 A s x)). Qed.
Lemma lem3738077 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term586 A x s).
Proof. exact (MK_COMB (@lem3738076 A s x) (@lem3738064 A s)). Qed.
Lemma lem3738078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3738083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3738084 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3738083 A Prop f x). Qed.
Lemma lem3738086 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3738084 A s x). Qed.
Lemma lem3738087 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term576 A s x).
Proof. exact (MK_COMB (@lem3738078) (@lem3738086 A s x)). Qed.
Lemma lem3738088 {A : Type'} (s : A -> Prop) : (term127 A s) = (term587 A s).
Proof. exact (fun_ext (fun x : A => @lem3738087 A s x)). Qed.
Lemma lem3738089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738090 {A : Type'} (s : A -> Prop) : (term128 A s) = (term588 A s).
Proof. exact (MK_COMB (@lem3738089 A) (@lem3738088 A s)). Qed.
Lemma lem3738097 {A : Type'} (R : type1402 A) (x'' : A) (y : A) : (term589 A R x'' y) = (term589 A R x'' y).
Proof. exact (eq_refl (term589 A R x'' y)). Qed.
Lemma lem3738098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3738103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3738104 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3738103 A Prop f x). Qed.
Lemma lem3738106 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem3738104 A s y). Qed.
Lemma lem3738107 {A : Type'} (s : A -> Prop) (y : A) : (term125 A s y) = (term576 A s y).
Proof. exact (MK_COMB (@lem3738098) (@lem3738106 A s y)). Qed.
Lemma lem3738108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3738109 {A : Type'} (s : A -> Prop) (y : A) : (term590 A s y) = (term591 A s y).
Proof. exact (MK_COMB (@lem3738108) (@lem3738107 A s y)). Qed.
Lemma lem3738110 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (y : A) : (term230 A s R x'' y) = (term592 A s R x'' y).
Proof. exact (MK_COMB (@lem3738109 A s y) (@lem3738097 A R x'' y)). Qed.
Lemma lem3738111 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term237 A s R x'') = (term593 A s R x'').
Proof. exact (fun_ext (fun y : A => @lem3738110 A s R x'' y)). Qed.
Lemma lem3738112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738113 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term238 A s R x'') = (term594 A s R x'').
Proof. exact (MK_COMB (@lem3738112 A) (@lem3738111 A s R x'')). Qed.
Lemma lem3738118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3738119 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3738118 A Prop f x). Qed.
Lemma lem3738121 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3738119 A s x''). Qed.
Lemma lem3738122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738123 {A : Type'} (s : A -> Prop) (x'' : A) : (term106 A s x'') = (term595 A s x'').
Proof. exact (MK_COMB (@lem3738122) (@lem3738121 A s x'')). Qed.
Lemma lem3738124 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term240 A s R x'') = (term596 A s R x'').
Proof. exact (MK_COMB (@lem3738123 A s x'') (@lem3738113 A s R x'')). Qed.
Lemma lem3738149 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) : (term311 A y' R x'' z) = (term311 A y' R x'' z).
Proof. exact (eq_refl (term311 A y' R x'' z)). Qed.
Lemma lem3738150 {A : Type'} (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) : (term313 A y' z s R x'') = (term597 A y' z s R x'').
Proof. exact (MK_COMB (@lem3738149 A y' R x'' z) (@lem3738124 A s R x'')). Qed.
Lemma lem3738157 {A : Type'} (R : type1402 A) (x'' : A) : (term334 A R x'') = (term334 A R x'').
Proof. exact (eq_refl (term334 A R x'')). Qed.
Lemma lem3738158 {A : Type'} (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) : (term362 A y' z s R x'') = (term598 A y' z s R x'').
Proof. exact (MK_COMB (@lem3738157 A R x'') (@lem3738150 A y' z s R x'')). Qed.
Lemma lem3738159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3738160 {A : Type'} (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) : (term411 A y' z s R x'') = (term599 A y' z s R x'').
Proof. exact (MK_COMB (@lem3738159) (@lem3738158 A y' z s R x'')). Qed.
Lemma lem3738161 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (s : A -> Prop) : (term413 A y' z R x'' s) = (term600 A y' z R x'' s).
Proof. exact (MK_COMB (@lem3738160 A y' z s R x'') (@lem3738090 A s)). Qed.
Lemma lem3738162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738163 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (s : A -> Prop) : (term464 A y' z R x'' s) = (term601 A y' z R x'' s).
Proof. exact (MK_COMB (@lem3738162) (@lem3738161 A y' z R x'' s)). Qed.
Lemma lem3738164 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) : (term466 A y' z R x'' x s) = (term602 A y' z R x'' x s).
Proof. exact (MK_COMB (@lem3738163 A y' z R x'' s) (@lem3738077 A x s)). Qed.
Lemma lem3738165 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (h1 : term466 A y' z R x'' x s) : term602 A y' z R x'' x s.
Proof. exact (EQ_MP (@lem3738164 A y' z R x'' x s) (@lem3737937 A y' z R x'' x s h1)). Qed.
Lemma lem3738167 {A : Type'} (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (h1 : term466 A y' z R x'' x s) : term600 A y' z R x'' s.
Proof. exact (proj1 (@lem3738165 A y' z R x'' x s h1)). Qed.
Lemma lem3738170 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term583 A x s R y.
Proof. exact (proj2 (@lem3738061 A x s R y h1)). Qed.
Lemma lem3738171 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (proj1 (@lem3738061 A x s R y h1)). Qed.
Lemma lem3738172 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term582 A x s R y.
Proof. exact (proj2 (@lem3738170 A x s R y h1)). Qed.
Lemma lem3738173 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term485 A R.
Proof. exact (proj1 (@lem3738170 A x s R y h1)). Qed.
Lemma lem3738174 {A : Type'} (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term598 A y' z s R x'') : term598 A y' z s R x''.
Proof. exact (h1). Qed.
Lemma lem3738175 {A : Type'} (s : A -> Prop) (h1 : term588 A s) : term588 A s.
Proof. exact (h1). Qed.
Lemma lem3738177 {A : Type'} (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term597 A y' z s R x'') : term597 A y' z s R x''.
Proof. exact (h1). Qed.
Lemma lem3738180 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term206 A y' R x'' z.
Proof. exact (h1). Qed.
Lemma lem3738181 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term596 A s R x''.
Proof. exact (h1). Qed.
Lemma lem3738183 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term207 A x'' R y' z.
Proof. exact (proj1 (@lem3738180 A y' R x'' z h1)). Qed.
Lemma lem3738188 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term594 A s R x''.
Proof. exact (proj2 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3738203 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738204 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738203 A R x)). Qed.
Lemma lem3738205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738207 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738205 A) (@lem3738204 A R)). Qed.
Lemma lem3738208 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (EQ_MP (@lem3738207 A R) (@lem3738171 A x s R y h1)). Qed.
Lemma lem3738282 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3738296 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738297 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738296 A R x)). Qed.
Lemma lem3738298 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738300 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738298 A) (@lem3738297 A R)). Qed.
Lemma lem3738301 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (EQ_MP (@lem3738300 A R) (@lem3738171 A x s R y h1)). Qed.
Lemma lem3738375 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3738408 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term479 A y R x z) = (term479 A y R x z).
Proof. exact (eq_refl (term479 A y R x z)). Qed.
Lemma lem3738409 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term480 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3738408 A y R x z)). Qed.
Lemma lem3738410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738411 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term481 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3738410 A) (@lem3738409 A y R x)). Qed.
Lemma lem3738412 {A : Type'} (R : type1402 A) (x : A) : (term482 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3738411 A y R x)). Qed.
Lemma lem3738413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738414 {A : Type'} (R : type1402 A) (x : A) : (term483 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3738413 A) (@lem3738412 A R x)). Qed.
Lemma lem3738415 {A : Type'} (R : type1402 A) : (term484 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3738414 A R x)). Qed.
Lemma lem3738416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738418 {A : Type'} (R : type1402 A) : (term485 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3738416 A) (@lem3738415 A R)). Qed.
Lemma lem3738419 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term485 A R.
Proof. exact (EQ_MP (@lem3738418 A R) (@lem3738173 A x s R y h1)). Qed.
Lemma lem3738509 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term479 A y R x z) = (term479 A y R x z).
Proof. exact (eq_refl (term479 A y R x z)). Qed.
Lemma lem3738510 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term480 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3738509 A y R x z)). Qed.
Lemma lem3738511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738512 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term481 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3738511 A) (@lem3738510 A y R x)). Qed.
Lemma lem3738513 {A : Type'} (R : type1402 A) (x : A) : (term482 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3738512 A y R x)). Qed.
Lemma lem3738514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738515 {A : Type'} (R : type1402 A) (x : A) : (term483 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3738514 A) (@lem3738513 A R x)). Qed.
Lemma lem3738516 {A : Type'} (R : type1402 A) : (term484 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3738515 A R x)). Qed.
Lemma lem3738517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738519 {A : Type'} (R : type1402 A) : (term485 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3738517 A) (@lem3738516 A R)). Qed.
Lemma lem3738520 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term485 A R.
Proof. exact (EQ_MP (@lem3738519 A R) (@lem3738173 A x s R y h1)). Qed.
Lemma lem3738591 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738592 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738591 A R x)). Qed.
Lemma lem3738593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738595 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738593 A) (@lem3738592 A R)). Qed.
Lemma lem3738596 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (EQ_MP (@lem3738595 A R) (@lem3738171 A x s R y h1)). Qed.
Lemma lem3738610 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term479 A y R x z) = (term479 A y R x z).
Proof. exact (eq_refl (term479 A y R x z)). Qed.
Lemma lem3738611 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term480 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3738610 A y R x z)). Qed.
Lemma lem3738612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738613 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term481 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3738612 A) (@lem3738611 A y R x)). Qed.
Lemma lem3738614 {A : Type'} (R : type1402 A) (x : A) : (term482 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3738613 A y R x)). Qed.
Lemma lem3738615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738616 {A : Type'} (R : type1402 A) (x : A) : (term483 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3738615 A) (@lem3738614 A R x)). Qed.
Lemma lem3738617 {A : Type'} (R : type1402 A) : (term484 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3738616 A R x)). Qed.
Lemma lem3738618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738620 {A : Type'} (R : type1402 A) : (term485 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3738618 A) (@lem3738617 A R)). Qed.
Lemma lem3738621 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term485 A R.
Proof. exact (EQ_MP (@lem3738620 A R) (@lem3738173 A x s R y h1)). Qed.
Lemma lem3738642 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term603 A x s R y x').
Proof. exact (@lem19490 (term571 A x s y x') (term578 A x s x') (term566 A R y x')). Qed.
Lemma lem3738649 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term604 A x s R y x') = (term605 A x s R y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term566 A R y x')). Qed.
Lemma lem3738656 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term607 A x s y x') = (term608 A x s y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term571 A x s y x')). Qed.
Lemma lem3738657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738658 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term609 A x s y x') = (term610 A x s y x').
Proof. exact (MK_COMB (@lem3738657) (@lem3738656 A x s y x')). Qed.
Lemma lem3738659 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term603 A x s R y x') = (term611 A x s R y x').
Proof. exact (MK_COMB (@lem3738658 A x s y x') (@lem3738649 A x s R y x')). Qed.
Lemma lem3738661 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term611 A x s R y x').
Proof. exact (TRANS (@lem3738642 A x s R y x') (@lem3738659 A x s R y x')). Qed.
Lemma lem3738662 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term581 A x s R y) = (term612 A x s R y).
Proof. exact (fun_ext (fun x' : A => @lem3738661 A x s R y x')). Qed.
Lemma lem3738663 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738665 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term582 A x s R y) = (term613 A x s R y).
Proof. exact (MK_COMB (@lem3738663 A) (@lem3738662 A x s R y)). Qed.
Lemma lem3738666 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term613 A x s R y.
Proof. exact (EQ_MP (@lem3738665 A x s R y) (@lem3738172 A x s R y h1)). Qed.
Lemma lem3738678 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (y : A) : (term592 A s R x'' y) = (term592 A s R x'' y).
Proof. exact (eq_refl (term592 A s R x'' y)). Qed.
Lemma lem3738679 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term593 A s R x'') = (term593 A s R x'').
Proof. exact (fun_ext (fun y : A => @lem3738678 A s R x'' y)). Qed.
Lemma lem3738680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738682 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term594 A s R x'') = (term594 A s R x'').
Proof. exact (MK_COMB (@lem3738680 A) (@lem3738679 A s R x'')). Qed.
Lemma lem3738683 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term594 A s R x''.
Proof. exact (EQ_MP (@lem3738682 A s R x'') (@lem3738188 A s R x'' h1)). Qed.
Lemma lem3738697 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738698 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738697 A R x)). Qed.
Lemma lem3738699 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738701 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738699 A) (@lem3738698 A R)). Qed.
Lemma lem3738702 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (EQ_MP (@lem3738701 A R) (@lem3738171 A x s R y h1)). Qed.
Lemma lem3738716 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term479 A y R x z) = (term479 A y R x z).
Proof. exact (eq_refl (term479 A y R x z)). Qed.
Lemma lem3738717 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term480 A y R x) = (term480 A y R x).
Proof. exact (fun_ext (fun z : A => @lem3738716 A y R x z)). Qed.
Lemma lem3738718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738719 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term481 A y R x) = (term481 A y R x).
Proof. exact (MK_COMB (@lem3738718 A) (@lem3738717 A y R x)). Qed.
Lemma lem3738720 {A : Type'} (R : type1402 A) (x : A) : (term482 A R x) = (term482 A R x).
Proof. exact (fun_ext (fun y : A => @lem3738719 A y R x)). Qed.
Lemma lem3738721 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738722 {A : Type'} (R : type1402 A) (x : A) : (term483 A R x) = (term483 A R x).
Proof. exact (MK_COMB (@lem3738721 A) (@lem3738720 A R x)). Qed.
Lemma lem3738723 {A : Type'} (R : type1402 A) : (term484 A R) = (term484 A R).
Proof. exact (fun_ext (fun x : A => @lem3738722 A R x)). Qed.
Lemma lem3738724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738726 {A : Type'} (R : type1402 A) : (term485 A R) = (term485 A R).
Proof. exact (MK_COMB (@lem3738724 A) (@lem3738723 A R)). Qed.
Lemma lem3738727 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term485 A R.
Proof. exact (EQ_MP (@lem3738726 A R) (@lem3738173 A x s R y h1)). Qed.
Lemma lem3738748 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term603 A x s R y x').
Proof. exact (@lem19490 (term571 A x s y x') (term578 A x s x') (term566 A R y x')). Qed.
Lemma lem3738755 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term604 A x s R y x') = (term605 A x s R y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term566 A R y x')). Qed.
Lemma lem3738762 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term607 A x s y x') = (term608 A x s y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term571 A x s y x')). Qed.
Lemma lem3738763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738764 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term609 A x s y x') = (term610 A x s y x').
Proof. exact (MK_COMB (@lem3738763) (@lem3738762 A x s y x')). Qed.
Lemma lem3738765 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term603 A x s R y x') = (term611 A x s R y x').
Proof. exact (MK_COMB (@lem3738764 A x s y x') (@lem3738755 A x s R y x')). Qed.
Lemma lem3738767 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term611 A x s R y x').
Proof. exact (TRANS (@lem3738748 A x s R y x') (@lem3738765 A x s R y x')). Qed.
Lemma lem3738768 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term581 A x s R y) = (term612 A x s R y).
Proof. exact (fun_ext (fun x' : A => @lem3738767 A x s R y x')). Qed.
Lemma lem3738769 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738771 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term582 A x s R y) = (term613 A x s R y).
Proof. exact (MK_COMB (@lem3738769 A) (@lem3738768 A x s R y)). Qed.
Lemma lem3738772 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term613 A x s R y.
Proof. exact (EQ_MP (@lem3738771 A x s R y) (@lem3738172 A x s R y h1)). Qed.
Lemma lem3738784 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (y : A) : (term592 A s R x'' y) = (term592 A s R x'' y).
Proof. exact (eq_refl (term592 A s R x'' y)). Qed.
Lemma lem3738785 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term593 A s R x'') = (term593 A s R x'').
Proof. exact (fun_ext (fun y : A => @lem3738784 A s R x'' y)). Qed.
Lemma lem3738786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738788 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) : (term594 A s R x'') = (term594 A s R x'').
Proof. exact (MK_COMB (@lem3738786 A) (@lem3738785 A s R x'')). Qed.
Lemma lem3738789 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term594 A s R x''.
Proof. exact (EQ_MP (@lem3738788 A s R x'') (@lem3738188 A s R x'' h1)). Qed.
Lemma lem3738803 {A : Type'} (R : type1402 A) (x : A) : (term192 A R x) = (term192 A R x).
Proof. exact (eq_refl (term192 A R x)). Qed.
Lemma lem3738804 {A : Type'} (R : type1402 A) : (term193 A R) = (term193 A R).
Proof. exact (fun_ext (fun x : A => @lem3738803 A R x)). Qed.
Lemma lem3738805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738807 {A : Type'} (R : type1402 A) : (term194 A R) = (term194 A R).
Proof. exact (MK_COMB (@lem3738805 A) (@lem3738804 A R)). Qed.
Lemma lem3738808 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term194 A R.
Proof. exact (EQ_MP (@lem3738807 A R) (@lem3738171 A x s R y h1)). Qed.
Lemma lem3738854 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term603 A x s R y x').
Proof. exact (@lem19490 (term571 A x s y x') (term578 A x s x') (term566 A R y x')). Qed.
Lemma lem3738861 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term604 A x s R y x') = (term605 A x s R y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term566 A R y x')). Qed.
Lemma lem3738868 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term607 A x s y x') = (term608 A x s y x').
Proof. exact (@lem19699 (term606 A x' x) (term576 A s x') (term571 A x s y x')). Qed.
Lemma lem3738869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3738870 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (x' : A) : (term609 A x s y x') = (term610 A x s y x').
Proof. exact (MK_COMB (@lem3738869) (@lem3738868 A x s y x')). Qed.
Lemma lem3738871 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term603 A x s R y x') = (term611 A x s R y x').
Proof. exact (MK_COMB (@lem3738870 A x s y x') (@lem3738861 A x s R y x')). Qed.
Lemma lem3738873 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (x' : A) : (term580 A x s R y x') = (term611 A x s R y x').
Proof. exact (TRANS (@lem3738854 A x s R y x') (@lem3738871 A x s R y x')). Qed.
Lemma lem3738874 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term581 A x s R y) = (term612 A x s R y).
Proof. exact (fun_ext (fun x' : A => @lem3738873 A x s R y x')). Qed.
Lemma lem3738875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738877 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) : (term582 A x s R y) = (term613 A x s R y).
Proof. exact (MK_COMB (@lem3738875 A) (@lem3738874 A x s R y)). Qed.
Lemma lem3738878 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term613 A x s R y.
Proof. exact (EQ_MP (@lem3738877 A x s R y) (@lem3738172 A x s R y h1)). Qed.
Lemma lem3738880 {A : Type'} (s : A -> Prop) (x : A) : (term576 A s x) = (term576 A s x).
Proof. exact (eq_refl (term576 A s x)). Qed.
Lemma lem3738881 {A : Type'} (s : A -> Prop) : (term587 A s) = (term587 A s).
Proof. exact (fun_ext (fun x : A => @lem3738880 A s x)). Qed.
Lemma lem3738882 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738884 {A : Type'} (s : A -> Prop) : (term588 A s) = (term588 A s).
Proof. exact (MK_COMB (@lem3738882 A) (@lem3738881 A s)). Qed.
Lemma lem3738885 {A : Type'} (s : A -> Prop) (h1 : term588 A s) : term588 A s.
Proof. exact (EQ_MP (@lem3738884 A s) (@lem3738175 A s h1)). Qed.
Lemma lem3738976 {A : Type'} (s : A -> Prop) (x : A) : (term576 A s x) = (term576 A s x).
Proof. exact (eq_refl (term576 A s x)). Qed.
Lemma lem3738977 {A : Type'} (s : A -> Prop) : (term587 A s) = (term587 A s).
Proof. exact (fun_ext (fun x : A => @lem3738976 A s x)). Qed.
Lemma lem3738978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3738980 {A : Type'} (s : A -> Prop) : (term588 A s) = (term588 A s).
Proof. exact (MK_COMB (@lem3738978 A) (@lem3738977 A s)). Qed.
Lemma lem3738981 {A : Type'} (s : A -> Prop) (h1 : term588 A s) : term588 A s.
Proof. exact (EQ_MP (@lem3738980 A s) (@lem3738175 A s h1)). Qed.
Lemma lem3738985 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3738986 {A : Type'} (_42891 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term200 A R _42891.
Proof. exact (@lem3738208 A x s R y h1 _42891). Qed.
Lemma lem3738987 {A : Type'} (R : type1402 A) (_42891 : A) : (term200 A R _42891) = (term192 A R _42891).
Proof. exact (eq_refl (term200 A R _42891)). Qed.
Lemma lem3739001 {A : Type'} (_42896 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term200 A R _42896.
Proof. exact (@lem3738301 A x s R y h1 _42896). Qed.
Lemma lem3739002 {A : Type'} (R : type1402 A) (_42896 : A) : (term200 A R _42896) = (term192 A R _42896).
Proof. exact (eq_refl (term200 A R _42896)). Qed.
Lemma lem3739019 {A : Type'} (_42902 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term614 A R _42902.
Proof. exact (@lem3738419 A x s R y h1 _42902). Qed.
Lemma lem3739020 {A : Type'} (R : type1402 A) (_42902 : A) : (term614 A R _42902) = (term483 A R _42902).
Proof. exact (eq_refl (term614 A R _42902)). Qed.
Lemma lem3739021 {A : Type'} (_42902 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term483 A R _42902.
Proof. exact (EQ_MP (@lem3739020 A R _42902) (@lem3739019 A _42902 x s R y h1)). Qed.
Lemma lem3739022 {A : Type'} (_42902 : A) (_42903 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term615 A R _42902 _42903.
Proof. exact (@lem3739021 A _42902 x s R y h1 _42903). Qed.
Lemma lem3739023 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) : (term615 A R _42902 _42903) = (term481 A _42903 R _42902).
Proof. exact (eq_refl (term615 A R _42902 _42903)). Qed.
Lemma lem3739024 {A : Type'} (_42903 : A) (_42902 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term481 A _42903 R _42902.
Proof. exact (EQ_MP (@lem3739023 A _42903 R _42902) (@lem3739022 A _42902 _42903 x s R y h1)). Qed.
Lemma lem3739025 {A : Type'} (_42903 : A) (_42902 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term616 A _42903 R _42902 _42904.
Proof. exact (@lem3739024 A _42903 _42902 x s R y h1 _42904). Qed.
Lemma lem3739026 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) (_42904 : A) : (term616 A _42903 R _42902 _42904) = (term479 A _42903 R _42902 _42904).
Proof. exact (eq_refl (term616 A _42903 R _42902 _42904)). Qed.
Lemma lem3739027 {A : Type'} (_42903 : A) (_42902 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term479 A _42903 R _42902 _42904.
Proof. exact (EQ_MP (@lem3739026 A _42903 R _42902 _42904) (@lem3739025 A _42903 _42902 _42904 x s R y h1)). Qed.
Lemma lem3739034 {A : Type'} (_42907 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term614 A R _42907.
Proof. exact (@lem3738520 A x s R y h1 _42907). Qed.
Lemma lem3739035 {A : Type'} (R : type1402 A) (_42907 : A) : (term614 A R _42907) = (term483 A R _42907).
Proof. exact (eq_refl (term614 A R _42907)). Qed.
Lemma lem3739036 {A : Type'} (_42907 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term483 A R _42907.
Proof. exact (EQ_MP (@lem3739035 A R _42907) (@lem3739034 A _42907 x s R y h1)). Qed.
Lemma lem3739037 {A : Type'} (_42907 : A) (_42908 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term615 A R _42907 _42908.
Proof. exact (@lem3739036 A _42907 x s R y h1 _42908). Qed.
Lemma lem3739038 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) : (term615 A R _42907 _42908) = (term481 A _42908 R _42907).
Proof. exact (eq_refl (term615 A R _42907 _42908)). Qed.
Lemma lem3739039 {A : Type'} (_42908 : A) (_42907 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term481 A _42908 R _42907.
Proof. exact (EQ_MP (@lem3739038 A _42908 R _42907) (@lem3739037 A _42907 _42908 x s R y h1)). Qed.
Lemma lem3739040 {A : Type'} (_42908 : A) (_42907 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term616 A _42908 R _42907 _42909.
Proof. exact (@lem3739039 A _42908 _42907 x s R y h1 _42909). Qed.
Lemma lem3739041 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) (_42909 : A) : (term616 A _42908 R _42907 _42909) = (term479 A _42908 R _42907 _42909).
Proof. exact (eq_refl (term616 A _42908 R _42907 _42909)). Qed.
Lemma lem3739042 {A : Type'} (_42908 : A) (_42907 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term479 A _42908 R _42907 _42909.
Proof. exact (EQ_MP (@lem3739041 A _42908 R _42907 _42909) (@lem3739040 A _42908 _42907 _42909 x s R y h1)). Qed.
Lemma lem3739046 {A : Type'} (_42911 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term200 A R _42911.
Proof. exact (@lem3738596 A x s R y h1 _42911). Qed.
Lemma lem3739047 {A : Type'} (R : type1402 A) (_42911 : A) : (term200 A R _42911) = (term192 A R _42911).
Proof. exact (eq_refl (term200 A R _42911)). Qed.
Lemma lem3739049 {A : Type'} (_42912 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term614 A R _42912.
Proof. exact (@lem3738621 A x s R y h1 _42912). Qed.
Lemma lem3739050 {A : Type'} (R : type1402 A) (_42912 : A) : (term614 A R _42912) = (term483 A R _42912).
Proof. exact (eq_refl (term614 A R _42912)). Qed.
Lemma lem3739051 {A : Type'} (_42912 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term483 A R _42912.
Proof. exact (EQ_MP (@lem3739050 A R _42912) (@lem3739049 A _42912 x s R y h1)). Qed.
Lemma lem3739052 {A : Type'} (_42912 : A) (_42913 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term615 A R _42912 _42913.
Proof. exact (@lem3739051 A _42912 x s R y h1 _42913). Qed.
Lemma lem3739053 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) : (term615 A R _42912 _42913) = (term481 A _42913 R _42912).
Proof. exact (eq_refl (term615 A R _42912 _42913)). Qed.
Lemma lem3739054 {A : Type'} (_42913 : A) (_42912 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term481 A _42913 R _42912.
Proof. exact (EQ_MP (@lem3739053 A _42913 R _42912) (@lem3739052 A _42912 _42913 x s R y h1)). Qed.
Lemma lem3739055 {A : Type'} (_42913 : A) (_42912 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term616 A _42913 R _42912 _42914.
Proof. exact (@lem3739054 A _42913 _42912 x s R y h1 _42914). Qed.
Lemma lem3739056 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) (_42914 : A) : (term616 A _42913 R _42912 _42914) = (term479 A _42913 R _42912 _42914).
Proof. exact (eq_refl (term616 A _42913 R _42912 _42914)). Qed.
Lemma lem3739057 {A : Type'} (_42913 : A) (_42912 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term479 A _42913 R _42912 _42914.
Proof. exact (EQ_MP (@lem3739056 A _42913 R _42912 _42914) (@lem3739055 A _42913 _42912 _42914 x s R y h1)). Qed.
Lemma lem3739058 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term617 A x s R y _42915.
Proof. exact (@lem3738666 A x s R y h1 _42915). Qed.
Lemma lem3739059 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42915 : A) : (term617 A x s R y _42915) = (term611 A x s R y _42915).
Proof. exact (eq_refl (term617 A x s R y _42915)). Qed.
Lemma lem3739060 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term611 A x s R y _42915.
Proof. exact (EQ_MP (@lem3739059 A x s R y _42915) (@lem3739058 A _42915 x s R y h1)). Qed.
Lemma lem3739061 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term618 A s R x'' _42916.
Proof. exact (@lem3738683 A s R x'' h1 _42916). Qed.
Lemma lem3739062 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (_42916 : A) : (term618 A s R x'' _42916) = (term592 A s R x'' _42916).
Proof. exact (eq_refl (term618 A s R x'' _42916)). Qed.
Lemma lem3739064 {A : Type'} (_42917 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term200 A R _42917.
Proof. exact (@lem3738702 A x s R y h1 _42917). Qed.
Lemma lem3739065 {A : Type'} (R : type1402 A) (_42917 : A) : (term200 A R _42917) = (term192 A R _42917).
Proof. exact (eq_refl (term200 A R _42917)). Qed.
Lemma lem3739067 {A : Type'} (_42918 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term614 A R _42918.
Proof. exact (@lem3738727 A x s R y h1 _42918). Qed.
Lemma lem3739068 {A : Type'} (R : type1402 A) (_42918 : A) : (term614 A R _42918) = (term483 A R _42918).
Proof. exact (eq_refl (term614 A R _42918)). Qed.
Lemma lem3739069 {A : Type'} (_42918 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term483 A R _42918.
Proof. exact (EQ_MP (@lem3739068 A R _42918) (@lem3739067 A _42918 x s R y h1)). Qed.
Lemma lem3739070 {A : Type'} (_42918 : A) (_42919 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term615 A R _42918 _42919.
Proof. exact (@lem3739069 A _42918 x s R y h1 _42919). Qed.
Lemma lem3739071 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) : (term615 A R _42918 _42919) = (term481 A _42919 R _42918).
Proof. exact (eq_refl (term615 A R _42918 _42919)). Qed.
Lemma lem3739072 {A : Type'} (_42919 : A) (_42918 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term481 A _42919 R _42918.
Proof. exact (EQ_MP (@lem3739071 A _42919 R _42918) (@lem3739070 A _42918 _42919 x s R y h1)). Qed.
Lemma lem3739073 {A : Type'} (_42919 : A) (_42918 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term616 A _42919 R _42918 _42920.
Proof. exact (@lem3739072 A _42919 _42918 x s R y h1 _42920). Qed.
Lemma lem3739074 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) (_42920 : A) : (term616 A _42919 R _42918 _42920) = (term479 A _42919 R _42918 _42920).
Proof. exact (eq_refl (term616 A _42919 R _42918 _42920)). Qed.
Lemma lem3739075 {A : Type'} (_42919 : A) (_42918 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term479 A _42919 R _42918 _42920.
Proof. exact (EQ_MP (@lem3739074 A _42919 R _42918 _42920) (@lem3739073 A _42919 _42918 _42920 x s R y h1)). Qed.
Lemma lem3739076 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term617 A x s R y _42921.
Proof. exact (@lem3738772 A x s R y h1 _42921). Qed.
Lemma lem3739077 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42921 : A) : (term617 A x s R y _42921) = (term611 A x s R y _42921).
Proof. exact (eq_refl (term617 A x s R y _42921)). Qed.
Lemma lem3739078 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term611 A x s R y _42921.
Proof. exact (EQ_MP (@lem3739077 A x s R y _42921) (@lem3739076 A _42921 x s R y h1)). Qed.
Lemma lem3739079 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term618 A s R x'' _42922.
Proof. exact (@lem3738789 A s R x'' h1 _42922). Qed.
Lemma lem3739080 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (_42922 : A) : (term618 A s R x'' _42922) = (term592 A s R x'' _42922).
Proof. exact (eq_refl (term618 A s R x'' _42922)). Qed.
Lemma lem3739082 {A : Type'} (_42923 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term200 A R _42923.
Proof. exact (@lem3738808 A x s R y h1 _42923). Qed.
Lemma lem3739083 {A : Type'} (R : type1402 A) (_42923 : A) : (term200 A R _42923) = (term192 A R _42923).
Proof. exact (eq_refl (term200 A R _42923)). Qed.
Lemma lem3739094 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term617 A x s R y _42927.
Proof. exact (@lem3738878 A x s R y h1 _42927). Qed.
Lemma lem3739095 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42927 : A) : (term617 A x s R y _42927) = (term611 A x s R y _42927).
Proof. exact (eq_refl (term617 A x s R y _42927)). Qed.
Lemma lem3739096 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term611 A x s R y _42927.
Proof. exact (EQ_MP (@lem3739095 A x s R y _42927) (@lem3739094 A _42927 x s R y h1)). Qed.
Lemma lem3739097 {A : Type'} (_42928 : A) (s : A -> Prop) (h1 : term588 A s) : term619 A s _42928.
Proof. exact (@lem3738885 A s h1 _42928). Qed.
Lemma lem3739098 {A : Type'} (s : A -> Prop) (_42928 : A) : (term619 A s _42928) = (term576 A s _42928).
Proof. exact (eq_refl (term619 A s _42928)). Qed.
Lemma lem3739115 {A : Type'} (_42934 : A) (s : A -> Prop) (h1 : term588 A s) : term619 A s _42934.
Proof. exact (@lem3738981 A s h1 _42934). Qed.
Lemma lem3739116 {A : Type'} (s : A -> Prop) (_42934 : A) : (term619 A s _42934) = (term576 A s _42934).
Proof. exact (eq_refl (term619 A s _42934)). Qed.
Lemma lem3739142 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term605 A x s R y _42915.
Proof. exact (proj2 (@lem3739060 A _42915 x s R y h1)). Qed.
Lemma lem3739143 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term608 A x s y _42915.
Proof. exact (proj1 (@lem3739060 A _42915 x s R y h1)). Qed.
Lemma lem3739148 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term605 A x s R y _42921.
Proof. exact (proj2 (@lem3739078 A _42921 x s R y h1)). Qed.
Lemma lem3739149 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term608 A x s y _42921.
Proof. exact (proj1 (@lem3739078 A _42921 x s R y h1)). Qed.
Lemma lem3739154 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term605 A x s R y _42927.
Proof. exact (proj2 (@lem3739096 A _42927 x s R y h1)). Qed.
Lemma lem3739155 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term608 A x s y _42927.
Proof. exact (proj1 (@lem3739096 A _42927 x s R y h1)). Qed.
Lemma lem3739185 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3739225 {A : Type'} (_42896 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42896.
Proof. exact (EQ_MP (@lem3739002 A R _42896) (@lem3739001 A _42896 x s R y h1)). Qed.
Lemma lem3739239 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3739290 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) (_42904 : A) : (term479 A _42903 R _42902 _42904) = (term620 A _42903 R _42902 _42904).
Proof. exact (@lem3735663 (term589 A R _42902 _42903) (term589 A R _42903 _42904) (R _42902 _42904)). Qed.
Lemma lem3739348 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) (_42909 : A) : (term479 A _42908 R _42907 _42909) = (term620 A _42908 R _42907 _42909).
Proof. exact (@lem3735663 (term589 A R _42907 _42908) (term589 A R _42908 _42909) (R _42907 _42909)). Qed.
Lemma lem3739349 {A : Type'} (_42908 : A) (_42907 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term620 A _42908 R _42907 _42909.
Proof. exact (EQ_MP (@lem3739348 A _42908 R _42907 _42909) (@lem3739042 A _42908 _42907 _42909 x s R y h1)). Qed.
Lemma lem3739351 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term589 A R x'' z.
Proof. exact (proj2 (@lem3738180 A y' R x'' z h1)). Qed.
Lemma lem3739406 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) (_42914 : A) : (term479 A _42913 R _42912 _42914) = (term620 A _42913 R _42912 _42914).
Proof. exact (@lem3735663 (term589 A R _42912 _42913) (term589 A R _42913 _42914) (R _42912 _42914)). Qed.
Lemma lem3739455 {A : Type'} (_42917 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42917.
Proof. exact (EQ_MP (@lem3739065 A R _42917) (@lem3739064 A _42917 x s R y h1)). Qed.
Lemma lem3739466 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) (_42920 : A) : (term479 A _42919 R _42918 _42920) = (term620 A _42919 R _42918 _42920).
Proof. exact (@lem3735663 (term589 A R _42918 _42919) (term589 A R _42919 _42920) (R _42918 _42920)). Qed.
Lemma lem3739467 {A : Type'} (_42919 : A) (_42918 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term620 A _42919 R _42918 _42920.
Proof. exact (EQ_MP (@lem3739466 A _42919 R _42918 _42920) (@lem3739075 A _42919 _42918 _42920 x s R y h1)). Qed.
Lemma lem3739475 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term592 A s R x'' _42922.
Proof. exact (EQ_MP (@lem3739080 A s R x'' _42922) (@lem3739079 A _42922 s R x'' h1)). Qed.
Lemma lem3739483 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term621 A x R y _42921.
Proof. exact (proj1 (@lem3739148 A _42921 x s R y h1)). Qed.
Lemma lem3739489 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term622 A s R y _42921.
Proof. exact (proj2 (@lem3739148 A _42921 x s R y h1)). Qed.
Lemma lem3739499 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term623 A x s y _42921.
Proof. exact (proj1 (@lem3739149 A _42921 x s R y h1)). Qed.
Lemma lem3739509 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term624 A x s y _42921.
Proof. exact (proj2 (@lem3739149 A _42921 x s R y h1)). Qed.
Lemma lem3739583 {A : Type'} (_42934 : A) (s : A -> Prop) (h1 : term588 A s) : term576 A s _42934.
Proof. exact (EQ_MP (@lem3739116 A s _42934) (@lem3739115 A _42934 s h1)). Qed.
Lemma lem3739585 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3739673 {A : Type'} (_42891 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42891.
Proof. exact (EQ_MP (@lem3738987 A R _42891) (@lem3738986 A _42891 x s R y h1)). Qed.
Lemma lem3739701 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3739827 {A : Type'} (_42903 : A) (_42902 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term620 A _42903 R _42902 _42904.
Proof. exact (EQ_MP (@lem3739290 A _42903 R _42902 _42904) (@lem3739027 A _42903 _42902 _42904 x s R y h1)). Qed.
Lemma lem3739841 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term589 A R x'' z.
Proof. exact (proj2 (@lem3738180 A y' R x'' z h1)). Qed.
Lemma lem3739981 {A : Type'} (_42911 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42911.
Proof. exact (EQ_MP (@lem3739047 A R _42911) (@lem3739046 A _42911 x s R y h1)). Qed.
Lemma lem3739995 {A : Type'} (_42913 : A) (_42912 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term620 A _42913 R _42912 _42914.
Proof. exact (EQ_MP (@lem3739406 A _42913 R _42912 _42914) (@lem3739057 A _42913 _42912 _42914 x s R y h1)). Qed.
Lemma lem3740023 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term592 A s R x'' _42916.
Proof. exact (EQ_MP (@lem3739062 A s R x'' _42916) (@lem3739061 A _42916 s R x'' h1)). Qed.
Lemma lem3740037 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term621 A x R y _42915.
Proof. exact (proj1 (@lem3739142 A _42915 x s R y h1)). Qed.
Lemma lem3740051 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term622 A s R y _42915.
Proof. exact (proj2 (@lem3739142 A _42915 x s R y h1)). Qed.
Lemma lem3740065 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term623 A x s y _42915.
Proof. exact (proj1 (@lem3739143 A _42915 x s R y h1)). Qed.
Lemma lem3740079 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term624 A x s y _42915.
Proof. exact (proj2 (@lem3739143 A _42915 x s R y h1)). Qed.
Lemma lem3740163 {A : Type'} (_42928 : A) (s : A -> Prop) (h1 : term588 A s) : term576 A s _42928.
Proof. exact (EQ_MP (@lem3739098 A s _42928) (@lem3739097 A _42928 s h1)). Qed.
Lemma lem3740177 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term621 A x R y _42927.
Proof. exact (proj1 (@lem3739154 A _42927 x s R y h1)). Qed.
Lemma lem3740205 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term623 A x s y _42927.
Proof. exact (proj1 (@lem3739155 A _42927 x s R y h1)). Qed.
Lemma lem3740283 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3740284 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : term625 A R x''.
Proof. exact (fun h0 : term192 A R x'' => @lem3740283 A R x'' h1). Qed.
Lemma lem3740286 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740287 {A : Type'} (R : type1402 A) (x'' : A) : (term625 A R x'') = (R x'' x'').
Proof. exact (@lem3740286 (R x'' x'')). Qed.
Lemma lem3740288 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (EQ_MP (@lem3740287 A R x'') (@lem3740284 A R x'' h1)). Qed.
Lemma lem3740291 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3740293 {A : Type'} (R : type1402 A) (_42891 : A) : (term192 A R _42891) = (term627 A R _42891).
Proof. exact (@lem3740291 (R _42891 _42891)). Qed.
Lemma lem3740296 {A : Type'} (_42891 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42891.
Proof. exact (EQ_MP (@lem3740293 A R _42891) (@lem3739673 A _42891 x s R y h1)). Qed.
Lemma lem3740297 {A : Type'} (_42891 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42891.
Proof. exact (@lem3740296 A _42891 x s R y h1). Qed.
Lemma lem3740298 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R x''.
Proof. exact (@lem3740297 A x'' x s R y h1). Qed.
Lemma lem3740301 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (@lem3740298 A x'' x s R y h1 (@lem3740288 A R x'' h2)). Qed.
Lemma lem3740302 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : term628.
Proof. exact (fun h0 : ~ False => @lem3740301 A x s y R x'' h1 h2). Qed.
Lemma lem3740304 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740305 : term628 = False.
Proof. exact (@lem3740304 False). Qed.
Lemma lem3740306 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3740305) (@lem3740302 A x s y R x'' h1 h2)). Qed.
Lemma lem3740370 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (h1). Qed.
Lemma lem3740371 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : term625 A R x''.
Proof. exact (fun h0 : term192 A R x'' => @lem3740370 A R x'' h1). Qed.
Lemma lem3740373 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740374 {A : Type'} (R : type1402 A) (x'' : A) : (term625 A R x'') = (R x'' x'').
Proof. exact (@lem3740373 (R x'' x'')). Qed.
Lemma lem3740375 {A : Type'} (R : type1402 A) (x'' : A) (h1 : R x'' x'') : R x'' x''.
Proof. exact (EQ_MP (@lem3740374 A R x'') (@lem3740371 A R x'' h1)). Qed.
Lemma lem3740378 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3740380 {A : Type'} (R : type1402 A) (_42896 : A) : (term192 A R _42896) = (term627 A R _42896).
Proof. exact (@lem3740378 (R _42896 _42896)). Qed.
Lemma lem3740383 {A : Type'} (_42896 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42896.
Proof. exact (EQ_MP (@lem3740380 A R _42896) (@lem3739225 A _42896 x s R y h1)). Qed.
Lemma lem3740384 {A : Type'} (_42896 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42896.
Proof. exact (@lem3740383 A _42896 x s R y h1). Qed.
Lemma lem3740385 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R x''.
Proof. exact (@lem3740384 A x'' x s R y h1). Qed.
Lemma lem3740388 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (@lem3740385 A x'' x s R y h1 (@lem3740375 A R x'' h2)). Qed.
Lemma lem3740389 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : term628.
Proof. exact (fun h0 : ~ False => @lem3740388 A x s y R x'' h1 h2). Qed.
Lemma lem3740391 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740392 : term628 = False.
Proof. exact (@lem3740391 False). Qed.
Lemma lem3740393 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3740392) (@lem3740389 A x s y R x'' h1 h2)). Qed.
Lemma lem3740457 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R x'' y'.
Proof. exact (proj1 (@lem3738183 A y' R x'' z h1)). Qed.
Lemma lem3740458 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term629 A R x'' y'.
Proof. exact (fun h0 : term589 A R x'' y' => @lem3740457 A y' R x'' z h1). Qed.
Lemma lem3740460 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740461 {A : Type'} (R : type1402 A) (x'' : A) (y' : A) : (term629 A R x'' y') = (R x'' y').
Proof. exact (@lem3740460 (R x'' y')). Qed.
Lemma lem3740462 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R x'' y'.
Proof. exact (EQ_MP (@lem3740461 A R x'' y') (@lem3740458 A y' R x'' z h1)). Qed.
Lemma lem3740464 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R y' z.
Proof. exact (proj2 (@lem3738183 A y' R x'' z h1)). Qed.
Lemma lem3740465 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term629 A R y' z.
Proof. exact (fun h0 : term589 A R y' z => @lem3740464 A y' R x'' z h1). Qed.
Lemma lem3740467 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740468 {A : Type'} (R : type1402 A) (y' : A) (z : A) : (term629 A R y' z) = (R y' z).
Proof. exact (@lem3740467 (R y' z)). Qed.
Lemma lem3740469 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R y' z.
Proof. exact (EQ_MP (@lem3740468 A R y' z) (@lem3740465 A y' R x'' z h1)). Qed.
Lemma lem3740485 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3740486 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term630 A _42903 R _42902 _42904) = (term631 A _42902 R _42903 _42904).
Proof. exact (@lem3740485 (R _42902 _42904) (term589 A R _42903 _42904)). Qed.
Lemma lem3740492 {A : Type'} (R : type1402 A) (_42902 : A) (_42903 : A) : (term632 A R _42902 _42903) = (term632 A R _42902 _42903).
Proof. exact (eq_refl (term632 A R _42902 _42903)). Qed.
Lemma lem3740493 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term620 A _42903 R _42902 _42904) = (term633 A _42902 R _42903 _42904).
Proof. exact (MK_COMB (@lem3740492 A R _42902 _42903) (@lem3740486 A _42902 R _42903 _42904)). Qed.
Lemma lem3740497 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3740498 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term633 A _42902 R _42903 _42904) = (term634 A _42902 R _42903 _42904).
Proof. exact (@lem3740497 (R _42902 _42904) (term589 A R _42902 _42903) (term589 A R _42903 _42904)). Qed.
Lemma lem3740514 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term620 A _42903 R _42902 _42904) = (term634 A _42902 R _42903 _42904).
Proof. exact (TRANS (@lem3740493 A _42902 R _42903 _42904) (@lem3740498 A _42902 R _42903 _42904)). Qed.
Lemma lem3740515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3740516 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term635 A _42903 R _42902 _42904) = (term636 A _42902 R _42903 _42904).
Proof. exact (MK_COMB (@lem3740515) (@lem3740514 A _42902 R _42903 _42904)). Qed.
Lemma lem3740532 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term634 A _42902 R _42903 _42904) = (term634 A _42902 R _42903 _42904).
Proof. exact (eq_refl (term634 A _42902 R _42903 _42904)). Qed.
Lemma lem3740533 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : ((term620 A _42903 R _42902 _42904) = (term634 A _42902 R _42903 _42904)) = ((term634 A _42902 R _42903 _42904) = (term634 A _42902 R _42903 _42904)).
Proof. exact (MK_COMB (@lem3740516 A _42902 R _42903 _42904) (@lem3740532 A _42902 R _42903 _42904)). Qed.
Lemma lem3740535 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3740536 (x : Prop) : (x = x) = True.
Proof. exact (@lem3740535 Prop x). Qed.
Lemma lem3740537 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : ((term634 A _42902 R _42903 _42904) = (term634 A _42902 R _42903 _42904)) = True.
Proof. exact (@lem3740536 (term634 A _42902 R _42903 _42904)). Qed.
Lemma lem3740538 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : ((term620 A _42903 R _42902 _42904) = (term634 A _42902 R _42903 _42904)) = True.
Proof. exact (TRANS (@lem3740533 A _42902 R _42903 _42904) (@lem3740537 A _42902 R _42903 _42904)). Qed.
Lemma lem3740539 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : True = ((term620 A _42903 R _42902 _42904) = (term634 A _42902 R _42903 _42904)).
Proof. exact (SYM (@lem3740538 A _42902 R _42903 _42904)). Qed.
Lemma lem3740540 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term620 A _42903 R _42902 _42904) = (term634 A _42902 R _42903 _42904).
Proof. exact (EQ_MP (@lem3740539 A _42902 R _42903 _42904) (@lem0)). Qed.
Lemma lem3740541 {A : Type'} (_42902 : A) (_42903 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term634 A _42902 R _42903 _42904.
Proof. exact (EQ_MP (@lem3740540 A _42902 R _42903 _42904) (@lem3739827 A _42903 _42902 _42904 x s R y h1)). Qed.
Lemma lem3740543 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3740544 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) (_42904 : A) : (term634 A _42902 R _42903 _42904) = (term638 A _42903 R _42902 _42904).
Proof. exact (@lem3740543 (term475 A _42902 R _42903 _42904) (R _42902 _42904)). Qed.
Lemma lem3740546 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3740547 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term641 A _42902 R _42903 _42904) = (term642 A _42902 R _42903 _42904).
Proof. exact (@lem3740546 (term589 A R _42902 _42903) (term589 A R _42903 _42904)). Qed.
Lemma lem3740549 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740550 {A : Type'} (R : type1402 A) (_42902 : A) (_42903 : A) : (term643 A R _42902 _42903) = (R _42902 _42903).
Proof. exact (@lem3740549 (R _42902 _42903)). Qed.
Lemma lem3740551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3740552 {A : Type'} (R : type1402 A) (_42902 : A) (_42903 : A) : (term644 A R _42902 _42903) = (term645 A R _42902 _42903).
Proof. exact (MK_COMB (@lem3740551) (@lem3740550 A R _42902 _42903)). Qed.
Lemma lem3740554 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740555 {A : Type'} (R : type1402 A) (_42903 : A) (_42904 : A) : (term643 A R _42903 _42904) = (R _42903 _42904).
Proof. exact (@lem3740554 (R _42903 _42904)). Qed.
Lemma lem3740556 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term642 A _42902 R _42903 _42904) = (term207 A _42902 R _42903 _42904).
Proof. exact (MK_COMB (@lem3740552 A R _42902 _42903) (@lem3740555 A R _42903 _42904)). Qed.
Lemma lem3740557 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term641 A _42902 R _42903 _42904) = (term207 A _42902 R _42903 _42904).
Proof. exact (TRANS (@lem3740547 A _42902 R _42903 _42904) (@lem3740556 A _42902 R _42903 _42904)). Qed.
Lemma lem3740558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3740559 {A : Type'} (_42902 : A) (R : type1402 A) (_42903 : A) (_42904 : A) : (term646 A _42902 R _42903 _42904) = (term647 A _42902 R _42903 _42904).
Proof. exact (MK_COMB (@lem3740558) (@lem3740557 A _42902 R _42903 _42904)). Qed.
Lemma lem3740560 {A : Type'} (R : type1402 A) (_42902 : A) (_42904 : A) : (R _42902 _42904) = (R _42902 _42904).
Proof. exact (eq_refl (R _42902 _42904)). Qed.
Lemma lem3740561 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) (_42904 : A) : (term638 A _42903 R _42902 _42904) = (term186 A _42903 R _42902 _42904).
Proof. exact (MK_COMB (@lem3740559 A _42902 R _42903 _42904) (@lem3740560 A R _42902 _42904)). Qed.
Lemma lem3740562 {A : Type'} (_42903 : A) (R : type1402 A) (_42902 : A) (_42904 : A) : (term634 A _42902 R _42903 _42904) = (term186 A _42903 R _42902 _42904).
Proof. exact (TRANS (@lem3740544 A _42903 R _42902 _42904) (@lem3740561 A _42903 R _42902 _42904)). Qed.
Lemma lem3740564 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term207 A x'' R y' z.
Proof. exact (conj (@lem3740462 A y' R x'' z h1) (@lem3740469 A y' R x'' z h1)). Qed.
Lemma lem3740566 {A : Type'} (_42903 : A) (_42902 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42903 R _42902 _42904.
Proof. exact (EQ_MP (@lem3740562 A _42903 R _42902 _42904) (@lem3740541 A _42902 _42903 _42904 x s R y h1)). Qed.
Lemma lem3740567 {A : Type'} (_42903 : A) (_42902 : A) (_42904 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42903 R _42902 _42904.
Proof. exact (@lem3740566 A _42903 _42902 _42904 x s R y h1). Qed.
Lemma lem3740568 {A : Type'} (y' : A) (x'' : A) (z : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A y' R x'' z.
Proof. exact (@lem3740567 A y' x'' z x s R y h1). Qed.
Lemma lem3740571 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : R x'' z.
Proof. exact (@lem3740568 A y' x'' z x s R y h1 (@lem3740564 A y' R x'' z h2)). Qed.
Lemma lem3740572 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : term629 A R x'' z.
Proof. exact (fun h0 : term589 A R x'' z => @lem3740571 A x s y y' R x'' z h1 h2). Qed.
Lemma lem3740574 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740575 {A : Type'} (R : type1402 A) (x'' : A) (z : A) : (term629 A R x'' z) = (R x'' z).
Proof. exact (@lem3740574 (R x'' z)). Qed.
Lemma lem3740576 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : R x'' z.
Proof. exact (EQ_MP (@lem3740575 A R x'' z) (@lem3740572 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3740579 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3740581 {A : Type'} (R : type1402 A) (x'' : A) (z : A) : (term589 A R x'' z) = (term648 A R x'' z).
Proof. exact (@lem3740579 (R x'' z)). Qed.
Lemma lem3740584 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term648 A R x'' z.
Proof. exact (EQ_MP (@lem3740581 A R x'' z) (@lem3739841 A y' R x'' z h1)). Qed.
Lemma lem3740587 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : False.
Proof. exact (@lem3740584 A y' R x'' z h2 (@lem3740576 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3740588 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : term628.
Proof. exact (fun h0 : ~ False => @lem3740587 A x s y y' R x'' z h1 h2). Qed.
Lemma lem3740590 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740591 : term628 = False.
Proof. exact (@lem3740590 False). Qed.
Lemma lem3740656 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R x'' y'.
Proof. exact (proj1 (@lem3738183 A y' R x'' z h1)). Qed.
Lemma lem3740657 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term629 A R x'' y'.
Proof. exact (fun h0 : term589 A R x'' y' => @lem3740656 A y' R x'' z h1). Qed.
Lemma lem3740659 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740660 {A : Type'} (R : type1402 A) (x'' : A) (y' : A) : (term629 A R x'' y') = (R x'' y').
Proof. exact (@lem3740659 (R x'' y')). Qed.
Lemma lem3740661 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R x'' y'.
Proof. exact (EQ_MP (@lem3740660 A R x'' y') (@lem3740657 A y' R x'' z h1)). Qed.
Lemma lem3740663 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R y' z.
Proof. exact (proj2 (@lem3738183 A y' R x'' z h1)). Qed.
Lemma lem3740664 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term629 A R y' z.
Proof. exact (fun h0 : term589 A R y' z => @lem3740663 A y' R x'' z h1). Qed.
Lemma lem3740666 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740667 {A : Type'} (R : type1402 A) (y' : A) (z : A) : (term629 A R y' z) = (R y' z).
Proof. exact (@lem3740666 (R y' z)). Qed.
Lemma lem3740668 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : R y' z.
Proof. exact (EQ_MP (@lem3740667 A R y' z) (@lem3740664 A y' R x'' z h1)). Qed.
Lemma lem3740684 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3740685 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term630 A _42908 R _42907 _42909) = (term631 A _42907 R _42908 _42909).
Proof. exact (@lem3740684 (R _42907 _42909) (term589 A R _42908 _42909)). Qed.
Lemma lem3740691 {A : Type'} (R : type1402 A) (_42907 : A) (_42908 : A) : (term632 A R _42907 _42908) = (term632 A R _42907 _42908).
Proof. exact (eq_refl (term632 A R _42907 _42908)). Qed.
Lemma lem3740692 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term620 A _42908 R _42907 _42909) = (term633 A _42907 R _42908 _42909).
Proof. exact (MK_COMB (@lem3740691 A R _42907 _42908) (@lem3740685 A _42907 R _42908 _42909)). Qed.
Lemma lem3740696 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3740697 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term633 A _42907 R _42908 _42909) = (term634 A _42907 R _42908 _42909).
Proof. exact (@lem3740696 (R _42907 _42909) (term589 A R _42907 _42908) (term589 A R _42908 _42909)). Qed.
Lemma lem3740713 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term620 A _42908 R _42907 _42909) = (term634 A _42907 R _42908 _42909).
Proof. exact (TRANS (@lem3740692 A _42907 R _42908 _42909) (@lem3740697 A _42907 R _42908 _42909)). Qed.
Lemma lem3740714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3740715 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term635 A _42908 R _42907 _42909) = (term636 A _42907 R _42908 _42909).
Proof. exact (MK_COMB (@lem3740714) (@lem3740713 A _42907 R _42908 _42909)). Qed.
Lemma lem3740731 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term634 A _42907 R _42908 _42909) = (term634 A _42907 R _42908 _42909).
Proof. exact (eq_refl (term634 A _42907 R _42908 _42909)). Qed.
Lemma lem3740732 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : ((term620 A _42908 R _42907 _42909) = (term634 A _42907 R _42908 _42909)) = ((term634 A _42907 R _42908 _42909) = (term634 A _42907 R _42908 _42909)).
Proof. exact (MK_COMB (@lem3740715 A _42907 R _42908 _42909) (@lem3740731 A _42907 R _42908 _42909)). Qed.
Lemma lem3740734 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3740735 (x : Prop) : (x = x) = True.
Proof. exact (@lem3740734 Prop x). Qed.
Lemma lem3740736 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : ((term634 A _42907 R _42908 _42909) = (term634 A _42907 R _42908 _42909)) = True.
Proof. exact (@lem3740735 (term634 A _42907 R _42908 _42909)). Qed.
Lemma lem3740737 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : ((term620 A _42908 R _42907 _42909) = (term634 A _42907 R _42908 _42909)) = True.
Proof. exact (TRANS (@lem3740732 A _42907 R _42908 _42909) (@lem3740736 A _42907 R _42908 _42909)). Qed.
Lemma lem3740738 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : True = ((term620 A _42908 R _42907 _42909) = (term634 A _42907 R _42908 _42909)).
Proof. exact (SYM (@lem3740737 A _42907 R _42908 _42909)). Qed.
Lemma lem3740739 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term620 A _42908 R _42907 _42909) = (term634 A _42907 R _42908 _42909).
Proof. exact (EQ_MP (@lem3740738 A _42907 R _42908 _42909) (@lem0)). Qed.
Lemma lem3740740 {A : Type'} (_42907 : A) (_42908 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term634 A _42907 R _42908 _42909.
Proof. exact (EQ_MP (@lem3740739 A _42907 R _42908 _42909) (@lem3739349 A _42908 _42907 _42909 x s R y h1)). Qed.
Lemma lem3740742 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3740743 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) (_42909 : A) : (term634 A _42907 R _42908 _42909) = (term638 A _42908 R _42907 _42909).
Proof. exact (@lem3740742 (term475 A _42907 R _42908 _42909) (R _42907 _42909)). Qed.
Lemma lem3740745 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3740746 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term641 A _42907 R _42908 _42909) = (term642 A _42907 R _42908 _42909).
Proof. exact (@lem3740745 (term589 A R _42907 _42908) (term589 A R _42908 _42909)). Qed.
Lemma lem3740748 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740749 {A : Type'} (R : type1402 A) (_42907 : A) (_42908 : A) : (term643 A R _42907 _42908) = (R _42907 _42908).
Proof. exact (@lem3740748 (R _42907 _42908)). Qed.
Lemma lem3740750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3740751 {A : Type'} (R : type1402 A) (_42907 : A) (_42908 : A) : (term644 A R _42907 _42908) = (term645 A R _42907 _42908).
Proof. exact (MK_COMB (@lem3740750) (@lem3740749 A R _42907 _42908)). Qed.
Lemma lem3740753 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740754 {A : Type'} (R : type1402 A) (_42908 : A) (_42909 : A) : (term643 A R _42908 _42909) = (R _42908 _42909).
Proof. exact (@lem3740753 (R _42908 _42909)). Qed.
Lemma lem3740755 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term642 A _42907 R _42908 _42909) = (term207 A _42907 R _42908 _42909).
Proof. exact (MK_COMB (@lem3740751 A R _42907 _42908) (@lem3740754 A R _42908 _42909)). Qed.
Lemma lem3740756 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term641 A _42907 R _42908 _42909) = (term207 A _42907 R _42908 _42909).
Proof. exact (TRANS (@lem3740746 A _42907 R _42908 _42909) (@lem3740755 A _42907 R _42908 _42909)). Qed.
Lemma lem3740757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3740758 {A : Type'} (_42907 : A) (R : type1402 A) (_42908 : A) (_42909 : A) : (term646 A _42907 R _42908 _42909) = (term647 A _42907 R _42908 _42909).
Proof. exact (MK_COMB (@lem3740757) (@lem3740756 A _42907 R _42908 _42909)). Qed.
Lemma lem3740759 {A : Type'} (R : type1402 A) (_42907 : A) (_42909 : A) : (R _42907 _42909) = (R _42907 _42909).
Proof. exact (eq_refl (R _42907 _42909)). Qed.
Lemma lem3740760 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) (_42909 : A) : (term638 A _42908 R _42907 _42909) = (term186 A _42908 R _42907 _42909).
Proof. exact (MK_COMB (@lem3740758 A _42907 R _42908 _42909) (@lem3740759 A R _42907 _42909)). Qed.
Lemma lem3740761 {A : Type'} (_42908 : A) (R : type1402 A) (_42907 : A) (_42909 : A) : (term634 A _42907 R _42908 _42909) = (term186 A _42908 R _42907 _42909).
Proof. exact (TRANS (@lem3740743 A _42908 R _42907 _42909) (@lem3740760 A _42908 R _42907 _42909)). Qed.
Lemma lem3740763 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term207 A x'' R y' z.
Proof. exact (conj (@lem3740661 A y' R x'' z h1) (@lem3740668 A y' R x'' z h1)). Qed.
Lemma lem3740765 {A : Type'} (_42908 : A) (_42907 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42908 R _42907 _42909.
Proof. exact (EQ_MP (@lem3740761 A _42908 R _42907 _42909) (@lem3740740 A _42907 _42908 _42909 x s R y h1)). Qed.
Lemma lem3740766 {A : Type'} (_42908 : A) (_42907 : A) (_42909 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42908 R _42907 _42909.
Proof. exact (@lem3740765 A _42908 _42907 _42909 x s R y h1). Qed.
Lemma lem3740767 {A : Type'} (y' : A) (x'' : A) (z : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A y' R x'' z.
Proof. exact (@lem3740766 A y' x'' z x s R y h1). Qed.
Lemma lem3740770 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : R x'' z.
Proof. exact (@lem3740767 A y' x'' z x s R y h1 (@lem3740763 A y' R x'' z h2)). Qed.
Lemma lem3740771 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : term629 A R x'' z.
Proof. exact (fun h0 : term589 A R x'' z => @lem3740770 A x s y y' R x'' z h1 h2). Qed.
Lemma lem3740773 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740774 {A : Type'} (R : type1402 A) (x'' : A) (z : A) : (term629 A R x'' z) = (R x'' z).
Proof. exact (@lem3740773 (R x'' z)). Qed.
Lemma lem3740775 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : R x'' z.
Proof. exact (EQ_MP (@lem3740774 A R x'' z) (@lem3740771 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3740778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3740780 {A : Type'} (R : type1402 A) (x'' : A) (z : A) : (term589 A R x'' z) = (term648 A R x'' z).
Proof. exact (@lem3740778 (R x'' z)). Qed.
Lemma lem3740783 {A : Type'} (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term206 A y' R x'' z) : term648 A R x'' z.
Proof. exact (EQ_MP (@lem3740780 A R x'' z) (@lem3739351 A y' R x'' z h1)). Qed.
Lemma lem3740786 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : False.
Proof. exact (@lem3740783 A y' R x'' z h2 (@lem3740775 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3740787 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : term628.
Proof. exact (fun h0 : ~ False => @lem3740786 A x s y y' R x'' z h1 h2). Qed.
Lemma lem3740789 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740790 : term628 = False.
Proof. exact (@lem3740789 False). Qed.
Lemma lem3740791 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : False.
Proof. exact (EQ_MP (@lem3740790) (@lem3740787 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3740792 {A : Type'} (R : type1402 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem3740793 {A : Type'} (_43069 : A) (_43071 : A) (h1 : _43069 = _43071) : _43069 = _43071.
Proof. exact (h1). Qed.
Lemma lem3740794 {A : Type'} (_43070 : A) (_43072 : A) (h1 : _43070 = _43072) : _43070 = _43072.
Proof. exact (h1). Qed.
Lemma lem3740795 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (h1 : _43069 = _43071) : (R _43069) = (R _43071).
Proof. exact (MK_COMB (@lem3740792 A R) (@lem3740793 A _43069 _43071 h1)). Qed.
Lemma lem3740796 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) (h1 : _43069 = _43071) (h2 : _43070 = _43072) : (R _43069 _43070) = (R _43071 _43072).
Proof. exact (MK_COMB (@lem3740795 A R _43069 _43071 h1) (@lem3740794 A _43070 _43072 h2)). Qed.
Lemma lem3740798 (b : Prop) (a : Prop) : term649 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3740799 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : term650 A _43071 _43072 R _43069 _43070.
Proof. exact (@lem3740798 (R _43071 _43072) (R _43069 _43070)). Qed.
Lemma lem3740800 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) (h1 : _43069 = _43071) (h2 : _43070 = _43072) : term651 A _43071 _43072 R _43069 _43070.
Proof. exact (@lem3740799 A _43071 _43072 R _43069 _43070 (@lem3740796 A R _43069 _43071 _43070 _43072 h1 h2)). Qed.
Lemma lem3740801 {A : Type'} (_43072 : A) (R : type1402 A) (_43070 : A) (_43069 : A) (_43071 : A) (h1 : _43069 = _43071) : term652 A _43071 _43072 R _43069 _43070.
Proof. exact (fun h0 : _43070 = _43072 => @lem3740800 A R _43069 _43071 _43070 _43072 h1 h0). Qed.
Lemma lem3740803 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3740804 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term652 A _43071 _43072 R _43069 _43070) = (term654 A _43071 _43072 R _43069 _43070).
Proof. exact (@lem3740803 (_43070 = _43072) (term651 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3740805 {A : Type'} (_43072 : A) (R : type1402 A) (_43070 : A) (_43069 : A) (_43071 : A) (h1 : _43069 = _43071) : term654 A _43071 _43072 R _43069 _43070.
Proof. exact (EQ_MP (@lem3740804 A _43071 _43072 R _43069 _43070) (@lem3740801 A _43072 R _43070 _43069 _43071 h1)). Qed.
Lemma lem3740806 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : term655 A _43071 _43072 R _43069 _43070.
Proof. exact (fun h0 : _43069 = _43071 => @lem3740805 A _43072 R _43070 _43069 _43071 h0). Qed.
Lemma lem3740808 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3740809 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term655 A _43071 _43072 R _43069 _43070) = (term656 A _43071 _43072 R _43069 _43070).
Proof. exact (@lem3740808 (_43069 = _43071) (term654 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3740810 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : term656 A _43071 _43072 R _43069 _43070.
Proof. exact (EQ_MP (@lem3740809 A _43071 _43072 R _43069 _43070) (@lem3740806 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3740855 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3740856 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3740855 A x). Qed.
Lemma lem3740857 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3740856 A x). Qed.
Lemma lem3740859 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740860 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3740859 (x = x)). Qed.
Lemma lem3740861 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3740860 A x) (@lem3740857 A x)). Qed.
Lemma lem3740863 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3740864 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3740863 A x). Qed.
Lemma lem3740865 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3740864 A x). Qed.
Lemma lem3740867 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740868 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3740867 (x = x)). Qed.
Lemma lem3740869 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3740868 A x) (@lem3740865 A x)). Qed.
Lemma lem3740871 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3740872 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3740871 A x). Qed.
Lemma lem3740873 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (@lem3740872 A x''). Qed.
Lemma lem3740874 {A : Type'} (x'' : A) : term657 A x''.
Proof. exact (fun h0 : term658 A x'' => @lem3740873 A x''). Qed.
Lemma lem3740876 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740877 {A : Type'} (x'' : A) : (term657 A x'') = (x'' = x'').
Proof. exact (@lem3740876 (x'' = x'')). Qed.
Lemma lem3740878 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (EQ_MP (@lem3740877 A x'') (@lem3740874 A x'')). Qed.
Lemma lem3740880 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3740881 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3740880 A s R x'' h1). Qed.
Lemma lem3740883 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740884 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3740883 (@I (A -> Prop) s x'')). Qed.
Lemma lem3740885 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3740884 A s x'') (@lem3740881 A s R x'' h1)). Qed.
Lemma lem3740887 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3740888 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3740887 A s R x'' h1). Qed.
Lemma lem3740890 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740891 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3740890 (@I (A -> Prop) s x'')). Qed.
Lemma lem3740892 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3740891 A s x'') (@lem3740888 A s R x'' h1)). Qed.
Lemma lem3740898 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3740899 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term622 A s R y _42915) = (term660 A R y s _42915).
Proof. exact (@lem3740898 (term566 A R y _42915) (term576 A s _42915)). Qed.
Lemma lem3740905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3740906 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term661 A s R y _42915) = (term662 A R y s _42915).
Proof. exact (MK_COMB (@lem3740905) (@lem3740899 A R y s _42915)). Qed.
Lemma lem3740912 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term660 A R y s _42915) = (term660 A R y s _42915).
Proof. exact (eq_refl (term660 A R y s _42915)). Qed.
Lemma lem3740913 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : ((term622 A s R y _42915) = (term660 A R y s _42915)) = ((term660 A R y s _42915) = (term660 A R y s _42915)).
Proof. exact (MK_COMB (@lem3740906 A R y s _42915) (@lem3740912 A R y s _42915)). Qed.
Lemma lem3740915 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3740916 (x : Prop) : (x = x) = True.
Proof. exact (@lem3740915 Prop x). Qed.
Lemma lem3740917 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : ((term660 A R y s _42915) = (term660 A R y s _42915)) = True.
Proof. exact (@lem3740916 (term660 A R y s _42915)). Qed.
Lemma lem3740918 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : ((term622 A s R y _42915) = (term660 A R y s _42915)) = True.
Proof. exact (TRANS (@lem3740913 A R y s _42915) (@lem3740917 A R y s _42915)). Qed.
Lemma lem3740919 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : True = ((term622 A s R y _42915) = (term660 A R y s _42915)).
Proof. exact (SYM (@lem3740918 A R y s _42915)). Qed.
Lemma lem3740920 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term622 A s R y _42915) = (term660 A R y s _42915).
Proof. exact (EQ_MP (@lem3740919 A R y s _42915) (@lem0)). Qed.
Lemma lem3740921 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term660 A R y s _42915.
Proof. exact (EQ_MP (@lem3740920 A R y s _42915) (@lem3740051 A _42915 x s R y h1)). Qed.
Lemma lem3740923 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3740924 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42915 : A) : (term660 A R y s _42915) = (term663 A s R y _42915).
Proof. exact (@lem3740923 (term576 A s _42915) (term566 A R y _42915)). Qed.
Lemma lem3740926 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740927 {A : Type'} (s : A -> Prop) (_42915 : A) : (term664 A s _42915) = (@I (A -> Prop) s _42915).
Proof. exact (@lem3740926 (@I (A -> Prop) s _42915)). Qed.
Lemma lem3740928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3740929 {A : Type'} (s : A -> Prop) (_42915 : A) : (term665 A s _42915) = (term666 A s _42915).
Proof. exact (MK_COMB (@lem3740928) (@lem3740927 A s _42915)). Qed.
Lemma lem3740930 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) : (term566 A R y _42915) = (term566 A R y _42915).
Proof. exact (eq_refl (term566 A R y _42915)). Qed.
Lemma lem3740931 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42915 : A) : (term663 A s R y _42915) = (term667 A s R y _42915).
Proof. exact (MK_COMB (@lem3740929 A s _42915) (@lem3740930 A R y _42915)). Qed.
Lemma lem3740932 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42915 : A) : (term660 A R y s _42915) = (term667 A s R y _42915).
Proof. exact (TRANS (@lem3740924 A s R y _42915) (@lem3740931 A s R y _42915)). Qed.
Lemma lem3740935 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42915.
Proof. exact (EQ_MP (@lem3740932 A s R y _42915) (@lem3740921 A _42915 x s R y h1)). Qed.
Lemma lem3740936 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42915.
Proof. exact (@lem3740935 A _42915 x s R y h1). Qed.
Lemma lem3740937 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y x''.
Proof. exact (@lem3740936 A x'' x s R y h1). Qed.
Lemma lem3740940 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (@lem3740937 A x'' x s R y h1 (@lem3740892 A s R x'' h2)). Qed.
Lemma lem3740941 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term668 A R y x''.
Proof. exact (fun h0 : term669 A R y x'' => @lem3740940 A x y s R x'' h1 h2). Qed.
Lemma lem3740943 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3740944 {A : Type'} (R : type1402 A) (y : A -> A) (x'' : A) : (term668 A R y x'') = (term566 A R y x'').
Proof. exact (@lem3740943 (term566 A R y x'')). Qed.
Lemma lem3740945 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (EQ_MP (@lem3740944 A R y x'') (@lem3740941 A x y s R x'' h1 h2)). Qed.
Lemma lem3740947 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3740948 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42916 : A) : (term592 A s R x'' _42916) = (term670 A R x'' s _42916).
Proof. exact (@lem3740947 (term589 A R x'' _42916) (term576 A s _42916)). Qed.
Lemma lem3740950 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3740951 {A : Type'} (R : type1402 A) (x'' : A) (_42916 : A) : (term643 A R x'' _42916) = (R x'' _42916).
Proof. exact (@lem3740950 (R x'' _42916)). Qed.
Lemma lem3740952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3740953 {A : Type'} (R : type1402 A) (x'' : A) (_42916 : A) : (term671 A R x'' _42916) = (term672 A R x'' _42916).
Proof. exact (MK_COMB (@lem3740952) (@lem3740951 A R x'' _42916)). Qed.
Lemma lem3740954 {A : Type'} (s : A -> Prop) (_42916 : A) : (term576 A s _42916) = (term576 A s _42916).
Proof. exact (eq_refl (term576 A s _42916)). Qed.
Lemma lem3740955 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42916 : A) : (term670 A R x'' s _42916) = (term673 A R x'' s _42916).
Proof. exact (MK_COMB (@lem3740953 A R x'' _42916) (@lem3740954 A s _42916)). Qed.
Lemma lem3740956 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42916 : A) : (term592 A s R x'' _42916) = (term673 A R x'' s _42916).
Proof. exact (TRANS (@lem3740948 A R x'' s _42916) (@lem3740955 A R x'' s _42916)). Qed.
Lemma lem3740959 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42916.
Proof. exact (EQ_MP (@lem3740956 A R x'' s _42916) (@lem3740023 A _42916 s R x'' h1)). Qed.
Lemma lem3740960 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42916.
Proof. exact (@lem3740959 A _42916 s R x'' h1). Qed.
Lemma lem3740961 {A : Type'} (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term674 A R s y x''.
Proof. exact (@lem3740960 A (y x'') s R x'' h1). Qed.
Lemma lem3740964 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x''.
Proof. exact (@lem3740961 A y s R x'' h2 (@lem3740945 A x y s R x'' h1 h2)). Qed.
Lemma lem3740965 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term676 A s y x''.
Proof. exact (fun h0 : term568 A s y x'' => @lem3740964 A x y s R x'' h1 h2). Qed.
Lemma lem3740967 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3740968 {A : Type'} (s : A -> Prop) (y : A -> A) (x'' : A) : (term676 A s y x'') = (term675 A s y x'').
Proof. exact (@lem3740967 (term568 A s y x'')). Qed.
Lemma lem3740969 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x''.
Proof. exact (EQ_MP (@lem3740968 A s y x'') (@lem3740965 A x y s R x'' h1 h2)). Qed.
Lemma lem3740975 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3740976 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term624 A x s y _42915) = (term678 A x s y _42915).
Proof. exact (@lem3740975 ((y _42915) = x) (term576 A s _42915) (term568 A s y _42915)). Qed.
Lemma lem3740992 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3740993 {A : Type'} (y : A -> A) (s : A -> Prop) (_42915 : A) : (term679 A s y _42915) = (term680 A y s _42915).
Proof. exact (@lem3740992 (term568 A s y _42915) (term576 A s _42915)). Qed.
Lemma lem3740999 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : (term569 A y _42915 x) = (term569 A y _42915 x).
Proof. exact (eq_refl (term569 A y _42915 x)). Qed.
Lemma lem3741000 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term678 A x s y _42915) = (term681 A x y s _42915).
Proof. exact (MK_COMB (@lem3740999 A y _42915 x) (@lem3740993 A y s _42915)). Qed.
Lemma lem3741011 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term624 A x s y _42915) = (term681 A x y s _42915).
Proof. exact (TRANS (@lem3740976 A x s y _42915) (@lem3741000 A x y s _42915)). Qed.
Lemma lem3741012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741013 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term682 A x s y _42915) = (term683 A x y s _42915).
Proof. exact (MK_COMB (@lem3741012) (@lem3741011 A x y s _42915)). Qed.
Lemma lem3741029 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741030 {A : Type'} (y : A -> A) (s : A -> Prop) (_42915 : A) : (term679 A s y _42915) = (term680 A y s _42915).
Proof. exact (@lem3741029 (term568 A s y _42915) (term576 A s _42915)). Qed.
Lemma lem3741036 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : (term569 A y _42915 x) = (term569 A y _42915 x).
Proof. exact (eq_refl (term569 A y _42915 x)). Qed.
Lemma lem3741037 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : (term678 A x s y _42915) = (term681 A x y s _42915).
Proof. exact (MK_COMB (@lem3741036 A y _42915 x) (@lem3741030 A y s _42915)). Qed.
Lemma lem3741048 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : ((term624 A x s y _42915) = (term678 A x s y _42915)) = ((term681 A x y s _42915) = (term681 A x y s _42915)).
Proof. exact (MK_COMB (@lem3741013 A x y s _42915) (@lem3741037 A x y s _42915)). Qed.
Lemma lem3741050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741051 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741050 Prop x). Qed.
Lemma lem3741052 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42915 : A) : ((term681 A x y s _42915) = (term681 A x y s _42915)) = True.
Proof. exact (@lem3741051 (term681 A x y s _42915)). Qed.
Lemma lem3741053 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : ((term624 A x s y _42915) = (term678 A x s y _42915)) = True.
Proof. exact (TRANS (@lem3741048 A x y s _42915) (@lem3741052 A x y s _42915)). Qed.
Lemma lem3741054 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : True = ((term624 A x s y _42915) = (term678 A x s y _42915)).
Proof. exact (SYM (@lem3741053 A x s y _42915)). Qed.
Lemma lem3741055 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term624 A x s y _42915) = (term678 A x s y _42915).
Proof. exact (EQ_MP (@lem3741054 A x s y _42915) (@lem0)). Qed.
Lemma lem3741056 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term678 A x s y _42915.
Proof. exact (EQ_MP (@lem3741055 A x s y _42915) (@lem3740079 A _42915 x s R y h1)). Qed.
Lemma lem3741058 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741059 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term678 A x s y _42915) = (term684 A s y _42915 x).
Proof. exact (@lem3741058 (term679 A s y _42915) ((y _42915) = x)). Qed.
Lemma lem3741061 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741062 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term685 A s y _42915) = (term686 A s y _42915).
Proof. exact (@lem3741061 (term576 A s _42915) (term568 A s y _42915)). Qed.
Lemma lem3741064 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741065 {A : Type'} (s : A -> Prop) (_42915 : A) : (term664 A s _42915) = (@I (A -> Prop) s _42915).
Proof. exact (@lem3741064 (@I (A -> Prop) s _42915)). Qed.
Lemma lem3741066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741067 {A : Type'} (s : A -> Prop) (_42915 : A) : (term687 A s _42915) = (term595 A s _42915).
Proof. exact (MK_COMB (@lem3741066) (@lem3741065 A s _42915)). Qed.
Lemma lem3741068 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term675 A s y _42915) = (term675 A s y _42915).
Proof. exact (eq_refl (term675 A s y _42915)). Qed.
Lemma lem3741069 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term686 A s y _42915) = (term688 A s y _42915).
Proof. exact (MK_COMB (@lem3741067 A s _42915) (@lem3741068 A s y _42915)). Qed.
Lemma lem3741070 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term685 A s y _42915) = (term688 A s y _42915).
Proof. exact (TRANS (@lem3741062 A s y _42915) (@lem3741069 A s y _42915)). Qed.
Lemma lem3741071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741072 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term689 A s y _42915) = (term690 A s y _42915).
Proof. exact (MK_COMB (@lem3741071) (@lem3741070 A s y _42915)). Qed.
Lemma lem3741073 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : ((y _42915) = x) = ((y _42915) = x).
Proof. exact (eq_refl ((y _42915) = x)). Qed.
Lemma lem3741074 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term684 A s y _42915 x) = (term691 A s y _42915 x).
Proof. exact (MK_COMB (@lem3741072 A s y _42915) (@lem3741073 A y _42915 x)). Qed.
Lemma lem3741075 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term678 A x s y _42915) = (term691 A s y _42915 x).
Proof. exact (TRANS (@lem3741059 A s y _42915 x) (@lem3741074 A s y _42915 x)). Qed.
Lemma lem3741077 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term688 A s y x''.
Proof. exact (conj (@lem3740885 A s R x'' h2) (@lem3740969 A x y s R x'' h1 h2)). Qed.
Lemma lem3741079 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y _42915 x.
Proof. exact (EQ_MP (@lem3741075 A s y _42915 x) (@lem3741056 A _42915 x s R y h1)). Qed.
Lemma lem3741080 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y _42915 x.
Proof. exact (@lem3741079 A _42915 x s R y h1). Qed.
Lemma lem3741081 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y x'' x.
Proof. exact (@lem3741080 A x'' x s R y h1). Qed.
Lemma lem3741084 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x'') = x.
Proof. exact (@lem3741081 A x'' x s R y h1 (@lem3741077 A x y s R x'' h1 h2)). Qed.
Lemma lem3741085 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term692 A y x'' x.
Proof. exact (fun h0 : term693 A y x'' x => @lem3741084 A x y s R x'' h1 h2). Qed.
Lemma lem3741087 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741088 {A : Type'} (y : A -> A) (x'' : A) (x : A) : (term692 A y x'' x) = ((y x'') = x).
Proof. exact (@lem3741087 ((y x'') = x)). Qed.
Lemma lem3741089 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x'') = x.
Proof. exact (EQ_MP (@lem3741088 A y x'' x) (@lem3741085 A x y s R x'' h1 h2)). Qed.
Lemma lem3741091 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3741092 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3741091 A s R x'' h1). Qed.
Lemma lem3741094 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741095 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3741094 (@I (A -> Prop) s x'')). Qed.
Lemma lem3741096 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3741095 A s x'') (@lem3741092 A s R x'' h1)). Qed.
Lemma lem3741098 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42915.
Proof. exact (EQ_MP (@lem3740932 A s R y _42915) (@lem3740921 A _42915 x s R y h1)). Qed.
Lemma lem3741099 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42915.
Proof. exact (@lem3741098 A _42915 x s R y h1). Qed.
Lemma lem3741100 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y x''.
Proof. exact (@lem3741099 A x'' x s R y h1). Qed.
Lemma lem3741103 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (@lem3741100 A x'' x s R y h1 (@lem3741096 A s R x'' h2)). Qed.
Lemma lem3741104 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term668 A R y x''.
Proof. exact (fun h0 : term669 A R y x'' => @lem3741103 A x y s R x'' h1 h2). Qed.
Lemma lem3741106 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741107 {A : Type'} (R : type1402 A) (y : A -> A) (x'' : A) : (term668 A R y x'') = (term566 A R y x'').
Proof. exact (@lem3741106 (term566 A R y x'')). Qed.
Lemma lem3741108 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (EQ_MP (@lem3741107 A R y x'') (@lem3741104 A x y s R x'' h1 h2)). Qed.
Lemma lem3741126 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741127 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term654 A _43071 _43072 R _43069 _43070) = (term694 A _43071 _43072 R _43069 _43070).
Proof. exact (@lem3741126 (R _43071 _43072) (term606 A _43070 _43072) (term589 A R _43069 _43070)). Qed.
Lemma lem3741141 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741142 {A : Type'} (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term695 A _43072 R _43069 _43070) = (term696 A R _43069 _43070 _43072).
Proof. exact (@lem3741141 (term589 A R _43069 _43070) (term606 A _43070 _43072)). Qed.
Lemma lem3741150 {A : Type'} (R : type1402 A) (_43071 : A) (_43072 : A) : (term697 A R _43071 _43072) = (term697 A R _43071 _43072).
Proof. exact (eq_refl (term697 A R _43071 _43072)). Qed.
Lemma lem3741151 {A : Type'} (_43071 : A) (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term694 A _43071 _43072 R _43069 _43070) = (term698 A _43071 R _43069 _43070 _43072).
Proof. exact (MK_COMB (@lem3741150 A R _43071 _43072) (@lem3741142 A R _43069 _43070 _43072)). Qed.
Lemma lem3741162 {A : Type'} (_43071 : A) (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term654 A _43071 _43072 R _43069 _43070) = (term698 A _43071 R _43069 _43070 _43072).
Proof. exact (TRANS (@lem3741127 A _43071 _43072 R _43069 _43070) (@lem3741151 A _43071 R _43069 _43070 _43072)). Qed.
Lemma lem3741163 {A : Type'} (_43069 : A) (_43071 : A) : (term699 A _43069 _43071) = (term699 A _43069 _43071).
Proof. exact (eq_refl (term699 A _43069 _43071)). Qed.
Lemma lem3741164 {A : Type'} (_43071 : A) (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term656 A _43071 _43072 R _43069 _43070) = (term700 A _43071 R _43069 _43070 _43072).
Proof. exact (MK_COMB (@lem3741163 A _43069 _43071) (@lem3741162 A _43071 R _43069 _43070 _43072)). Qed.
Lemma lem3741168 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741169 {A : Type'} (_43071 : A) (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term700 A _43071 R _43069 _43070 _43072) = (term701 A _43071 R _43069 _43070 _43072).
Proof. exact (@lem3741168 (R _43071 _43072) (term606 A _43069 _43071) (term696 A R _43069 _43070 _43072)). Qed.
Lemma lem3741183 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741184 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term702 A _43071 R _43069 _43070 _43072) = (term703 A R _43069 _43071 _43070 _43072).
Proof. exact (@lem3741183 (term589 A R _43069 _43070) (term606 A _43069 _43071) (term606 A _43070 _43072)). Qed.
Lemma lem3741204 {A : Type'} (R : type1402 A) (_43071 : A) (_43072 : A) : (term697 A R _43071 _43072) = (term697 A R _43071 _43072).
Proof. exact (eq_refl (term697 A R _43071 _43072)). Qed.
Lemma lem3741205 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term701 A _43071 R _43069 _43070 _43072) = (term704 A R _43069 _43071 _43070 _43072).
Proof. exact (MK_COMB (@lem3741204 A R _43071 _43072) (@lem3741184 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741216 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term700 A _43071 R _43069 _43070 _43072) = (term704 A R _43069 _43071 _43070 _43072).
Proof. exact (TRANS (@lem3741169 A _43071 R _43069 _43070 _43072) (@lem3741205 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741217 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term656 A _43071 _43072 R _43069 _43070) = (term704 A R _43069 _43071 _43070 _43072).
Proof. exact (TRANS (@lem3741164 A _43071 R _43069 _43070 _43072) (@lem3741216 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741219 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term705 A _43071 _43072 R _43069 _43070) = (term706 A R _43069 _43071 _43070 _43072).
Proof. exact (MK_COMB (@lem3741218) (@lem3741217 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741245 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741246 {A : Type'} (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term695 A _43072 R _43069 _43070) = (term696 A R _43069 _43070 _43072).
Proof. exact (@lem3741245 (term589 A R _43069 _43070) (term606 A _43070 _43072)). Qed.
Lemma lem3741254 {A : Type'} (_43069 : A) (_43071 : A) : (term699 A _43069 _43071) = (term699 A _43069 _43071).
Proof. exact (eq_refl (term699 A _43069 _43071)). Qed.
Lemma lem3741255 {A : Type'} (_43071 : A) (R : type1402 A) (_43069 : A) (_43070 : A) (_43072 : A) : (term707 A _43071 _43072 R _43069 _43070) = (term702 A _43071 R _43069 _43070 _43072).
Proof. exact (MK_COMB (@lem3741254 A _43069 _43071) (@lem3741246 A R _43069 _43070 _43072)). Qed.
Lemma lem3741259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741260 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term702 A _43071 R _43069 _43070 _43072) = (term703 A R _43069 _43071 _43070 _43072).
Proof. exact (@lem3741259 (term589 A R _43069 _43070) (term606 A _43069 _43071) (term606 A _43070 _43072)). Qed.
Lemma lem3741280 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term707 A _43071 _43072 R _43069 _43070) = (term703 A R _43069 _43071 _43070 _43072).
Proof. exact (TRANS (@lem3741255 A _43071 R _43069 _43070 _43072) (@lem3741260 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741281 {A : Type'} (R : type1402 A) (_43071 : A) (_43072 : A) : (term697 A R _43071 _43072) = (term697 A R _43071 _43072).
Proof. exact (eq_refl (term697 A R _43071 _43072)). Qed.
Lemma lem3741282 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : (term708 A _43071 _43072 R _43069 _43070) = (term704 A R _43069 _43071 _43070 _43072).
Proof. exact (MK_COMB (@lem3741281 A R _43071 _43072) (@lem3741280 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741293 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : ((term656 A _43071 _43072 R _43069 _43070) = (term708 A _43071 _43072 R _43069 _43070)) = ((term704 A R _43069 _43071 _43070 _43072) = (term704 A R _43069 _43071 _43070 _43072)).
Proof. exact (MK_COMB (@lem3741219 A R _43069 _43071 _43070 _43072) (@lem3741282 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741296 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741295 Prop x). Qed.
Lemma lem3741297 {A : Type'} (R : type1402 A) (_43069 : A) (_43071 : A) (_43070 : A) (_43072 : A) : ((term704 A R _43069 _43071 _43070 _43072) = (term704 A R _43069 _43071 _43070 _43072)) = True.
Proof. exact (@lem3741296 (term704 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741298 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : ((term656 A _43071 _43072 R _43069 _43070) = (term708 A _43071 _43072 R _43069 _43070)) = True.
Proof. exact (TRANS (@lem3741293 A R _43069 _43071 _43070 _43072) (@lem3741297 A R _43069 _43071 _43070 _43072)). Qed.
Lemma lem3741299 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : True = ((term656 A _43071 _43072 R _43069 _43070) = (term708 A _43071 _43072 R _43069 _43070)).
Proof. exact (SYM (@lem3741298 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741300 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term656 A _43071 _43072 R _43069 _43070) = (term708 A _43071 _43072 R _43069 _43070).
Proof. exact (EQ_MP (@lem3741299 A _43071 _43072 R _43069 _43070) (@lem0)). Qed.
Lemma lem3741301 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : term708 A _43071 _43072 R _43069 _43070.
Proof. exact (EQ_MP (@lem3741300 A _43071 _43072 R _43069 _43070) (@lem3740810 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741303 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741304 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : (term708 A _43071 _43072 R _43069 _43070) = (term709 A _43069 _43070 R _43071 _43072).
Proof. exact (@lem3741303 (term707 A _43071 _43072 R _43069 _43070) (R _43071 _43072)). Qed.
Lemma lem3741306 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741307 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term710 A _43071 _43072 R _43069 _43070) = (term711 A _43071 _43072 R _43069 _43070).
Proof. exact (@lem3741306 (term606 A _43069 _43071) (term695 A _43072 R _43069 _43070)). Qed.
Lemma lem3741309 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741310 {A : Type'} (_43069 : A) (_43071 : A) : (term712 A _43069 _43071) = (_43069 = _43071).
Proof. exact (@lem3741309 (_43069 = _43071)). Qed.
Lemma lem3741311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741312 {A : Type'} (_43069 : A) (_43071 : A) : (term713 A _43069 _43071) = (term714 A _43069 _43071).
Proof. exact (MK_COMB (@lem3741311) (@lem3741310 A _43069 _43071)). Qed.
Lemma lem3741314 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741315 {A : Type'} (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term715 A _43072 R _43069 _43070) = (term716 A _43072 R _43069 _43070).
Proof. exact (@lem3741314 (term606 A _43070 _43072) (term589 A R _43069 _43070)). Qed.
Lemma lem3741317 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741318 {A : Type'} (_43070 : A) (_43072 : A) : (term712 A _43070 _43072) = (_43070 = _43072).
Proof. exact (@lem3741317 (_43070 = _43072)). Qed.
Lemma lem3741319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741320 {A : Type'} (_43070 : A) (_43072 : A) : (term713 A _43070 _43072) = (term714 A _43070 _43072).
Proof. exact (MK_COMB (@lem3741319) (@lem3741318 A _43070 _43072)). Qed.
Lemma lem3741322 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741323 {A : Type'} (R : type1402 A) (_43069 : A) (_43070 : A) : (term643 A R _43069 _43070) = (R _43069 _43070).
Proof. exact (@lem3741322 (R _43069 _43070)). Qed.
Lemma lem3741324 {A : Type'} (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term716 A _43072 R _43069 _43070) = (term717 A _43072 R _43069 _43070).
Proof. exact (MK_COMB (@lem3741320 A _43070 _43072) (@lem3741323 A R _43069 _43070)). Qed.
Lemma lem3741325 {A : Type'} (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term715 A _43072 R _43069 _43070) = (term717 A _43072 R _43069 _43070).
Proof. exact (TRANS (@lem3741315 A _43072 R _43069 _43070) (@lem3741324 A _43072 R _43069 _43070)). Qed.
Lemma lem3741326 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term711 A _43071 _43072 R _43069 _43070) = (term718 A _43071 _43072 R _43069 _43070).
Proof. exact (MK_COMB (@lem3741312 A _43069 _43071) (@lem3741325 A _43072 R _43069 _43070)). Qed.
Lemma lem3741327 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term710 A _43071 _43072 R _43069 _43070) = (term718 A _43071 _43072 R _43069 _43070).
Proof. exact (TRANS (@lem3741307 A _43071 _43072 R _43069 _43070) (@lem3741326 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741329 {A : Type'} (_43071 : A) (_43072 : A) (R : type1402 A) (_43069 : A) (_43070 : A) : (term719 A _43071 _43072 R _43069 _43070) = (term720 A _43071 _43072 R _43069 _43070).
Proof. exact (MK_COMB (@lem3741328) (@lem3741327 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741330 {A : Type'} (R : type1402 A) (_43071 : A) (_43072 : A) : (R _43071 _43072) = (R _43071 _43072).
Proof. exact (eq_refl (R _43071 _43072)). Qed.
Lemma lem3741331 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : (term709 A _43069 _43070 R _43071 _43072) = (term721 A _43069 _43070 R _43071 _43072).
Proof. exact (MK_COMB (@lem3741329 A _43071 _43072 R _43069 _43070) (@lem3741330 A R _43071 _43072)). Qed.
Lemma lem3741332 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : (term708 A _43071 _43072 R _43069 _43070) = (term721 A _43069 _43070 R _43071 _43072).
Proof. exact (TRANS (@lem3741304 A _43069 _43070 R _43071 _43072) (@lem3741331 A _43069 _43070 R _43071 _43072)). Qed.
Lemma lem3741334 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term722 A x R y x''.
Proof. exact (conj (@lem3741089 A x y s R x'' h1 h2) (@lem3741108 A x y s R x'' h1 h2)). Qed.
Lemma lem3741335 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term723 A x R y x''.
Proof. exact (conj (@lem3740878 A x'') (@lem3741334 A x y s R x'' h1 h2)). Qed.
Lemma lem3741337 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : term721 A _43069 _43070 R _43071 _43072.
Proof. exact (EQ_MP (@lem3741332 A _43069 _43070 R _43071 _43072) (@lem3741301 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741338 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : term721 A _43069 _43070 R _43071 _43072.
Proof. exact (@lem3741337 A _43069 _43070 R _43071 _43072). Qed.
Lemma lem3741339 {A : Type'} (y : A -> A) (R : type1402 A) (x'' : A) (x : A) : term724 A y R x'' x.
Proof. exact (@lem3741338 A x'' (y x'') R x'' x). Qed.
Lemma lem3741342 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x'' x.
Proof. exact (@lem3741339 A y R x'' x (@lem3741335 A x y s R x'' h1 h2)). Qed.
Lemma lem3741343 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term629 A R x'' x.
Proof. exact (fun h0 : term589 A R x'' x => @lem3741342 A x y s R x'' h1 h2). Qed.
Lemma lem3741345 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741346 {A : Type'} (R : type1402 A) (x'' : A) (x : A) : (term629 A R x'' x) = (R x'' x).
Proof. exact (@lem3741345 (R x'' x)). Qed.
Lemma lem3741347 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x'' x.
Proof. exact (EQ_MP (@lem3741346 A R x'' x) (@lem3741343 A x y s R x'' h1 h2)). Qed.
Lemma lem3741349 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3741350 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3741349 A x). Qed.
Lemma lem3741351 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3741350 A x). Qed.
Lemma lem3741353 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741354 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3741353 (x = x)). Qed.
Lemma lem3741355 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3741354 A x) (@lem3741351 A x)). Qed.
Lemma lem3741361 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741362 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : (term621 A x R y _42915) = (term725 A R y _42915 x).
Proof. exact (@lem3741361 (term566 A R y _42915) (term606 A _42915 x)). Qed.
Lemma lem3741370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741371 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : (term726 A x R y _42915) = (term727 A R y _42915 x).
Proof. exact (MK_COMB (@lem3741370) (@lem3741362 A R y _42915 x)). Qed.
Lemma lem3741379 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : (term725 A R y _42915 x) = (term725 A R y _42915 x).
Proof. exact (eq_refl (term725 A R y _42915 x)). Qed.
Lemma lem3741380 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : ((term621 A x R y _42915) = (term725 A R y _42915 x)) = ((term725 A R y _42915 x) = (term725 A R y _42915 x)).
Proof. exact (MK_COMB (@lem3741371 A R y _42915 x) (@lem3741379 A R y _42915 x)). Qed.
Lemma lem3741382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741383 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741382 Prop x). Qed.
Lemma lem3741384 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : ((term725 A R y _42915 x) = (term725 A R y _42915 x)) = True.
Proof. exact (@lem3741383 (term725 A R y _42915 x)). Qed.
Lemma lem3741385 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : ((term621 A x R y _42915) = (term725 A R y _42915 x)) = True.
Proof. exact (TRANS (@lem3741380 A R y _42915 x) (@lem3741384 A R y _42915 x)). Qed.
Lemma lem3741386 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : True = ((term621 A x R y _42915) = (term725 A R y _42915 x)).
Proof. exact (SYM (@lem3741385 A R y _42915 x)). Qed.
Lemma lem3741387 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) (x : A) : (term621 A x R y _42915) = (term725 A R y _42915 x).
Proof. exact (EQ_MP (@lem3741386 A R y _42915 x) (@lem0)). Qed.
Lemma lem3741388 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term725 A R y _42915 x.
Proof. exact (EQ_MP (@lem3741387 A R y _42915 x) (@lem3740037 A _42915 x s R y h1)). Qed.
Lemma lem3741390 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741391 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42915 : A) : (term725 A R y _42915 x) = (term728 A x R y _42915).
Proof. exact (@lem3741390 (term606 A _42915 x) (term566 A R y _42915)). Qed.
Lemma lem3741393 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741394 {A : Type'} (_42915 : A) (x : A) : (term712 A _42915 x) = (_42915 = x).
Proof. exact (@lem3741393 (_42915 = x)). Qed.
Lemma lem3741395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741396 {A : Type'} (_42915 : A) (x : A) : (term729 A _42915 x) = (term730 A _42915 x).
Proof. exact (MK_COMB (@lem3741395) (@lem3741394 A _42915 x)). Qed.
Lemma lem3741397 {A : Type'} (R : type1402 A) (y : A -> A) (_42915 : A) : (term566 A R y _42915) = (term566 A R y _42915).
Proof. exact (eq_refl (term566 A R y _42915)). Qed.
Lemma lem3741398 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42915 : A) : (term728 A x R y _42915) = (term731 A x R y _42915).
Proof. exact (MK_COMB (@lem3741396 A _42915 x) (@lem3741397 A R y _42915)). Qed.
Lemma lem3741399 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42915 : A) : (term725 A R y _42915 x) = (term731 A x R y _42915).
Proof. exact (TRANS (@lem3741391 A x R y _42915) (@lem3741398 A x R y _42915)). Qed.
Lemma lem3741402 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42915.
Proof. exact (EQ_MP (@lem3741399 A x R y _42915) (@lem3741388 A _42915 x s R y h1)). Qed.
Lemma lem3741403 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42915.
Proof. exact (@lem3741402 A _42915 x s R y h1). Qed.
Lemma lem3741404 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term732 A R y x.
Proof. exact (@lem3741403 A x x s R y h1). Qed.
Lemma lem3741407 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (@lem3741404 A x s R y h1 (@lem3741355 A x)). Qed.
Lemma lem3741408 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term668 A R y x.
Proof. exact (fun h0 : term669 A R y x => @lem3741407 A x s R y h1). Qed.
Lemma lem3741410 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741411 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : (term668 A R y x) = (term566 A R y x).
Proof. exact (@lem3741410 (term566 A R y x)). Qed.
Lemma lem3741412 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (EQ_MP (@lem3741411 A R y x) (@lem3741408 A x s R y h1)). Qed.
Lemma lem3741428 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741429 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term630 A _42913 R _42912 _42914) = (term631 A _42912 R _42913 _42914).
Proof. exact (@lem3741428 (R _42912 _42914) (term589 A R _42913 _42914)). Qed.
Lemma lem3741435 {A : Type'} (R : type1402 A) (_42912 : A) (_42913 : A) : (term632 A R _42912 _42913) = (term632 A R _42912 _42913).
Proof. exact (eq_refl (term632 A R _42912 _42913)). Qed.
Lemma lem3741436 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term620 A _42913 R _42912 _42914) = (term633 A _42912 R _42913 _42914).
Proof. exact (MK_COMB (@lem3741435 A R _42912 _42913) (@lem3741429 A _42912 R _42913 _42914)). Qed.
Lemma lem3741440 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741441 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term633 A _42912 R _42913 _42914) = (term634 A _42912 R _42913 _42914).
Proof. exact (@lem3741440 (R _42912 _42914) (term589 A R _42912 _42913) (term589 A R _42913 _42914)). Qed.
Lemma lem3741457 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term620 A _42913 R _42912 _42914) = (term634 A _42912 R _42913 _42914).
Proof. exact (TRANS (@lem3741436 A _42912 R _42913 _42914) (@lem3741441 A _42912 R _42913 _42914)). Qed.
Lemma lem3741458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741459 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term635 A _42913 R _42912 _42914) = (term636 A _42912 R _42913 _42914).
Proof. exact (MK_COMB (@lem3741458) (@lem3741457 A _42912 R _42913 _42914)). Qed.
Lemma lem3741475 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term634 A _42912 R _42913 _42914) = (term634 A _42912 R _42913 _42914).
Proof. exact (eq_refl (term634 A _42912 R _42913 _42914)). Qed.
Lemma lem3741476 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : ((term620 A _42913 R _42912 _42914) = (term634 A _42912 R _42913 _42914)) = ((term634 A _42912 R _42913 _42914) = (term634 A _42912 R _42913 _42914)).
Proof. exact (MK_COMB (@lem3741459 A _42912 R _42913 _42914) (@lem3741475 A _42912 R _42913 _42914)). Qed.
Lemma lem3741478 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741479 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741478 Prop x). Qed.
Lemma lem3741480 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : ((term634 A _42912 R _42913 _42914) = (term634 A _42912 R _42913 _42914)) = True.
Proof. exact (@lem3741479 (term634 A _42912 R _42913 _42914)). Qed.
Lemma lem3741481 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : ((term620 A _42913 R _42912 _42914) = (term634 A _42912 R _42913 _42914)) = True.
Proof. exact (TRANS (@lem3741476 A _42912 R _42913 _42914) (@lem3741480 A _42912 R _42913 _42914)). Qed.
Lemma lem3741482 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : True = ((term620 A _42913 R _42912 _42914) = (term634 A _42912 R _42913 _42914)).
Proof. exact (SYM (@lem3741481 A _42912 R _42913 _42914)). Qed.
Lemma lem3741483 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term620 A _42913 R _42912 _42914) = (term634 A _42912 R _42913 _42914).
Proof. exact (EQ_MP (@lem3741482 A _42912 R _42913 _42914) (@lem0)). Qed.
Lemma lem3741484 {A : Type'} (_42912 : A) (_42913 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term634 A _42912 R _42913 _42914.
Proof. exact (EQ_MP (@lem3741483 A _42912 R _42913 _42914) (@lem3739995 A _42913 _42912 _42914 x s R y h1)). Qed.
Lemma lem3741486 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741487 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) (_42914 : A) : (term634 A _42912 R _42913 _42914) = (term638 A _42913 R _42912 _42914).
Proof. exact (@lem3741486 (term475 A _42912 R _42913 _42914) (R _42912 _42914)). Qed.
Lemma lem3741489 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741490 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term641 A _42912 R _42913 _42914) = (term642 A _42912 R _42913 _42914).
Proof. exact (@lem3741489 (term589 A R _42912 _42913) (term589 A R _42913 _42914)). Qed.
Lemma lem3741492 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741493 {A : Type'} (R : type1402 A) (_42912 : A) (_42913 : A) : (term643 A R _42912 _42913) = (R _42912 _42913).
Proof. exact (@lem3741492 (R _42912 _42913)). Qed.
Lemma lem3741494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741495 {A : Type'} (R : type1402 A) (_42912 : A) (_42913 : A) : (term644 A R _42912 _42913) = (term645 A R _42912 _42913).
Proof. exact (MK_COMB (@lem3741494) (@lem3741493 A R _42912 _42913)). Qed.
Lemma lem3741497 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741498 {A : Type'} (R : type1402 A) (_42913 : A) (_42914 : A) : (term643 A R _42913 _42914) = (R _42913 _42914).
Proof. exact (@lem3741497 (R _42913 _42914)). Qed.
Lemma lem3741499 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term642 A _42912 R _42913 _42914) = (term207 A _42912 R _42913 _42914).
Proof. exact (MK_COMB (@lem3741495 A R _42912 _42913) (@lem3741498 A R _42913 _42914)). Qed.
Lemma lem3741500 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term641 A _42912 R _42913 _42914) = (term207 A _42912 R _42913 _42914).
Proof. exact (TRANS (@lem3741490 A _42912 R _42913 _42914) (@lem3741499 A _42912 R _42913 _42914)). Qed.
Lemma lem3741501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741502 {A : Type'} (_42912 : A) (R : type1402 A) (_42913 : A) (_42914 : A) : (term646 A _42912 R _42913 _42914) = (term647 A _42912 R _42913 _42914).
Proof. exact (MK_COMB (@lem3741501) (@lem3741500 A _42912 R _42913 _42914)). Qed.
Lemma lem3741503 {A : Type'} (R : type1402 A) (_42912 : A) (_42914 : A) : (R _42912 _42914) = (R _42912 _42914).
Proof. exact (eq_refl (R _42912 _42914)). Qed.
Lemma lem3741504 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) (_42914 : A) : (term638 A _42913 R _42912 _42914) = (term186 A _42913 R _42912 _42914).
Proof. exact (MK_COMB (@lem3741502 A _42912 R _42913 _42914) (@lem3741503 A R _42912 _42914)). Qed.
Lemma lem3741505 {A : Type'} (_42913 : A) (R : type1402 A) (_42912 : A) (_42914 : A) : (term634 A _42912 R _42913 _42914) = (term186 A _42913 R _42912 _42914).
Proof. exact (TRANS (@lem3741487 A _42913 R _42912 _42914) (@lem3741504 A _42913 R _42912 _42914)). Qed.
Lemma lem3741507 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term733 A x'' R y x.
Proof. exact (conj (@lem3741347 A x y s R x'' h1 h2) (@lem3741412 A x s R y h1)). Qed.
Lemma lem3741509 {A : Type'} (_42913 : A) (_42912 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42913 R _42912 _42914.
Proof. exact (EQ_MP (@lem3741505 A _42913 R _42912 _42914) (@lem3741484 A _42912 _42913 _42914 x s R y h1)). Qed.
Lemma lem3741510 {A : Type'} (_42913 : A) (_42912 : A) (_42914 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42913 R _42912 _42914.
Proof. exact (@lem3741509 A _42913 _42912 _42914 x s R y h1). Qed.
Lemma lem3741511 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term734 A R x'' y x.
Proof. exact (@lem3741510 A x x'' (y x) x s R y h1). Qed.
Lemma lem3741514 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term735 A R x'' y x.
Proof. exact (@lem3741511 A x'' x s R y h1 (@lem3741507 A x y s R x'' h1 h2)). Qed.
Lemma lem3741515 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term736 A R x'' y x.
Proof. exact (fun h0 : term737 A R x'' y x => @lem3741514 A x y s R x'' h1 h2). Qed.
Lemma lem3741517 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741518 {A : Type'} (R : type1402 A) (x'' : A) (y : A -> A) (x : A) : (term736 A R x'' y x) = (term735 A R x'' y x).
Proof. exact (@lem3741517 (term735 A R x'' y x)). Qed.
Lemma lem3741519 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term735 A R x'' y x.
Proof. exact (EQ_MP (@lem3741518 A R x'' y x) (@lem3741515 A x y s R x'' h1 h2)). Qed.
Lemma lem3741521 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42916.
Proof. exact (EQ_MP (@lem3740956 A R x'' s _42916) (@lem3740023 A _42916 s R x'' h1)). Qed.
Lemma lem3741522 {A : Type'} (_42916 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42916.
Proof. exact (@lem3741521 A _42916 s R x'' h1). Qed.
Lemma lem3741523 {A : Type'} (y : A -> A) (x : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term738 A R x'' s y x.
Proof. exact (@lem3741522 A (y x) s R x'' h1). Qed.
Lemma lem3741526 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x.
Proof. exact (@lem3741523 A y x s R x'' h2 (@lem3741519 A x y s R x'' h1 h2)). Qed.
Lemma lem3741527 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term676 A s y x.
Proof. exact (fun h0 : term568 A s y x => @lem3741526 A x y s R x'' h1 h2). Qed.
Lemma lem3741529 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3741530 {A : Type'} (s : A -> Prop) (y : A -> A) (x : A) : (term676 A s y x) = (term675 A s y x).
Proof. exact (@lem3741529 (term568 A s y x)). Qed.
Lemma lem3741531 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x.
Proof. exact (EQ_MP (@lem3741530 A s y x) (@lem3741527 A x y s R x'' h1 h2)). Qed.
Lemma lem3741537 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741538 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term623 A x s y _42915) = (term739 A x s y _42915).
Proof. exact (@lem3741537 ((y _42915) = x) (term606 A _42915 x) (term568 A s y _42915)). Qed.
Lemma lem3741554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741555 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term740 A x s y _42915) = (term741 A s y _42915 x).
Proof. exact (@lem3741554 (term568 A s y _42915) (term606 A _42915 x)). Qed.
Lemma lem3741563 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : (term569 A y _42915 x) = (term569 A y _42915 x).
Proof. exact (eq_refl (term569 A y _42915 x)). Qed.
Lemma lem3741564 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term739 A x s y _42915) = (term742 A s y _42915 x).
Proof. exact (MK_COMB (@lem3741563 A y _42915 x) (@lem3741555 A s y _42915 x)). Qed.
Lemma lem3741575 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term623 A x s y _42915) = (term742 A s y _42915 x).
Proof. exact (TRANS (@lem3741538 A x s y _42915) (@lem3741564 A s y _42915 x)). Qed.
Lemma lem3741576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741577 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term743 A x s y _42915) = (term744 A s y _42915 x).
Proof. exact (MK_COMB (@lem3741576) (@lem3741575 A s y _42915 x)). Qed.
Lemma lem3741593 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741594 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term740 A x s y _42915) = (term741 A s y _42915 x).
Proof. exact (@lem3741593 (term568 A s y _42915) (term606 A _42915 x)). Qed.
Lemma lem3741602 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : (term569 A y _42915 x) = (term569 A y _42915 x).
Proof. exact (eq_refl (term569 A y _42915 x)). Qed.
Lemma lem3741603 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term739 A x s y _42915) = (term742 A s y _42915 x).
Proof. exact (MK_COMB (@lem3741602 A y _42915 x) (@lem3741594 A s y _42915 x)). Qed.
Lemma lem3741614 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : ((term623 A x s y _42915) = (term739 A x s y _42915)) = ((term742 A s y _42915 x) = (term742 A s y _42915 x)).
Proof. exact (MK_COMB (@lem3741577 A s y _42915 x) (@lem3741603 A s y _42915 x)). Qed.
Lemma lem3741616 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741617 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741616 Prop x). Qed.
Lemma lem3741618 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : ((term742 A s y _42915 x) = (term742 A s y _42915 x)) = True.
Proof. exact (@lem3741617 (term742 A s y _42915 x)). Qed.
Lemma lem3741619 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : ((term623 A x s y _42915) = (term739 A x s y _42915)) = True.
Proof. exact (TRANS (@lem3741614 A s y _42915 x) (@lem3741618 A s y _42915 x)). Qed.
Lemma lem3741620 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : True = ((term623 A x s y _42915) = (term739 A x s y _42915)).
Proof. exact (SYM (@lem3741619 A x s y _42915)). Qed.
Lemma lem3741621 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term623 A x s y _42915) = (term739 A x s y _42915).
Proof. exact (EQ_MP (@lem3741620 A x s y _42915) (@lem0)). Qed.
Lemma lem3741622 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term739 A x s y _42915.
Proof. exact (EQ_MP (@lem3741621 A x s y _42915) (@lem3740065 A _42915 x s R y h1)). Qed.
Lemma lem3741624 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741625 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term739 A x s y _42915) = (term745 A s y _42915 x).
Proof. exact (@lem3741624 (term740 A x s y _42915) ((y _42915) = x)). Qed.
Lemma lem3741627 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741628 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term746 A x s y _42915) = (term747 A x s y _42915).
Proof. exact (@lem3741627 (term606 A _42915 x) (term568 A s y _42915)). Qed.
Lemma lem3741630 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741631 {A : Type'} (_42915 : A) (x : A) : (term712 A _42915 x) = (_42915 = x).
Proof. exact (@lem3741630 (_42915 = x)). Qed.
Lemma lem3741632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741633 {A : Type'} (_42915 : A) (x : A) : (term713 A _42915 x) = (term714 A _42915 x).
Proof. exact (MK_COMB (@lem3741632) (@lem3741631 A _42915 x)). Qed.
Lemma lem3741634 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) : (term675 A s y _42915) = (term675 A s y _42915).
Proof. exact (eq_refl (term675 A s y _42915)). Qed.
Lemma lem3741635 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term747 A x s y _42915) = (term748 A x s y _42915).
Proof. exact (MK_COMB (@lem3741633 A _42915 x) (@lem3741634 A s y _42915)). Qed.
Lemma lem3741636 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term746 A x s y _42915) = (term748 A x s y _42915).
Proof. exact (TRANS (@lem3741628 A x s y _42915) (@lem3741635 A x s y _42915)). Qed.
Lemma lem3741637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741638 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42915 : A) : (term749 A x s y _42915) = (term750 A x s y _42915).
Proof. exact (MK_COMB (@lem3741637) (@lem3741636 A x s y _42915)). Qed.
Lemma lem3741639 {A : Type'} (y : A -> A) (_42915 : A) (x : A) : ((y _42915) = x) = ((y _42915) = x).
Proof. exact (eq_refl ((y _42915) = x)). Qed.
Lemma lem3741640 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term745 A s y _42915 x) = (term751 A s y _42915 x).
Proof. exact (MK_COMB (@lem3741638 A x s y _42915) (@lem3741639 A y _42915 x)). Qed.
Lemma lem3741641 {A : Type'} (s : A -> Prop) (y : A -> A) (_42915 : A) (x : A) : (term739 A x s y _42915) = (term751 A s y _42915 x).
Proof. exact (TRANS (@lem3741625 A s y _42915 x) (@lem3741640 A s y _42915 x)). Qed.
Lemma lem3741643 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term752 A s y x.
Proof. exact (conj (@lem3740869 A x) (@lem3741531 A x y s R x'' h1 h2)). Qed.
Lemma lem3741645 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term751 A s y _42915 x.
Proof. exact (EQ_MP (@lem3741641 A s y _42915 x) (@lem3741622 A _42915 x s R y h1)). Qed.
Lemma lem3741646 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term751 A s y _42915 x.
Proof. exact (@lem3741645 A _42915 x s R y h1). Qed.
Lemma lem3741647 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term753 A s y x.
Proof. exact (@lem3741646 A x x s R y h1). Qed.
Lemma lem3741650 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x) = x.
Proof. exact (@lem3741647 A x s R y h1 (@lem3741643 A x y s R x'' h1 h2)). Qed.
Lemma lem3741651 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term754 A y x.
Proof. exact (fun h0 : term755 A y x => @lem3741650 A x y s R x'' h1 h2). Qed.
Lemma lem3741653 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741654 {A : Type'} (y : A -> A) (x : A) : (term754 A y x) = ((y x) = x).
Proof. exact (@lem3741653 ((y x) = x)). Qed.
Lemma lem3741655 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x) = x.
Proof. exact (EQ_MP (@lem3741654 A y x) (@lem3741651 A x y s R x'' h1 h2)). Qed.
Lemma lem3741657 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3741658 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3741657 A x). Qed.
Lemma lem3741659 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3741658 A x). Qed.
Lemma lem3741661 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741662 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3741661 (x = x)). Qed.
Lemma lem3741663 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3741662 A x) (@lem3741659 A x)). Qed.
Lemma lem3741665 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42915.
Proof. exact (EQ_MP (@lem3741399 A x R y _42915) (@lem3741388 A _42915 x s R y h1)). Qed.
Lemma lem3741666 {A : Type'} (_42915 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42915.
Proof. exact (@lem3741665 A _42915 x s R y h1). Qed.
Lemma lem3741667 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term732 A R y x.
Proof. exact (@lem3741666 A x x s R y h1). Qed.
Lemma lem3741670 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (@lem3741667 A x s R y h1 (@lem3741663 A x)). Qed.
Lemma lem3741671 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term668 A R y x.
Proof. exact (fun h0 : term669 A R y x => @lem3741670 A x s R y h1). Qed.
Lemma lem3741673 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741674 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : (term668 A R y x) = (term566 A R y x).
Proof. exact (@lem3741673 (term566 A R y x)). Qed.
Lemma lem3741675 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (EQ_MP (@lem3741674 A R y x) (@lem3741671 A x s R y h1)). Qed.
Lemma lem3741676 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term756 A R y x.
Proof. exact (conj (@lem3741655 A x y s R x'' h1 h2) (@lem3741675 A x s R y h1)). Qed.
Lemma lem3741677 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term757 A R y x.
Proof. exact (conj (@lem3740861 A x) (@lem3741676 A x y s R x'' h1 h2)). Qed.
Lemma lem3741679 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : term721 A _43069 _43070 R _43071 _43072.
Proof. exact (EQ_MP (@lem3741332 A _43069 _43070 R _43071 _43072) (@lem3741301 A _43071 _43072 R _43069 _43070)). Qed.
Lemma lem3741680 {A : Type'} (_43069 : A) (_43070 : A) (R : type1402 A) (_43071 : A) (_43072 : A) : term721 A _43069 _43070 R _43071 _43072.
Proof. exact (@lem3741679 A _43069 _43070 R _43071 _43072). Qed.
Lemma lem3741681 {A : Type'} (y : A -> A) (R : type1402 A) (x : A) : term758 A y R x.
Proof. exact (@lem3741680 A x (y x) R x x). Qed.
Lemma lem3741684 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x x.
Proof. exact (@lem3741681 A y R x (@lem3741677 A x y s R x'' h1 h2)). Qed.
Lemma lem3741685 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term625 A R x.
Proof. exact (fun h0 : term192 A R x => @lem3741684 A x y s R x'' h1 h2). Qed.
Lemma lem3741687 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741688 {A : Type'} (R : type1402 A) (x : A) : (term625 A R x) = (R x x).
Proof. exact (@lem3741687 (R x x)). Qed.
Lemma lem3741689 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x x.
Proof. exact (EQ_MP (@lem3741688 A R x) (@lem3741685 A x y s R x'' h1 h2)). Qed.
Lemma lem3741692 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3741694 {A : Type'} (R : type1402 A) (_42911 : A) : (term192 A R _42911) = (term627 A R _42911).
Proof. exact (@lem3741692 (R _42911 _42911)). Qed.
Lemma lem3741697 {A : Type'} (_42911 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42911.
Proof. exact (EQ_MP (@lem3741694 A R _42911) (@lem3739981 A _42911 x s R y h1)). Qed.
Lemma lem3741698 {A : Type'} (_42911 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42911.
Proof. exact (@lem3741697 A _42911 x s R y h1). Qed.
Lemma lem3741699 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R x.
Proof. exact (@lem3741698 A x x s R y h1). Qed.
Lemma lem3741702 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : False.
Proof. exact (@lem3741699 A x s R y h1 (@lem3741689 A x y s R x'' h1 h2)). Qed.
Lemma lem3741703 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term628.
Proof. exact (fun h0 : ~ False => @lem3741702 A x y s R x'' h1 h2). Qed.
Lemma lem3741705 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741706 : term628 = False.
Proof. exact (@lem3741705 False). Qed.
Lemma lem3741708 {A : Type'} (R : type1402 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem3741709 {A : Type'} (_43081 : A) (_43083 : A) (h1 : _43081 = _43083) : _43081 = _43083.
Proof. exact (h1). Qed.
Lemma lem3741710 {A : Type'} (_43082 : A) (_43084 : A) (h1 : _43082 = _43084) : _43082 = _43084.
Proof. exact (h1). Qed.
Lemma lem3741711 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (h1 : _43081 = _43083) : (R _43081) = (R _43083).
Proof. exact (MK_COMB (@lem3741708 A R) (@lem3741709 A _43081 _43083 h1)). Qed.
Lemma lem3741712 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) (h1 : _43081 = _43083) (h2 : _43082 = _43084) : (R _43081 _43082) = (R _43083 _43084).
Proof. exact (MK_COMB (@lem3741711 A R _43081 _43083 h1) (@lem3741710 A _43082 _43084 h2)). Qed.
Lemma lem3741714 (b : Prop) (a : Prop) : term649 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3741715 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : term650 A _43083 _43084 R _43081 _43082.
Proof. exact (@lem3741714 (R _43083 _43084) (R _43081 _43082)). Qed.
Lemma lem3741716 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) (h1 : _43081 = _43083) (h2 : _43082 = _43084) : term651 A _43083 _43084 R _43081 _43082.
Proof. exact (@lem3741715 A _43083 _43084 R _43081 _43082 (@lem3741712 A R _43081 _43083 _43082 _43084 h1 h2)). Qed.
Lemma lem3741717 {A : Type'} (_43084 : A) (R : type1402 A) (_43082 : A) (_43081 : A) (_43083 : A) (h1 : _43081 = _43083) : term652 A _43083 _43084 R _43081 _43082.
Proof. exact (fun h0 : _43082 = _43084 => @lem3741716 A R _43081 _43083 _43082 _43084 h1 h0). Qed.
Lemma lem3741719 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3741720 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term652 A _43083 _43084 R _43081 _43082) = (term654 A _43083 _43084 R _43081 _43082).
Proof. exact (@lem3741719 (_43082 = _43084) (term651 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3741721 {A : Type'} (_43084 : A) (R : type1402 A) (_43082 : A) (_43081 : A) (_43083 : A) (h1 : _43081 = _43083) : term654 A _43083 _43084 R _43081 _43082.
Proof. exact (EQ_MP (@lem3741720 A _43083 _43084 R _43081 _43082) (@lem3741717 A _43084 R _43082 _43081 _43083 h1)). Qed.
Lemma lem3741722 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : term655 A _43083 _43084 R _43081 _43082.
Proof. exact (fun h0 : _43081 = _43083 => @lem3741721 A _43084 R _43082 _43081 _43083 h0). Qed.
Lemma lem3741724 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3741725 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term655 A _43083 _43084 R _43081 _43082) = (term656 A _43083 _43084 R _43081 _43082).
Proof. exact (@lem3741724 (_43081 = _43083) (term654 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3741726 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : term656 A _43083 _43084 R _43081 _43082.
Proof. exact (EQ_MP (@lem3741725 A _43083 _43084 R _43081 _43082) (@lem3741722 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3741771 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3741772 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3741771 A x). Qed.
Lemma lem3741773 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3741772 A x). Qed.
Lemma lem3741775 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741776 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3741775 (x = x)). Qed.
Lemma lem3741777 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3741776 A x) (@lem3741773 A x)). Qed.
Lemma lem3741779 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3741780 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3741779 A x). Qed.
Lemma lem3741781 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3741780 A x). Qed.
Lemma lem3741783 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741784 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3741783 (x = x)). Qed.
Lemma lem3741785 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3741784 A x) (@lem3741781 A x)). Qed.
Lemma lem3741787 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3741788 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3741787 A x). Qed.
Lemma lem3741789 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (@lem3741788 A x''). Qed.
Lemma lem3741790 {A : Type'} (x'' : A) : term657 A x''.
Proof. exact (fun h0 : term658 A x'' => @lem3741789 A x''). Qed.
Lemma lem3741792 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741793 {A : Type'} (x'' : A) : (term657 A x'') = (x'' = x'').
Proof. exact (@lem3741792 (x'' = x'')). Qed.
Lemma lem3741794 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (EQ_MP (@lem3741793 A x'') (@lem3741790 A x'')). Qed.
Lemma lem3741796 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3741797 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3741796 A s R x'' h1). Qed.
Lemma lem3741799 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741800 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3741799 (@I (A -> Prop) s x'')). Qed.
Lemma lem3741801 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3741800 A s x'') (@lem3741797 A s R x'' h1)). Qed.
Lemma lem3741803 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3741804 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3741803 A s R x'' h1). Qed.
Lemma lem3741806 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741807 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3741806 (@I (A -> Prop) s x'')). Qed.
Lemma lem3741808 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3741807 A s x'') (@lem3741804 A s R x'' h1)). Qed.
Lemma lem3741814 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741815 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term622 A s R y _42921) = (term660 A R y s _42921).
Proof. exact (@lem3741814 (term566 A R y _42921) (term576 A s _42921)). Qed.
Lemma lem3741821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741822 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term661 A s R y _42921) = (term662 A R y s _42921).
Proof. exact (MK_COMB (@lem3741821) (@lem3741815 A R y s _42921)). Qed.
Lemma lem3741828 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term660 A R y s _42921) = (term660 A R y s _42921).
Proof. exact (eq_refl (term660 A R y s _42921)). Qed.
Lemma lem3741829 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : ((term622 A s R y _42921) = (term660 A R y s _42921)) = ((term660 A R y s _42921) = (term660 A R y s _42921)).
Proof. exact (MK_COMB (@lem3741822 A R y s _42921) (@lem3741828 A R y s _42921)). Qed.
Lemma lem3741831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741832 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741831 Prop x). Qed.
Lemma lem3741833 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : ((term660 A R y s _42921) = (term660 A R y s _42921)) = True.
Proof. exact (@lem3741832 (term660 A R y s _42921)). Qed.
Lemma lem3741834 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : ((term622 A s R y _42921) = (term660 A R y s _42921)) = True.
Proof. exact (TRANS (@lem3741829 A R y s _42921) (@lem3741833 A R y s _42921)). Qed.
Lemma lem3741835 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : True = ((term622 A s R y _42921) = (term660 A R y s _42921)).
Proof. exact (SYM (@lem3741834 A R y s _42921)). Qed.
Lemma lem3741836 {A : Type'} (R : type1402 A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term622 A s R y _42921) = (term660 A R y s _42921).
Proof. exact (EQ_MP (@lem3741835 A R y s _42921) (@lem0)). Qed.
Lemma lem3741837 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term660 A R y s _42921.
Proof. exact (EQ_MP (@lem3741836 A R y s _42921) (@lem3739489 A _42921 x s R y h1)). Qed.
Lemma lem3741839 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741840 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42921 : A) : (term660 A R y s _42921) = (term663 A s R y _42921).
Proof. exact (@lem3741839 (term576 A s _42921) (term566 A R y _42921)). Qed.
Lemma lem3741842 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741843 {A : Type'} (s : A -> Prop) (_42921 : A) : (term664 A s _42921) = (@I (A -> Prop) s _42921).
Proof. exact (@lem3741842 (@I (A -> Prop) s _42921)). Qed.
Lemma lem3741844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741845 {A : Type'} (s : A -> Prop) (_42921 : A) : (term665 A s _42921) = (term666 A s _42921).
Proof. exact (MK_COMB (@lem3741844) (@lem3741843 A s _42921)). Qed.
Lemma lem3741846 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) : (term566 A R y _42921) = (term566 A R y _42921).
Proof. exact (eq_refl (term566 A R y _42921)). Qed.
Lemma lem3741847 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42921 : A) : (term663 A s R y _42921) = (term667 A s R y _42921).
Proof. exact (MK_COMB (@lem3741845 A s _42921) (@lem3741846 A R y _42921)). Qed.
Lemma lem3741848 {A : Type'} (s : A -> Prop) (R : type1402 A) (y : A -> A) (_42921 : A) : (term660 A R y s _42921) = (term667 A s R y _42921).
Proof. exact (TRANS (@lem3741840 A s R y _42921) (@lem3741847 A s R y _42921)). Qed.
Lemma lem3741851 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42921.
Proof. exact (EQ_MP (@lem3741848 A s R y _42921) (@lem3741837 A _42921 x s R y h1)). Qed.
Lemma lem3741852 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42921.
Proof. exact (@lem3741851 A _42921 x s R y h1). Qed.
Lemma lem3741853 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y x''.
Proof. exact (@lem3741852 A x'' x s R y h1). Qed.
Lemma lem3741856 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (@lem3741853 A x'' x s R y h1 (@lem3741808 A s R x'' h2)). Qed.
Lemma lem3741857 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term668 A R y x''.
Proof. exact (fun h0 : term669 A R y x'' => @lem3741856 A x y s R x'' h1 h2). Qed.
Lemma lem3741859 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3741860 {A : Type'} (R : type1402 A) (y : A -> A) (x'' : A) : (term668 A R y x'') = (term566 A R y x'').
Proof. exact (@lem3741859 (term566 A R y x'')). Qed.
Lemma lem3741861 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (EQ_MP (@lem3741860 A R y x'') (@lem3741857 A x y s R x'' h1 h2)). Qed.
Lemma lem3741863 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741864 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42922 : A) : (term592 A s R x'' _42922) = (term670 A R x'' s _42922).
Proof. exact (@lem3741863 (term589 A R x'' _42922) (term576 A s _42922)). Qed.
Lemma lem3741866 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741867 {A : Type'} (R : type1402 A) (x'' : A) (_42922 : A) : (term643 A R x'' _42922) = (R x'' _42922).
Proof. exact (@lem3741866 (R x'' _42922)). Qed.
Lemma lem3741868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741869 {A : Type'} (R : type1402 A) (x'' : A) (_42922 : A) : (term671 A R x'' _42922) = (term672 A R x'' _42922).
Proof. exact (MK_COMB (@lem3741868) (@lem3741867 A R x'' _42922)). Qed.
Lemma lem3741870 {A : Type'} (s : A -> Prop) (_42922 : A) : (term576 A s _42922) = (term576 A s _42922).
Proof. exact (eq_refl (term576 A s _42922)). Qed.
Lemma lem3741871 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42922 : A) : (term670 A R x'' s _42922) = (term673 A R x'' s _42922).
Proof. exact (MK_COMB (@lem3741869 A R x'' _42922) (@lem3741870 A s _42922)). Qed.
Lemma lem3741872 {A : Type'} (R : type1402 A) (x'' : A) (s : A -> Prop) (_42922 : A) : (term592 A s R x'' _42922) = (term673 A R x'' s _42922).
Proof. exact (TRANS (@lem3741864 A R x'' s _42922) (@lem3741871 A R x'' s _42922)). Qed.
Lemma lem3741875 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42922.
Proof. exact (EQ_MP (@lem3741872 A R x'' s _42922) (@lem3739475 A _42922 s R x'' h1)). Qed.
Lemma lem3741876 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42922.
Proof. exact (@lem3741875 A _42922 s R x'' h1). Qed.
Lemma lem3741877 {A : Type'} (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term674 A R s y x''.
Proof. exact (@lem3741876 A (y x'') s R x'' h1). Qed.
Lemma lem3741880 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x''.
Proof. exact (@lem3741877 A y s R x'' h2 (@lem3741861 A x y s R x'' h1 h2)). Qed.
Lemma lem3741881 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term676 A s y x''.
Proof. exact (fun h0 : term568 A s y x'' => @lem3741880 A x y s R x'' h1 h2). Qed.
Lemma lem3741883 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3741884 {A : Type'} (s : A -> Prop) (y : A -> A) (x'' : A) : (term676 A s y x'') = (term675 A s y x'').
Proof. exact (@lem3741883 (term568 A s y x'')). Qed.
Lemma lem3741885 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x''.
Proof. exact (EQ_MP (@lem3741884 A s y x'') (@lem3741881 A x y s R x'' h1 h2)). Qed.
Lemma lem3741891 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3741892 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term624 A x s y _42921) = (term678 A x s y _42921).
Proof. exact (@lem3741891 ((y _42921) = x) (term576 A s _42921) (term568 A s y _42921)). Qed.
Lemma lem3741908 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741909 {A : Type'} (y : A -> A) (s : A -> Prop) (_42921 : A) : (term679 A s y _42921) = (term680 A y s _42921).
Proof. exact (@lem3741908 (term568 A s y _42921) (term576 A s _42921)). Qed.
Lemma lem3741915 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : (term569 A y _42921 x) = (term569 A y _42921 x).
Proof. exact (eq_refl (term569 A y _42921 x)). Qed.
Lemma lem3741916 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term678 A x s y _42921) = (term681 A x y s _42921).
Proof. exact (MK_COMB (@lem3741915 A y _42921 x) (@lem3741909 A y s _42921)). Qed.
Lemma lem3741927 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term624 A x s y _42921) = (term681 A x y s _42921).
Proof. exact (TRANS (@lem3741892 A x s y _42921) (@lem3741916 A x y s _42921)). Qed.
Lemma lem3741928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3741929 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term682 A x s y _42921) = (term683 A x y s _42921).
Proof. exact (MK_COMB (@lem3741928) (@lem3741927 A x y s _42921)). Qed.
Lemma lem3741945 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3741946 {A : Type'} (y : A -> A) (s : A -> Prop) (_42921 : A) : (term679 A s y _42921) = (term680 A y s _42921).
Proof. exact (@lem3741945 (term568 A s y _42921) (term576 A s _42921)). Qed.
Lemma lem3741952 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : (term569 A y _42921 x) = (term569 A y _42921 x).
Proof. exact (eq_refl (term569 A y _42921 x)). Qed.
Lemma lem3741953 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : (term678 A x s y _42921) = (term681 A x y s _42921).
Proof. exact (MK_COMB (@lem3741952 A y _42921 x) (@lem3741946 A y s _42921)). Qed.
Lemma lem3741964 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : ((term624 A x s y _42921) = (term678 A x s y _42921)) = ((term681 A x y s _42921) = (term681 A x y s _42921)).
Proof. exact (MK_COMB (@lem3741929 A x y s _42921) (@lem3741953 A x y s _42921)). Qed.
Lemma lem3741966 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3741967 (x : Prop) : (x = x) = True.
Proof. exact (@lem3741966 Prop x). Qed.
Lemma lem3741968 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (_42921 : A) : ((term681 A x y s _42921) = (term681 A x y s _42921)) = True.
Proof. exact (@lem3741967 (term681 A x y s _42921)). Qed.
Lemma lem3741969 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : ((term624 A x s y _42921) = (term678 A x s y _42921)) = True.
Proof. exact (TRANS (@lem3741964 A x y s _42921) (@lem3741968 A x y s _42921)). Qed.
Lemma lem3741970 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : True = ((term624 A x s y _42921) = (term678 A x s y _42921)).
Proof. exact (SYM (@lem3741969 A x s y _42921)). Qed.
Lemma lem3741971 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term624 A x s y _42921) = (term678 A x s y _42921).
Proof. exact (EQ_MP (@lem3741970 A x s y _42921) (@lem0)). Qed.
Lemma lem3741972 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term678 A x s y _42921.
Proof. exact (EQ_MP (@lem3741971 A x s y _42921) (@lem3739509 A _42921 x s R y h1)). Qed.
Lemma lem3741974 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3741975 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term678 A x s y _42921) = (term684 A s y _42921 x).
Proof. exact (@lem3741974 (term679 A s y _42921) ((y _42921) = x)). Qed.
Lemma lem3741977 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3741978 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term685 A s y _42921) = (term686 A s y _42921).
Proof. exact (@lem3741977 (term576 A s _42921) (term568 A s y _42921)). Qed.
Lemma lem3741980 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3741981 {A : Type'} (s : A -> Prop) (_42921 : A) : (term664 A s _42921) = (@I (A -> Prop) s _42921).
Proof. exact (@lem3741980 (@I (A -> Prop) s _42921)). Qed.
Lemma lem3741982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3741983 {A : Type'} (s : A -> Prop) (_42921 : A) : (term687 A s _42921) = (term595 A s _42921).
Proof. exact (MK_COMB (@lem3741982) (@lem3741981 A s _42921)). Qed.
Lemma lem3741984 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term675 A s y _42921) = (term675 A s y _42921).
Proof. exact (eq_refl (term675 A s y _42921)). Qed.
Lemma lem3741985 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term686 A s y _42921) = (term688 A s y _42921).
Proof. exact (MK_COMB (@lem3741983 A s _42921) (@lem3741984 A s y _42921)). Qed.
Lemma lem3741986 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term685 A s y _42921) = (term688 A s y _42921).
Proof. exact (TRANS (@lem3741978 A s y _42921) (@lem3741985 A s y _42921)). Qed.
Lemma lem3741987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3741988 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term689 A s y _42921) = (term690 A s y _42921).
Proof. exact (MK_COMB (@lem3741987) (@lem3741986 A s y _42921)). Qed.
Lemma lem3741989 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : ((y _42921) = x) = ((y _42921) = x).
Proof. exact (eq_refl ((y _42921) = x)). Qed.
Lemma lem3741990 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term684 A s y _42921 x) = (term691 A s y _42921 x).
Proof. exact (MK_COMB (@lem3741988 A s y _42921) (@lem3741989 A y _42921 x)). Qed.
Lemma lem3741991 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term678 A x s y _42921) = (term691 A s y _42921 x).
Proof. exact (TRANS (@lem3741975 A s y _42921 x) (@lem3741990 A s y _42921 x)). Qed.
Lemma lem3741993 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term688 A s y x''.
Proof. exact (conj (@lem3741801 A s R x'' h2) (@lem3741885 A x y s R x'' h1 h2)). Qed.
Lemma lem3741995 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y _42921 x.
Proof. exact (EQ_MP (@lem3741991 A s y _42921 x) (@lem3741972 A _42921 x s R y h1)). Qed.
Lemma lem3741996 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y _42921 x.
Proof. exact (@lem3741995 A _42921 x s R y h1). Qed.
Lemma lem3741997 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term691 A s y x'' x.
Proof. exact (@lem3741996 A x'' x s R y h1). Qed.
Lemma lem3742000 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x'') = x.
Proof. exact (@lem3741997 A x'' x s R y h1 (@lem3741993 A x y s R x'' h1 h2)). Qed.
Lemma lem3742001 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term692 A y x'' x.
Proof. exact (fun h0 : term693 A y x'' x => @lem3742000 A x y s R x'' h1 h2). Qed.
Lemma lem3742003 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742004 {A : Type'} (y : A -> A) (x'' : A) (x : A) : (term692 A y x'' x) = ((y x'') = x).
Proof. exact (@lem3742003 ((y x'') = x)). Qed.
Lemma lem3742005 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x'') = x.
Proof. exact (EQ_MP (@lem3742004 A y x'' x) (@lem3742001 A x y s R x'' h1 h2)). Qed.
Lemma lem3742007 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (proj1 (@lem3738181 A s R x'' h1)). Qed.
Lemma lem3742008 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term659 A s x''.
Proof. exact (fun h0 : term576 A s x'' => @lem3742007 A s R x'' h1). Qed.
Lemma lem3742010 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742011 {A : Type'} (s : A -> Prop) (x'' : A) : (term659 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3742010 (@I (A -> Prop) s x'')). Qed.
Lemma lem3742012 {A : Type'} (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3742011 A s x'') (@lem3742008 A s R x'' h1)). Qed.
Lemma lem3742014 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42921.
Proof. exact (EQ_MP (@lem3741848 A s R y _42921) (@lem3741837 A _42921 x s R y h1)). Qed.
Lemma lem3742015 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y _42921.
Proof. exact (@lem3742014 A _42921 x s R y h1). Qed.
Lemma lem3742016 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term667 A s R y x''.
Proof. exact (@lem3742015 A x'' x s R y h1). Qed.
Lemma lem3742019 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (@lem3742016 A x'' x s R y h1 (@lem3742012 A s R x'' h2)). Qed.
Lemma lem3742020 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term668 A R y x''.
Proof. exact (fun h0 : term669 A R y x'' => @lem3742019 A x y s R x'' h1 h2). Qed.
Lemma lem3742022 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742023 {A : Type'} (R : type1402 A) (y : A -> A) (x'' : A) : (term668 A R y x'') = (term566 A R y x'').
Proof. exact (@lem3742022 (term566 A R y x'')). Qed.
Lemma lem3742024 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term566 A R y x''.
Proof. exact (EQ_MP (@lem3742023 A R y x'') (@lem3742020 A x y s R x'' h1 h2)). Qed.
Lemma lem3742042 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742043 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term654 A _43083 _43084 R _43081 _43082) = (term694 A _43083 _43084 R _43081 _43082).
Proof. exact (@lem3742042 (R _43083 _43084) (term606 A _43082 _43084) (term589 A R _43081 _43082)). Qed.
Lemma lem3742057 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742058 {A : Type'} (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term695 A _43084 R _43081 _43082) = (term696 A R _43081 _43082 _43084).
Proof. exact (@lem3742057 (term589 A R _43081 _43082) (term606 A _43082 _43084)). Qed.
Lemma lem3742066 {A : Type'} (R : type1402 A) (_43083 : A) (_43084 : A) : (term697 A R _43083 _43084) = (term697 A R _43083 _43084).
Proof. exact (eq_refl (term697 A R _43083 _43084)). Qed.
Lemma lem3742067 {A : Type'} (_43083 : A) (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term694 A _43083 _43084 R _43081 _43082) = (term698 A _43083 R _43081 _43082 _43084).
Proof. exact (MK_COMB (@lem3742066 A R _43083 _43084) (@lem3742058 A R _43081 _43082 _43084)). Qed.
Lemma lem3742078 {A : Type'} (_43083 : A) (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term654 A _43083 _43084 R _43081 _43082) = (term698 A _43083 R _43081 _43082 _43084).
Proof. exact (TRANS (@lem3742043 A _43083 _43084 R _43081 _43082) (@lem3742067 A _43083 R _43081 _43082 _43084)). Qed.
Lemma lem3742079 {A : Type'} (_43081 : A) (_43083 : A) : (term699 A _43081 _43083) = (term699 A _43081 _43083).
Proof. exact (eq_refl (term699 A _43081 _43083)). Qed.
Lemma lem3742080 {A : Type'} (_43083 : A) (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term656 A _43083 _43084 R _43081 _43082) = (term700 A _43083 R _43081 _43082 _43084).
Proof. exact (MK_COMB (@lem3742079 A _43081 _43083) (@lem3742078 A _43083 R _43081 _43082 _43084)). Qed.
Lemma lem3742084 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742085 {A : Type'} (_43083 : A) (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term700 A _43083 R _43081 _43082 _43084) = (term701 A _43083 R _43081 _43082 _43084).
Proof. exact (@lem3742084 (R _43083 _43084) (term606 A _43081 _43083) (term696 A R _43081 _43082 _43084)). Qed.
Lemma lem3742099 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742100 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term702 A _43083 R _43081 _43082 _43084) = (term703 A R _43081 _43083 _43082 _43084).
Proof. exact (@lem3742099 (term589 A R _43081 _43082) (term606 A _43081 _43083) (term606 A _43082 _43084)). Qed.
Lemma lem3742120 {A : Type'} (R : type1402 A) (_43083 : A) (_43084 : A) : (term697 A R _43083 _43084) = (term697 A R _43083 _43084).
Proof. exact (eq_refl (term697 A R _43083 _43084)). Qed.
Lemma lem3742121 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term701 A _43083 R _43081 _43082 _43084) = (term704 A R _43081 _43083 _43082 _43084).
Proof. exact (MK_COMB (@lem3742120 A R _43083 _43084) (@lem3742100 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742132 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term700 A _43083 R _43081 _43082 _43084) = (term704 A R _43081 _43083 _43082 _43084).
Proof. exact (TRANS (@lem3742085 A _43083 R _43081 _43082 _43084) (@lem3742121 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742133 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term656 A _43083 _43084 R _43081 _43082) = (term704 A R _43081 _43083 _43082 _43084).
Proof. exact (TRANS (@lem3742080 A _43083 R _43081 _43082 _43084) (@lem3742132 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742135 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term705 A _43083 _43084 R _43081 _43082) = (term706 A R _43081 _43083 _43082 _43084).
Proof. exact (MK_COMB (@lem3742134) (@lem3742133 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742161 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742162 {A : Type'} (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term695 A _43084 R _43081 _43082) = (term696 A R _43081 _43082 _43084).
Proof. exact (@lem3742161 (term589 A R _43081 _43082) (term606 A _43082 _43084)). Qed.
Lemma lem3742170 {A : Type'} (_43081 : A) (_43083 : A) : (term699 A _43081 _43083) = (term699 A _43081 _43083).
Proof. exact (eq_refl (term699 A _43081 _43083)). Qed.
Lemma lem3742171 {A : Type'} (_43083 : A) (R : type1402 A) (_43081 : A) (_43082 : A) (_43084 : A) : (term707 A _43083 _43084 R _43081 _43082) = (term702 A _43083 R _43081 _43082 _43084).
Proof. exact (MK_COMB (@lem3742170 A _43081 _43083) (@lem3742162 A R _43081 _43082 _43084)). Qed.
Lemma lem3742175 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742176 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term702 A _43083 R _43081 _43082 _43084) = (term703 A R _43081 _43083 _43082 _43084).
Proof. exact (@lem3742175 (term589 A R _43081 _43082) (term606 A _43081 _43083) (term606 A _43082 _43084)). Qed.
Lemma lem3742196 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term707 A _43083 _43084 R _43081 _43082) = (term703 A R _43081 _43083 _43082 _43084).
Proof. exact (TRANS (@lem3742171 A _43083 R _43081 _43082 _43084) (@lem3742176 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742197 {A : Type'} (R : type1402 A) (_43083 : A) (_43084 : A) : (term697 A R _43083 _43084) = (term697 A R _43083 _43084).
Proof. exact (eq_refl (term697 A R _43083 _43084)). Qed.
Lemma lem3742198 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : (term708 A _43083 _43084 R _43081 _43082) = (term704 A R _43081 _43083 _43082 _43084).
Proof. exact (MK_COMB (@lem3742197 A R _43083 _43084) (@lem3742196 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742209 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : ((term656 A _43083 _43084 R _43081 _43082) = (term708 A _43083 _43084 R _43081 _43082)) = ((term704 A R _43081 _43083 _43082 _43084) = (term704 A R _43081 _43083 _43082 _43084)).
Proof. exact (MK_COMB (@lem3742135 A R _43081 _43083 _43082 _43084) (@lem3742198 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3742212 (x : Prop) : (x = x) = True.
Proof. exact (@lem3742211 Prop x). Qed.
Lemma lem3742213 {A : Type'} (R : type1402 A) (_43081 : A) (_43083 : A) (_43082 : A) (_43084 : A) : ((term704 A R _43081 _43083 _43082 _43084) = (term704 A R _43081 _43083 _43082 _43084)) = True.
Proof. exact (@lem3742212 (term704 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742214 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : ((term656 A _43083 _43084 R _43081 _43082) = (term708 A _43083 _43084 R _43081 _43082)) = True.
Proof. exact (TRANS (@lem3742209 A R _43081 _43083 _43082 _43084) (@lem3742213 A R _43081 _43083 _43082 _43084)). Qed.
Lemma lem3742215 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : True = ((term656 A _43083 _43084 R _43081 _43082) = (term708 A _43083 _43084 R _43081 _43082)).
Proof. exact (SYM (@lem3742214 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742216 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term656 A _43083 _43084 R _43081 _43082) = (term708 A _43083 _43084 R _43081 _43082).
Proof. exact (EQ_MP (@lem3742215 A _43083 _43084 R _43081 _43082) (@lem0)). Qed.
Lemma lem3742217 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : term708 A _43083 _43084 R _43081 _43082.
Proof. exact (EQ_MP (@lem3742216 A _43083 _43084 R _43081 _43082) (@lem3741726 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742219 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3742220 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : (term708 A _43083 _43084 R _43081 _43082) = (term709 A _43081 _43082 R _43083 _43084).
Proof. exact (@lem3742219 (term707 A _43083 _43084 R _43081 _43082) (R _43083 _43084)). Qed.
Lemma lem3742222 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3742223 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term710 A _43083 _43084 R _43081 _43082) = (term711 A _43083 _43084 R _43081 _43082).
Proof. exact (@lem3742222 (term606 A _43081 _43083) (term695 A _43084 R _43081 _43082)). Qed.
Lemma lem3742225 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742226 {A : Type'} (_43081 : A) (_43083 : A) : (term712 A _43081 _43083) = (_43081 = _43083).
Proof. exact (@lem3742225 (_43081 = _43083)). Qed.
Lemma lem3742227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3742228 {A : Type'} (_43081 : A) (_43083 : A) : (term713 A _43081 _43083) = (term714 A _43081 _43083).
Proof. exact (MK_COMB (@lem3742227) (@lem3742226 A _43081 _43083)). Qed.
Lemma lem3742230 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3742231 {A : Type'} (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term715 A _43084 R _43081 _43082) = (term716 A _43084 R _43081 _43082).
Proof. exact (@lem3742230 (term606 A _43082 _43084) (term589 A R _43081 _43082)). Qed.
Lemma lem3742233 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742234 {A : Type'} (_43082 : A) (_43084 : A) : (term712 A _43082 _43084) = (_43082 = _43084).
Proof. exact (@lem3742233 (_43082 = _43084)). Qed.
Lemma lem3742235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3742236 {A : Type'} (_43082 : A) (_43084 : A) : (term713 A _43082 _43084) = (term714 A _43082 _43084).
Proof. exact (MK_COMB (@lem3742235) (@lem3742234 A _43082 _43084)). Qed.
Lemma lem3742238 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742239 {A : Type'} (R : type1402 A) (_43081 : A) (_43082 : A) : (term643 A R _43081 _43082) = (R _43081 _43082).
Proof. exact (@lem3742238 (R _43081 _43082)). Qed.
Lemma lem3742240 {A : Type'} (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term716 A _43084 R _43081 _43082) = (term717 A _43084 R _43081 _43082).
Proof. exact (MK_COMB (@lem3742236 A _43082 _43084) (@lem3742239 A R _43081 _43082)). Qed.
Lemma lem3742241 {A : Type'} (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term715 A _43084 R _43081 _43082) = (term717 A _43084 R _43081 _43082).
Proof. exact (TRANS (@lem3742231 A _43084 R _43081 _43082) (@lem3742240 A _43084 R _43081 _43082)). Qed.
Lemma lem3742242 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term711 A _43083 _43084 R _43081 _43082) = (term718 A _43083 _43084 R _43081 _43082).
Proof. exact (MK_COMB (@lem3742228 A _43081 _43083) (@lem3742241 A _43084 R _43081 _43082)). Qed.
Lemma lem3742243 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term710 A _43083 _43084 R _43081 _43082) = (term718 A _43083 _43084 R _43081 _43082).
Proof. exact (TRANS (@lem3742223 A _43083 _43084 R _43081 _43082) (@lem3742242 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3742245 {A : Type'} (_43083 : A) (_43084 : A) (R : type1402 A) (_43081 : A) (_43082 : A) : (term719 A _43083 _43084 R _43081 _43082) = (term720 A _43083 _43084 R _43081 _43082).
Proof. exact (MK_COMB (@lem3742244) (@lem3742243 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742246 {A : Type'} (R : type1402 A) (_43083 : A) (_43084 : A) : (R _43083 _43084) = (R _43083 _43084).
Proof. exact (eq_refl (R _43083 _43084)). Qed.
Lemma lem3742247 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : (term709 A _43081 _43082 R _43083 _43084) = (term721 A _43081 _43082 R _43083 _43084).
Proof. exact (MK_COMB (@lem3742245 A _43083 _43084 R _43081 _43082) (@lem3742246 A R _43083 _43084)). Qed.
Lemma lem3742248 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : (term708 A _43083 _43084 R _43081 _43082) = (term721 A _43081 _43082 R _43083 _43084).
Proof. exact (TRANS (@lem3742220 A _43081 _43082 R _43083 _43084) (@lem3742247 A _43081 _43082 R _43083 _43084)). Qed.
Lemma lem3742250 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term722 A x R y x''.
Proof. exact (conj (@lem3742005 A x y s R x'' h1 h2) (@lem3742024 A x y s R x'' h1 h2)). Qed.
Lemma lem3742251 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term723 A x R y x''.
Proof. exact (conj (@lem3741794 A x'') (@lem3742250 A x y s R x'' h1 h2)). Qed.
Lemma lem3742253 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : term721 A _43081 _43082 R _43083 _43084.
Proof. exact (EQ_MP (@lem3742248 A _43081 _43082 R _43083 _43084) (@lem3742217 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742254 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : term721 A _43081 _43082 R _43083 _43084.
Proof. exact (@lem3742253 A _43081 _43082 R _43083 _43084). Qed.
Lemma lem3742255 {A : Type'} (y : A -> A) (R : type1402 A) (x'' : A) (x : A) : term724 A y R x'' x.
Proof. exact (@lem3742254 A x'' (y x'') R x'' x). Qed.
Lemma lem3742258 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x'' x.
Proof. exact (@lem3742255 A y R x'' x (@lem3742251 A x y s R x'' h1 h2)). Qed.
Lemma lem3742259 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term629 A R x'' x.
Proof. exact (fun h0 : term589 A R x'' x => @lem3742258 A x y s R x'' h1 h2). Qed.
Lemma lem3742261 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742262 {A : Type'} (R : type1402 A) (x'' : A) (x : A) : (term629 A R x'' x) = (R x'' x).
Proof. exact (@lem3742261 (R x'' x)). Qed.
Lemma lem3742263 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x'' x.
Proof. exact (EQ_MP (@lem3742262 A R x'' x) (@lem3742259 A x y s R x'' h1 h2)). Qed.
Lemma lem3742265 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3742266 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3742265 A x). Qed.
Lemma lem3742267 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3742266 A x). Qed.
Lemma lem3742269 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742270 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3742269 (x = x)). Qed.
Lemma lem3742271 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3742270 A x) (@lem3742267 A x)). Qed.
Lemma lem3742277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742278 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : (term621 A x R y _42921) = (term725 A R y _42921 x).
Proof. exact (@lem3742277 (term566 A R y _42921) (term606 A _42921 x)). Qed.
Lemma lem3742286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742287 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : (term726 A x R y _42921) = (term727 A R y _42921 x).
Proof. exact (MK_COMB (@lem3742286) (@lem3742278 A R y _42921 x)). Qed.
Lemma lem3742295 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : (term725 A R y _42921 x) = (term725 A R y _42921 x).
Proof. exact (eq_refl (term725 A R y _42921 x)). Qed.
Lemma lem3742296 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : ((term621 A x R y _42921) = (term725 A R y _42921 x)) = ((term725 A R y _42921 x) = (term725 A R y _42921 x)).
Proof. exact (MK_COMB (@lem3742287 A R y _42921 x) (@lem3742295 A R y _42921 x)). Qed.
Lemma lem3742298 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3742299 (x : Prop) : (x = x) = True.
Proof. exact (@lem3742298 Prop x). Qed.
Lemma lem3742300 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : ((term725 A R y _42921 x) = (term725 A R y _42921 x)) = True.
Proof. exact (@lem3742299 (term725 A R y _42921 x)). Qed.
Lemma lem3742301 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : ((term621 A x R y _42921) = (term725 A R y _42921 x)) = True.
Proof. exact (TRANS (@lem3742296 A R y _42921 x) (@lem3742300 A R y _42921 x)). Qed.
Lemma lem3742302 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : True = ((term621 A x R y _42921) = (term725 A R y _42921 x)).
Proof. exact (SYM (@lem3742301 A R y _42921 x)). Qed.
Lemma lem3742303 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) (x : A) : (term621 A x R y _42921) = (term725 A R y _42921 x).
Proof. exact (EQ_MP (@lem3742302 A R y _42921 x) (@lem0)). Qed.
Lemma lem3742304 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term725 A R y _42921 x.
Proof. exact (EQ_MP (@lem3742303 A R y _42921 x) (@lem3739483 A _42921 x s R y h1)). Qed.
Lemma lem3742306 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3742307 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42921 : A) : (term725 A R y _42921 x) = (term728 A x R y _42921).
Proof. exact (@lem3742306 (term606 A _42921 x) (term566 A R y _42921)). Qed.
Lemma lem3742309 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742310 {A : Type'} (_42921 : A) (x : A) : (term712 A _42921 x) = (_42921 = x).
Proof. exact (@lem3742309 (_42921 = x)). Qed.
Lemma lem3742311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3742312 {A : Type'} (_42921 : A) (x : A) : (term729 A _42921 x) = (term730 A _42921 x).
Proof. exact (MK_COMB (@lem3742311) (@lem3742310 A _42921 x)). Qed.
Lemma lem3742313 {A : Type'} (R : type1402 A) (y : A -> A) (_42921 : A) : (term566 A R y _42921) = (term566 A R y _42921).
Proof. exact (eq_refl (term566 A R y _42921)). Qed.
Lemma lem3742314 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42921 : A) : (term728 A x R y _42921) = (term731 A x R y _42921).
Proof. exact (MK_COMB (@lem3742312 A _42921 x) (@lem3742313 A R y _42921)). Qed.
Lemma lem3742315 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42921 : A) : (term725 A R y _42921 x) = (term731 A x R y _42921).
Proof. exact (TRANS (@lem3742307 A x R y _42921) (@lem3742314 A x R y _42921)). Qed.
Lemma lem3742318 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42921.
Proof. exact (EQ_MP (@lem3742315 A x R y _42921) (@lem3742304 A _42921 x s R y h1)). Qed.
Lemma lem3742319 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42921.
Proof. exact (@lem3742318 A _42921 x s R y h1). Qed.
Lemma lem3742320 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term732 A R y x.
Proof. exact (@lem3742319 A x x s R y h1). Qed.
Lemma lem3742323 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (@lem3742320 A x s R y h1 (@lem3742271 A x)). Qed.
Lemma lem3742324 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term668 A R y x.
Proof. exact (fun h0 : term669 A R y x => @lem3742323 A x s R y h1). Qed.
Lemma lem3742326 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742327 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : (term668 A R y x) = (term566 A R y x).
Proof. exact (@lem3742326 (term566 A R y x)). Qed.
Lemma lem3742328 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (EQ_MP (@lem3742327 A R y x) (@lem3742324 A x s R y h1)). Qed.
Lemma lem3742344 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742345 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term630 A _42919 R _42918 _42920) = (term631 A _42918 R _42919 _42920).
Proof. exact (@lem3742344 (R _42918 _42920) (term589 A R _42919 _42920)). Qed.
Lemma lem3742351 {A : Type'} (R : type1402 A) (_42918 : A) (_42919 : A) : (term632 A R _42918 _42919) = (term632 A R _42918 _42919).
Proof. exact (eq_refl (term632 A R _42918 _42919)). Qed.
Lemma lem3742352 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term620 A _42919 R _42918 _42920) = (term633 A _42918 R _42919 _42920).
Proof. exact (MK_COMB (@lem3742351 A R _42918 _42919) (@lem3742345 A _42918 R _42919 _42920)). Qed.
Lemma lem3742356 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742357 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term633 A _42918 R _42919 _42920) = (term634 A _42918 R _42919 _42920).
Proof. exact (@lem3742356 (R _42918 _42920) (term589 A R _42918 _42919) (term589 A R _42919 _42920)). Qed.
Lemma lem3742373 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term620 A _42919 R _42918 _42920) = (term634 A _42918 R _42919 _42920).
Proof. exact (TRANS (@lem3742352 A _42918 R _42919 _42920) (@lem3742357 A _42918 R _42919 _42920)). Qed.
Lemma lem3742374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742375 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term635 A _42919 R _42918 _42920) = (term636 A _42918 R _42919 _42920).
Proof. exact (MK_COMB (@lem3742374) (@lem3742373 A _42918 R _42919 _42920)). Qed.
Lemma lem3742391 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term634 A _42918 R _42919 _42920) = (term634 A _42918 R _42919 _42920).
Proof. exact (eq_refl (term634 A _42918 R _42919 _42920)). Qed.
Lemma lem3742392 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : ((term620 A _42919 R _42918 _42920) = (term634 A _42918 R _42919 _42920)) = ((term634 A _42918 R _42919 _42920) = (term634 A _42918 R _42919 _42920)).
Proof. exact (MK_COMB (@lem3742375 A _42918 R _42919 _42920) (@lem3742391 A _42918 R _42919 _42920)). Qed.
Lemma lem3742394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3742395 (x : Prop) : (x = x) = True.
Proof. exact (@lem3742394 Prop x). Qed.
Lemma lem3742396 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : ((term634 A _42918 R _42919 _42920) = (term634 A _42918 R _42919 _42920)) = True.
Proof. exact (@lem3742395 (term634 A _42918 R _42919 _42920)). Qed.
Lemma lem3742397 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : ((term620 A _42919 R _42918 _42920) = (term634 A _42918 R _42919 _42920)) = True.
Proof. exact (TRANS (@lem3742392 A _42918 R _42919 _42920) (@lem3742396 A _42918 R _42919 _42920)). Qed.
Lemma lem3742398 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : True = ((term620 A _42919 R _42918 _42920) = (term634 A _42918 R _42919 _42920)).
Proof. exact (SYM (@lem3742397 A _42918 R _42919 _42920)). Qed.
Lemma lem3742399 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term620 A _42919 R _42918 _42920) = (term634 A _42918 R _42919 _42920).
Proof. exact (EQ_MP (@lem3742398 A _42918 R _42919 _42920) (@lem0)). Qed.
Lemma lem3742400 {A : Type'} (_42918 : A) (_42919 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term634 A _42918 R _42919 _42920.
Proof. exact (EQ_MP (@lem3742399 A _42918 R _42919 _42920) (@lem3739467 A _42919 _42918 _42920 x s R y h1)). Qed.
Lemma lem3742402 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3742403 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) (_42920 : A) : (term634 A _42918 R _42919 _42920) = (term638 A _42919 R _42918 _42920).
Proof. exact (@lem3742402 (term475 A _42918 R _42919 _42920) (R _42918 _42920)). Qed.
Lemma lem3742405 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3742406 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term641 A _42918 R _42919 _42920) = (term642 A _42918 R _42919 _42920).
Proof. exact (@lem3742405 (term589 A R _42918 _42919) (term589 A R _42919 _42920)). Qed.
Lemma lem3742408 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742409 {A : Type'} (R : type1402 A) (_42918 : A) (_42919 : A) : (term643 A R _42918 _42919) = (R _42918 _42919).
Proof. exact (@lem3742408 (R _42918 _42919)). Qed.
Lemma lem3742410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3742411 {A : Type'} (R : type1402 A) (_42918 : A) (_42919 : A) : (term644 A R _42918 _42919) = (term645 A R _42918 _42919).
Proof. exact (MK_COMB (@lem3742410) (@lem3742409 A R _42918 _42919)). Qed.
Lemma lem3742413 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742414 {A : Type'} (R : type1402 A) (_42919 : A) (_42920 : A) : (term643 A R _42919 _42920) = (R _42919 _42920).
Proof. exact (@lem3742413 (R _42919 _42920)). Qed.
Lemma lem3742415 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term642 A _42918 R _42919 _42920) = (term207 A _42918 R _42919 _42920).
Proof. exact (MK_COMB (@lem3742411 A R _42918 _42919) (@lem3742414 A R _42919 _42920)). Qed.
Lemma lem3742416 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term641 A _42918 R _42919 _42920) = (term207 A _42918 R _42919 _42920).
Proof. exact (TRANS (@lem3742406 A _42918 R _42919 _42920) (@lem3742415 A _42918 R _42919 _42920)). Qed.
Lemma lem3742417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3742418 {A : Type'} (_42918 : A) (R : type1402 A) (_42919 : A) (_42920 : A) : (term646 A _42918 R _42919 _42920) = (term647 A _42918 R _42919 _42920).
Proof. exact (MK_COMB (@lem3742417) (@lem3742416 A _42918 R _42919 _42920)). Qed.
Lemma lem3742419 {A : Type'} (R : type1402 A) (_42918 : A) (_42920 : A) : (R _42918 _42920) = (R _42918 _42920).
Proof. exact (eq_refl (R _42918 _42920)). Qed.
Lemma lem3742420 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) (_42920 : A) : (term638 A _42919 R _42918 _42920) = (term186 A _42919 R _42918 _42920).
Proof. exact (MK_COMB (@lem3742418 A _42918 R _42919 _42920) (@lem3742419 A R _42918 _42920)). Qed.
Lemma lem3742421 {A : Type'} (_42919 : A) (R : type1402 A) (_42918 : A) (_42920 : A) : (term634 A _42918 R _42919 _42920) = (term186 A _42919 R _42918 _42920).
Proof. exact (TRANS (@lem3742403 A _42919 R _42918 _42920) (@lem3742420 A _42919 R _42918 _42920)). Qed.
Lemma lem3742423 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term733 A x'' R y x.
Proof. exact (conj (@lem3742263 A x y s R x'' h1 h2) (@lem3742328 A x s R y h1)). Qed.
Lemma lem3742425 {A : Type'} (_42919 : A) (_42918 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42919 R _42918 _42920.
Proof. exact (EQ_MP (@lem3742421 A _42919 R _42918 _42920) (@lem3742400 A _42918 _42919 _42920 x s R y h1)). Qed.
Lemma lem3742426 {A : Type'} (_42919 : A) (_42918 : A) (_42920 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term186 A _42919 R _42918 _42920.
Proof. exact (@lem3742425 A _42919 _42918 _42920 x s R y h1). Qed.
Lemma lem3742427 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term734 A R x'' y x.
Proof. exact (@lem3742426 A x x'' (y x) x s R y h1). Qed.
Lemma lem3742430 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term735 A R x'' y x.
Proof. exact (@lem3742427 A x'' x s R y h1 (@lem3742423 A x y s R x'' h1 h2)). Qed.
Lemma lem3742431 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term736 A R x'' y x.
Proof. exact (fun h0 : term737 A R x'' y x => @lem3742430 A x y s R x'' h1 h2). Qed.
Lemma lem3742433 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742434 {A : Type'} (R : type1402 A) (x'' : A) (y : A -> A) (x : A) : (term736 A R x'' y x) = (term735 A R x'' y x).
Proof. exact (@lem3742433 (term735 A R x'' y x)). Qed.
Lemma lem3742435 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term735 A R x'' y x.
Proof. exact (EQ_MP (@lem3742434 A R x'' y x) (@lem3742431 A x y s R x'' h1 h2)). Qed.
Lemma lem3742437 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42922.
Proof. exact (EQ_MP (@lem3741872 A R x'' s _42922) (@lem3739475 A _42922 s R x'' h1)). Qed.
Lemma lem3742438 {A : Type'} (_42922 : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term673 A R x'' s _42922.
Proof. exact (@lem3742437 A _42922 s R x'' h1). Qed.
Lemma lem3742439 {A : Type'} (y : A -> A) (x : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term596 A s R x'') : term738 A R x'' s y x.
Proof. exact (@lem3742438 A (y x) s R x'' h1). Qed.
Lemma lem3742442 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x.
Proof. exact (@lem3742439 A y x s R x'' h2 (@lem3742435 A x y s R x'' h1 h2)). Qed.
Lemma lem3742443 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term676 A s y x.
Proof. exact (fun h0 : term568 A s y x => @lem3742442 A x y s R x'' h1 h2). Qed.
Lemma lem3742445 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3742446 {A : Type'} (s : A -> Prop) (y : A -> A) (x : A) : (term676 A s y x) = (term675 A s y x).
Proof. exact (@lem3742445 (term568 A s y x)). Qed.
Lemma lem3742447 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term675 A s y x.
Proof. exact (EQ_MP (@lem3742446 A s y x) (@lem3742443 A x y s R x'' h1 h2)). Qed.
Lemma lem3742453 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742454 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term623 A x s y _42921) = (term739 A x s y _42921).
Proof. exact (@lem3742453 ((y _42921) = x) (term606 A _42921 x) (term568 A s y _42921)). Qed.
Lemma lem3742470 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742471 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term740 A x s y _42921) = (term741 A s y _42921 x).
Proof. exact (@lem3742470 (term568 A s y _42921) (term606 A _42921 x)). Qed.
Lemma lem3742479 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : (term569 A y _42921 x) = (term569 A y _42921 x).
Proof. exact (eq_refl (term569 A y _42921 x)). Qed.
Lemma lem3742480 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term739 A x s y _42921) = (term742 A s y _42921 x).
Proof. exact (MK_COMB (@lem3742479 A y _42921 x) (@lem3742471 A s y _42921 x)). Qed.
Lemma lem3742491 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term623 A x s y _42921) = (term742 A s y _42921 x).
Proof. exact (TRANS (@lem3742454 A x s y _42921) (@lem3742480 A s y _42921 x)). Qed.
Lemma lem3742492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742493 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term743 A x s y _42921) = (term744 A s y _42921 x).
Proof. exact (MK_COMB (@lem3742492) (@lem3742491 A s y _42921 x)). Qed.
Lemma lem3742509 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742510 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term740 A x s y _42921) = (term741 A s y _42921 x).
Proof. exact (@lem3742509 (term568 A s y _42921) (term606 A _42921 x)). Qed.
Lemma lem3742518 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : (term569 A y _42921 x) = (term569 A y _42921 x).
Proof. exact (eq_refl (term569 A y _42921 x)). Qed.
Lemma lem3742519 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term739 A x s y _42921) = (term742 A s y _42921 x).
Proof. exact (MK_COMB (@lem3742518 A y _42921 x) (@lem3742510 A s y _42921 x)). Qed.
Lemma lem3742530 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : ((term623 A x s y _42921) = (term739 A x s y _42921)) = ((term742 A s y _42921 x) = (term742 A s y _42921 x)).
Proof. exact (MK_COMB (@lem3742493 A s y _42921 x) (@lem3742519 A s y _42921 x)). Qed.
Lemma lem3742532 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3742533 (x : Prop) : (x = x) = True.
Proof. exact (@lem3742532 Prop x). Qed.
Lemma lem3742534 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : ((term742 A s y _42921 x) = (term742 A s y _42921 x)) = True.
Proof. exact (@lem3742533 (term742 A s y _42921 x)). Qed.
Lemma lem3742535 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : ((term623 A x s y _42921) = (term739 A x s y _42921)) = True.
Proof. exact (TRANS (@lem3742530 A s y _42921 x) (@lem3742534 A s y _42921 x)). Qed.
Lemma lem3742536 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : True = ((term623 A x s y _42921) = (term739 A x s y _42921)).
Proof. exact (SYM (@lem3742535 A x s y _42921)). Qed.
Lemma lem3742537 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term623 A x s y _42921) = (term739 A x s y _42921).
Proof. exact (EQ_MP (@lem3742536 A x s y _42921) (@lem0)). Qed.
Lemma lem3742538 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term739 A x s y _42921.
Proof. exact (EQ_MP (@lem3742537 A x s y _42921) (@lem3739499 A _42921 x s R y h1)). Qed.
Lemma lem3742540 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3742541 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term739 A x s y _42921) = (term745 A s y _42921 x).
Proof. exact (@lem3742540 (term740 A x s y _42921) ((y _42921) = x)). Qed.
Lemma lem3742543 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3742544 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term746 A x s y _42921) = (term747 A x s y _42921).
Proof. exact (@lem3742543 (term606 A _42921 x) (term568 A s y _42921)). Qed.
Lemma lem3742546 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742547 {A : Type'} (_42921 : A) (x : A) : (term712 A _42921 x) = (_42921 = x).
Proof. exact (@lem3742546 (_42921 = x)). Qed.
Lemma lem3742548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3742549 {A : Type'} (_42921 : A) (x : A) : (term713 A _42921 x) = (term714 A _42921 x).
Proof. exact (MK_COMB (@lem3742548) (@lem3742547 A _42921 x)). Qed.
Lemma lem3742550 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) : (term675 A s y _42921) = (term675 A s y _42921).
Proof. exact (eq_refl (term675 A s y _42921)). Qed.
Lemma lem3742551 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term747 A x s y _42921) = (term748 A x s y _42921).
Proof. exact (MK_COMB (@lem3742549 A _42921 x) (@lem3742550 A s y _42921)). Qed.
Lemma lem3742552 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term746 A x s y _42921) = (term748 A x s y _42921).
Proof. exact (TRANS (@lem3742544 A x s y _42921) (@lem3742551 A x s y _42921)). Qed.
Lemma lem3742553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3742554 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42921 : A) : (term749 A x s y _42921) = (term750 A x s y _42921).
Proof. exact (MK_COMB (@lem3742553) (@lem3742552 A x s y _42921)). Qed.
Lemma lem3742555 {A : Type'} (y : A -> A) (_42921 : A) (x : A) : ((y _42921) = x) = ((y _42921) = x).
Proof. exact (eq_refl ((y _42921) = x)). Qed.
Lemma lem3742556 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term745 A s y _42921 x) = (term751 A s y _42921 x).
Proof. exact (MK_COMB (@lem3742554 A x s y _42921) (@lem3742555 A y _42921 x)). Qed.
Lemma lem3742557 {A : Type'} (s : A -> Prop) (y : A -> A) (_42921 : A) (x : A) : (term739 A x s y _42921) = (term751 A s y _42921 x).
Proof. exact (TRANS (@lem3742541 A s y _42921 x) (@lem3742556 A s y _42921 x)). Qed.
Lemma lem3742559 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term752 A s y x.
Proof. exact (conj (@lem3741785 A x) (@lem3742447 A x y s R x'' h1 h2)). Qed.
Lemma lem3742561 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term751 A s y _42921 x.
Proof. exact (EQ_MP (@lem3742557 A s y _42921 x) (@lem3742538 A _42921 x s R y h1)). Qed.
Lemma lem3742562 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term751 A s y _42921 x.
Proof. exact (@lem3742561 A _42921 x s R y h1). Qed.
Lemma lem3742563 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term753 A s y x.
Proof. exact (@lem3742562 A x x s R y h1). Qed.
Lemma lem3742566 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x) = x.
Proof. exact (@lem3742563 A x s R y h1 (@lem3742559 A x y s R x'' h1 h2)). Qed.
Lemma lem3742567 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term754 A y x.
Proof. exact (fun h0 : term755 A y x => @lem3742566 A x y s R x'' h1 h2). Qed.
Lemma lem3742569 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742570 {A : Type'} (y : A -> A) (x : A) : (term754 A y x) = ((y x) = x).
Proof. exact (@lem3742569 ((y x) = x)). Qed.
Lemma lem3742571 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : (y x) = x.
Proof. exact (EQ_MP (@lem3742570 A y x) (@lem3742567 A x y s R x'' h1 h2)). Qed.
Lemma lem3742573 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3742574 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3742573 A x). Qed.
Lemma lem3742575 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3742574 A x). Qed.
Lemma lem3742577 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742578 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3742577 (x = x)). Qed.
Lemma lem3742579 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3742578 A x) (@lem3742575 A x)). Qed.
Lemma lem3742581 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42921.
Proof. exact (EQ_MP (@lem3742315 A x R y _42921) (@lem3742304 A _42921 x s R y h1)). Qed.
Lemma lem3742582 {A : Type'} (_42921 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42921.
Proof. exact (@lem3742581 A _42921 x s R y h1). Qed.
Lemma lem3742583 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term732 A R y x.
Proof. exact (@lem3742582 A x x s R y h1). Qed.
Lemma lem3742586 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (@lem3742583 A x s R y h1 (@lem3742579 A x)). Qed.
Lemma lem3742587 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term668 A R y x.
Proof. exact (fun h0 : term669 A R y x => @lem3742586 A x s R y h1). Qed.
Lemma lem3742589 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742590 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : (term668 A R y x) = (term566 A R y x).
Proof. exact (@lem3742589 (term566 A R y x)). Qed.
Lemma lem3742591 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (EQ_MP (@lem3742590 A R y x) (@lem3742587 A x s R y h1)). Qed.
Lemma lem3742592 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term756 A R y x.
Proof. exact (conj (@lem3742571 A x y s R x'' h1 h2) (@lem3742591 A x s R y h1)). Qed.
Lemma lem3742593 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term757 A R y x.
Proof. exact (conj (@lem3741777 A x) (@lem3742592 A x y s R x'' h1 h2)). Qed.
Lemma lem3742595 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : term721 A _43081 _43082 R _43083 _43084.
Proof. exact (EQ_MP (@lem3742248 A _43081 _43082 R _43083 _43084) (@lem3742217 A _43083 _43084 R _43081 _43082)). Qed.
Lemma lem3742596 {A : Type'} (_43081 : A) (_43082 : A) (R : type1402 A) (_43083 : A) (_43084 : A) : term721 A _43081 _43082 R _43083 _43084.
Proof. exact (@lem3742595 A _43081 _43082 R _43083 _43084). Qed.
Lemma lem3742597 {A : Type'} (y : A -> A) (R : type1402 A) (x : A) : term758 A y R x.
Proof. exact (@lem3742596 A x (y x) R x x). Qed.
Lemma lem3742600 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x x.
Proof. exact (@lem3742597 A y R x (@lem3742593 A x y s R x'' h1 h2)). Qed.
Lemma lem3742601 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term625 A R x.
Proof. exact (fun h0 : term192 A R x => @lem3742600 A x y s R x'' h1 h2). Qed.
Lemma lem3742603 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742604 {A : Type'} (R : type1402 A) (x : A) : (term625 A R x) = (R x x).
Proof. exact (@lem3742603 (R x x)). Qed.
Lemma lem3742605 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : R x x.
Proof. exact (EQ_MP (@lem3742604 A R x) (@lem3742601 A x y s R x'' h1 h2)). Qed.
Lemma lem3742608 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3742610 {A : Type'} (R : type1402 A) (_42917 : A) : (term192 A R _42917) = (term627 A R _42917).
Proof. exact (@lem3742608 (R _42917 _42917)). Qed.
Lemma lem3742613 {A : Type'} (_42917 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42917.
Proof. exact (EQ_MP (@lem3742610 A R _42917) (@lem3739455 A _42917 x s R y h1)). Qed.
Lemma lem3742614 {A : Type'} (_42917 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R _42917.
Proof. exact (@lem3742613 A _42917 x s R y h1). Qed.
Lemma lem3742615 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term627 A R x.
Proof. exact (@lem3742614 A x x s R y h1). Qed.
Lemma lem3742618 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : False.
Proof. exact (@lem3742615 A x s R y h1 (@lem3742605 A x y s R x'' h1 h2)). Qed.
Lemma lem3742619 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : term628.
Proof. exact (fun h0 : ~ False => @lem3742618 A x y s R x'' h1 h2). Qed.
Lemma lem3742621 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742622 : term628 = False.
Proof. exact (@lem3742621 False). Qed.
Lemma lem3742623 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : False.
Proof. exact (EQ_MP (@lem3742622) (@lem3742619 A x y s R x'' h1 h2)). Qed.
Lemma lem3742624 {A : Type'} (R : type1402 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem3742625 {A : Type'} (_43093 : A) (_43095 : A) (h1 : _43093 = _43095) : _43093 = _43095.
Proof. exact (h1). Qed.
Lemma lem3742626 {A : Type'} (_43094 : A) (_43096 : A) (h1 : _43094 = _43096) : _43094 = _43096.
Proof. exact (h1). Qed.
Lemma lem3742627 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (h1 : _43093 = _43095) : (R _43093) = (R _43095).
Proof. exact (MK_COMB (@lem3742624 A R) (@lem3742625 A _43093 _43095 h1)). Qed.
Lemma lem3742628 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) (h1 : _43093 = _43095) (h2 : _43094 = _43096) : (R _43093 _43094) = (R _43095 _43096).
Proof. exact (MK_COMB (@lem3742627 A R _43093 _43095 h1) (@lem3742626 A _43094 _43096 h2)). Qed.
Lemma lem3742630 (b : Prop) (a : Prop) : term649 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3742631 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : term650 A _43095 _43096 R _43093 _43094.
Proof. exact (@lem3742630 (R _43095 _43096) (R _43093 _43094)). Qed.
Lemma lem3742632 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) (h1 : _43093 = _43095) (h2 : _43094 = _43096) : term651 A _43095 _43096 R _43093 _43094.
Proof. exact (@lem3742631 A _43095 _43096 R _43093 _43094 (@lem3742628 A R _43093 _43095 _43094 _43096 h1 h2)). Qed.
Lemma lem3742633 {A : Type'} (_43096 : A) (R : type1402 A) (_43094 : A) (_43093 : A) (_43095 : A) (h1 : _43093 = _43095) : term652 A _43095 _43096 R _43093 _43094.
Proof. exact (fun h0 : _43094 = _43096 => @lem3742632 A R _43093 _43095 _43094 _43096 h1 h0). Qed.
Lemma lem3742635 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3742636 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term652 A _43095 _43096 R _43093 _43094) = (term654 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3742635 (_43094 = _43096) (term651 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3742637 {A : Type'} (_43096 : A) (R : type1402 A) (_43094 : A) (_43093 : A) (_43095 : A) (h1 : _43093 = _43095) : term654 A _43095 _43096 R _43093 _43094.
Proof. exact (EQ_MP (@lem3742636 A _43095 _43096 R _43093 _43094) (@lem3742633 A _43096 R _43094 _43093 _43095 h1)). Qed.
Lemma lem3742638 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : term655 A _43095 _43096 R _43093 _43094.
Proof. exact (fun h0 : _43093 = _43095 => @lem3742637 A _43096 R _43094 _43093 _43095 h0). Qed.
Lemma lem3742640 (a : Prop) (b : Prop) : (a -> b) = (term653 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3742641 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term655 A _43095 _43096 R _43093 _43094) = (term656 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3742640 (_43093 = _43095) (term654 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3742642 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : term656 A _43095 _43096 R _43093 _43094.
Proof. exact (EQ_MP (@lem3742641 A _43095 _43096 R _43093 _43094) (@lem3742638 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3742687 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3742688 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3742687 A x). Qed.
Lemma lem3742689 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3742688 A x). Qed.
Lemma lem3742691 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742692 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3742691 (x = x)). Qed.
Lemma lem3742693 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3742692 A x) (@lem3742689 A x)). Qed.
Lemma lem3742695 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3742696 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3742695 A x). Qed.
Lemma lem3742697 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3742696 A x). Qed.
Lemma lem3742699 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742700 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3742699 (x = x)). Qed.
Lemma lem3742701 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3742700 A x) (@lem3742697 A x)). Qed.
Lemma lem3742703 {A : Type'} (_42923 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42923.
Proof. exact (EQ_MP (@lem3739083 A R _42923) (@lem3739082 A _42923 x s R y h1)). Qed.
Lemma lem3742704 {A : Type'} (_42923 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R _42923.
Proof. exact (@lem3742703 A _42923 x s R y h1). Qed.
Lemma lem3742705 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R x.
Proof. exact (@lem3742704 A x x s R y h1). Qed.
Lemma lem3742706 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term759 A R x.
Proof. exact (fun h0 : R x x => @lem3742705 A x s R y h1). Qed.
Lemma lem3742708 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3742709 {A : Type'} (R : type1402 A) (x : A) : (term759 A R x) = (term192 A R x).
Proof. exact (@lem3742708 (R x x)). Qed.
Lemma lem3742710 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term192 A R x.
Proof. exact (EQ_MP (@lem3742709 A R x) (@lem3742706 A x s R y h1)). Qed.
Lemma lem3742712 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3742713 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3742712 A x). Qed.
Lemma lem3742714 {A : Type'} (x : A) : term657 A x.
Proof. exact (fun h0 : term658 A x => @lem3742713 A x). Qed.
Lemma lem3742716 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742717 {A : Type'} (x : A) : (term657 A x) = (x = x).
Proof. exact (@lem3742716 (x = x)). Qed.
Lemma lem3742718 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3742717 A x) (@lem3742714 A x)). Qed.
Lemma lem3742724 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742725 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : (term621 A x R y _42927) = (term725 A R y _42927 x).
Proof. exact (@lem3742724 (term566 A R y _42927) (term606 A _42927 x)). Qed.
Lemma lem3742733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742734 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : (term726 A x R y _42927) = (term727 A R y _42927 x).
Proof. exact (MK_COMB (@lem3742733) (@lem3742725 A R y _42927 x)). Qed.
Lemma lem3742742 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : (term725 A R y _42927 x) = (term725 A R y _42927 x).
Proof. exact (eq_refl (term725 A R y _42927 x)). Qed.
Lemma lem3742743 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : ((term621 A x R y _42927) = (term725 A R y _42927 x)) = ((term725 A R y _42927 x) = (term725 A R y _42927 x)).
Proof. exact (MK_COMB (@lem3742734 A R y _42927 x) (@lem3742742 A R y _42927 x)). Qed.
Lemma lem3742745 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3742746 (x : Prop) : (x = x) = True.
Proof. exact (@lem3742745 Prop x). Qed.
Lemma lem3742747 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : ((term725 A R y _42927 x) = (term725 A R y _42927 x)) = True.
Proof. exact (@lem3742746 (term725 A R y _42927 x)). Qed.
Lemma lem3742748 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : ((term621 A x R y _42927) = (term725 A R y _42927 x)) = True.
Proof. exact (TRANS (@lem3742743 A R y _42927 x) (@lem3742747 A R y _42927 x)). Qed.
Lemma lem3742749 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : True = ((term621 A x R y _42927) = (term725 A R y _42927 x)).
Proof. exact (SYM (@lem3742748 A R y _42927 x)). Qed.
Lemma lem3742750 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) (x : A) : (term621 A x R y _42927) = (term725 A R y _42927 x).
Proof. exact (EQ_MP (@lem3742749 A R y _42927 x) (@lem0)). Qed.
Lemma lem3742751 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term725 A R y _42927 x.
Proof. exact (EQ_MP (@lem3742750 A R y _42927 x) (@lem3740177 A _42927 x s R y h1)). Qed.
Lemma lem3742753 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3742754 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42927 : A) : (term725 A R y _42927 x) = (term728 A x R y _42927).
Proof. exact (@lem3742753 (term606 A _42927 x) (term566 A R y _42927)). Qed.
Lemma lem3742756 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3742757 {A : Type'} (_42927 : A) (x : A) : (term712 A _42927 x) = (_42927 = x).
Proof. exact (@lem3742756 (_42927 = x)). Qed.
Lemma lem3742758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3742759 {A : Type'} (_42927 : A) (x : A) : (term729 A _42927 x) = (term730 A _42927 x).
Proof. exact (MK_COMB (@lem3742758) (@lem3742757 A _42927 x)). Qed.
Lemma lem3742760 {A : Type'} (R : type1402 A) (y : A -> A) (_42927 : A) : (term566 A R y _42927) = (term566 A R y _42927).
Proof. exact (eq_refl (term566 A R y _42927)). Qed.
Lemma lem3742761 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42927 : A) : (term728 A x R y _42927) = (term731 A x R y _42927).
Proof. exact (MK_COMB (@lem3742759 A _42927 x) (@lem3742760 A R y _42927)). Qed.
Lemma lem3742762 {A : Type'} (x : A) (R : type1402 A) (y : A -> A) (_42927 : A) : (term725 A R y _42927 x) = (term731 A x R y _42927).
Proof. exact (TRANS (@lem3742754 A x R y _42927) (@lem3742761 A x R y _42927)). Qed.
Lemma lem3742765 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42927.
Proof. exact (EQ_MP (@lem3742762 A x R y _42927) (@lem3742751 A _42927 x s R y h1)). Qed.
Lemma lem3742766 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term731 A x R y _42927.
Proof. exact (@lem3742765 A _42927 x s R y h1). Qed.
Lemma lem3742767 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term732 A R y x.
Proof. exact (@lem3742766 A x x s R y h1). Qed.
Lemma lem3742770 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (@lem3742767 A x s R y h1 (@lem3742718 A x)). Qed.
Lemma lem3742771 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term668 A R y x.
Proof. exact (fun h0 : term669 A R y x => @lem3742770 A x s R y h1). Qed.
Lemma lem3742773 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3742774 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : (term668 A R y x) = (term566 A R y x).
Proof. exact (@lem3742773 (term566 A R y x)). Qed.
Lemma lem3742775 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term566 A R y x.
Proof. exact (EQ_MP (@lem3742774 A R y x) (@lem3742771 A x s R y h1)). Qed.
Lemma lem3742793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742794 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term654 A _43095 _43096 R _43093 _43094) = (term694 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3742793 (R _43095 _43096) (term606 A _43094 _43096) (term589 A R _43093 _43094)). Qed.
Lemma lem3742808 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742809 {A : Type'} (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term695 A _43096 R _43093 _43094) = (term696 A R _43093 _43094 _43096).
Proof. exact (@lem3742808 (term589 A R _43093 _43094) (term606 A _43094 _43096)). Qed.
Lemma lem3742817 {A : Type'} (R : type1402 A) (_43095 : A) (_43096 : A) : (term697 A R _43095 _43096) = (term697 A R _43095 _43096).
Proof. exact (eq_refl (term697 A R _43095 _43096)). Qed.
Lemma lem3742818 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term694 A _43095 _43096 R _43093 _43094) = (term698 A _43095 R _43093 _43094 _43096).
Proof. exact (MK_COMB (@lem3742817 A R _43095 _43096) (@lem3742809 A R _43093 _43094 _43096)). Qed.
Lemma lem3742829 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term654 A _43095 _43096 R _43093 _43094) = (term698 A _43095 R _43093 _43094 _43096).
Proof. exact (TRANS (@lem3742794 A _43095 _43096 R _43093 _43094) (@lem3742818 A _43095 R _43093 _43094 _43096)). Qed.
Lemma lem3742830 {A : Type'} (_43093 : A) (_43095 : A) : (term699 A _43093 _43095) = (term699 A _43093 _43095).
Proof. exact (eq_refl (term699 A _43093 _43095)). Qed.
Lemma lem3742831 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term656 A _43095 _43096 R _43093 _43094) = (term700 A _43095 R _43093 _43094 _43096).
Proof. exact (MK_COMB (@lem3742830 A _43093 _43095) (@lem3742829 A _43095 R _43093 _43094 _43096)). Qed.
Lemma lem3742835 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742836 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term700 A _43095 R _43093 _43094 _43096) = (term701 A _43095 R _43093 _43094 _43096).
Proof. exact (@lem3742835 (R _43095 _43096) (term606 A _43093 _43095) (term696 A R _43093 _43094 _43096)). Qed.
Lemma lem3742850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742851 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term702 A _43095 R _43093 _43094 _43096) = (term703 A R _43093 _43095 _43094 _43096).
Proof. exact (@lem3742850 (term589 A R _43093 _43094) (term606 A _43093 _43095) (term606 A _43094 _43096)). Qed.
Lemma lem3742871 {A : Type'} (R : type1402 A) (_43095 : A) (_43096 : A) : (term697 A R _43095 _43096) = (term697 A R _43095 _43096).
Proof. exact (eq_refl (term697 A R _43095 _43096)). Qed.
Lemma lem3742872 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term701 A _43095 R _43093 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (MK_COMB (@lem3742871 A R _43095 _43096) (@lem3742851 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742883 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term700 A _43095 R _43093 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (TRANS (@lem3742836 A _43095 R _43093 _43094 _43096) (@lem3742872 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742884 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term656 A _43095 _43096 R _43093 _43094) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (TRANS (@lem3742831 A _43095 R _43093 _43094 _43096) (@lem3742883 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3742886 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term705 A _43095 _43096 R _43093 _43094) = (term706 A R _43093 _43095 _43094 _43096).
Proof. exact (MK_COMB (@lem3742885) (@lem3742884 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742890 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742891 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term760 A _43095 _43096 R _43093 _43094) = (term656 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3742890 (term606 A _43093 _43095) (term606 A _43094 _43096) (term651 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3742907 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742908 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term654 A _43095 _43096 R _43093 _43094) = (term694 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3742907 (R _43095 _43096) (term606 A _43094 _43096) (term589 A R _43093 _43094)). Qed.
Lemma lem3742922 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3742923 {A : Type'} (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term695 A _43096 R _43093 _43094) = (term696 A R _43093 _43094 _43096).
Proof. exact (@lem3742922 (term589 A R _43093 _43094) (term606 A _43094 _43096)). Qed.
Lemma lem3742931 {A : Type'} (R : type1402 A) (_43095 : A) (_43096 : A) : (term697 A R _43095 _43096) = (term697 A R _43095 _43096).
Proof. exact (eq_refl (term697 A R _43095 _43096)). Qed.
Lemma lem3742932 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term694 A _43095 _43096 R _43093 _43094) = (term698 A _43095 R _43093 _43094 _43096).
Proof. exact (MK_COMB (@lem3742931 A R _43095 _43096) (@lem3742923 A R _43093 _43094 _43096)). Qed.
Lemma lem3742943 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term654 A _43095 _43096 R _43093 _43094) = (term698 A _43095 R _43093 _43094 _43096).
Proof. exact (TRANS (@lem3742908 A _43095 _43096 R _43093 _43094) (@lem3742932 A _43095 R _43093 _43094 _43096)). Qed.
Lemma lem3742944 {A : Type'} (_43093 : A) (_43095 : A) : (term699 A _43093 _43095) = (term699 A _43093 _43095).
Proof. exact (eq_refl (term699 A _43093 _43095)). Qed.
Lemma lem3742945 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term656 A _43095 _43096 R _43093 _43094) = (term700 A _43095 R _43093 _43094 _43096).
Proof. exact (MK_COMB (@lem3742944 A _43093 _43095) (@lem3742943 A _43095 R _43093 _43094 _43096)). Qed.
Lemma lem3742949 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742950 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term700 A _43095 R _43093 _43094 _43096) = (term701 A _43095 R _43093 _43094 _43096).
Proof. exact (@lem3742949 (R _43095 _43096) (term606 A _43093 _43095) (term696 A R _43093 _43094 _43096)). Qed.
Lemma lem3742964 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3742965 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term702 A _43095 R _43093 _43094 _43096) = (term703 A R _43093 _43095 _43094 _43096).
Proof. exact (@lem3742964 (term589 A R _43093 _43094) (term606 A _43093 _43095) (term606 A _43094 _43096)). Qed.
Lemma lem3742985 {A : Type'} (R : type1402 A) (_43095 : A) (_43096 : A) : (term697 A R _43095 _43096) = (term697 A R _43095 _43096).
Proof. exact (eq_refl (term697 A R _43095 _43096)). Qed.
Lemma lem3742986 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term701 A _43095 R _43093 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (MK_COMB (@lem3742985 A R _43095 _43096) (@lem3742965 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742997 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term700 A _43095 R _43093 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (TRANS (@lem3742950 A _43095 R _43093 _43094 _43096) (@lem3742986 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742998 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term656 A _43095 _43096 R _43093 _43094) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (TRANS (@lem3742945 A _43095 R _43093 _43094 _43096) (@lem3742997 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3742999 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : (term760 A _43095 _43096 R _43093 _43094) = (term704 A R _43093 _43095 _43094 _43096).
Proof. exact (TRANS (@lem3742891 A _43095 _43096 R _43093 _43094) (@lem3742998 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3743000 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : ((term656 A _43095 _43096 R _43093 _43094) = (term760 A _43095 _43096 R _43093 _43094)) = ((term704 A R _43093 _43095 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096)).
Proof. exact (MK_COMB (@lem3742886 A R _43093 _43095 _43094 _43096) (@lem3742999 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3743002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3743003 (x : Prop) : (x = x) = True.
Proof. exact (@lem3743002 Prop x). Qed.
Lemma lem3743004 {A : Type'} (R : type1402 A) (_43093 : A) (_43095 : A) (_43094 : A) (_43096 : A) : ((term704 A R _43093 _43095 _43094 _43096) = (term704 A R _43093 _43095 _43094 _43096)) = True.
Proof. exact (@lem3743003 (term704 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3743005 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : ((term656 A _43095 _43096 R _43093 _43094) = (term760 A _43095 _43096 R _43093 _43094)) = True.
Proof. exact (TRANS (@lem3743000 A R _43093 _43095 _43094 _43096) (@lem3743004 A R _43093 _43095 _43094 _43096)). Qed.
Lemma lem3743006 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : True = ((term656 A _43095 _43096 R _43093 _43094) = (term760 A _43095 _43096 R _43093 _43094)).
Proof. exact (SYM (@lem3743005 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743007 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term656 A _43095 _43096 R _43093 _43094) = (term760 A _43095 _43096 R _43093 _43094).
Proof. exact (EQ_MP (@lem3743006 A _43095 _43096 R _43093 _43094) (@lem0)). Qed.
Lemma lem3743008 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : term760 A _43095 _43096 R _43093 _43094.
Proof. exact (EQ_MP (@lem3743007 A _43095 _43096 R _43093 _43094) (@lem3742642 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743010 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3743011 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term760 A _43095 _43096 R _43093 _43094) = (term761 A _43095 R _43093 _43094 _43096).
Proof. exact (@lem3743010 (term762 A _43095 _43096 R _43093 _43094) (term606 A _43094 _43096)). Qed.
Lemma lem3743013 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3743014 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term763 A _43095 _43096 R _43093 _43094) = (term764 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3743013 (term606 A _43093 _43095) (term651 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743016 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3743017 {A : Type'} (_43093 : A) (_43095 : A) : (term712 A _43093 _43095) = (_43093 = _43095).
Proof. exact (@lem3743016 (_43093 = _43095)). Qed.
Lemma lem3743018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3743019 {A : Type'} (_43093 : A) (_43095 : A) : (term713 A _43093 _43095) = (term714 A _43093 _43095).
Proof. exact (MK_COMB (@lem3743018) (@lem3743017 A _43093 _43095)). Qed.
Lemma lem3743021 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3743022 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term765 A _43095 _43096 R _43093 _43094) = (term766 A _43095 _43096 R _43093 _43094).
Proof. exact (@lem3743021 (R _43095 _43096) (term589 A R _43093 _43094)). Qed.
Lemma lem3743024 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3743025 {A : Type'} (R : type1402 A) (_43093 : A) (_43094 : A) : (term643 A R _43093 _43094) = (R _43093 _43094).
Proof. exact (@lem3743024 (R _43093 _43094)). Qed.
Lemma lem3743026 {A : Type'} (R : type1402 A) (_43095 : A) (_43096 : A) : (term767 A R _43095 _43096) = (term767 A R _43095 _43096).
Proof. exact (eq_refl (term767 A R _43095 _43096)). Qed.
Lemma lem3743027 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term766 A _43095 _43096 R _43093 _43094) = (term768 A _43095 _43096 R _43093 _43094).
Proof. exact (MK_COMB (@lem3743026 A R _43095 _43096) (@lem3743025 A R _43093 _43094)). Qed.
Lemma lem3743028 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term765 A _43095 _43096 R _43093 _43094) = (term768 A _43095 _43096 R _43093 _43094).
Proof. exact (TRANS (@lem3743022 A _43095 _43096 R _43093 _43094) (@lem3743027 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743029 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term764 A _43095 _43096 R _43093 _43094) = (term769 A _43095 _43096 R _43093 _43094).
Proof. exact (MK_COMB (@lem3743019 A _43093 _43095) (@lem3743028 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743030 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term763 A _43095 _43096 R _43093 _43094) = (term769 A _43095 _43096 R _43093 _43094).
Proof. exact (TRANS (@lem3743014 A _43095 _43096 R _43093 _43094) (@lem3743029 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3743032 {A : Type'} (_43095 : A) (_43096 : A) (R : type1402 A) (_43093 : A) (_43094 : A) : (term770 A _43095 _43096 R _43093 _43094) = (term771 A _43095 _43096 R _43093 _43094).
Proof. exact (MK_COMB (@lem3743031) (@lem3743030 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743033 {A : Type'} (_43094 : A) (_43096 : A) : (term606 A _43094 _43096) = (term606 A _43094 _43096).
Proof. exact (eq_refl (term606 A _43094 _43096)). Qed.
Lemma lem3743034 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term761 A _43095 R _43093 _43094 _43096) = (term772 A _43095 R _43093 _43094 _43096).
Proof. exact (MK_COMB (@lem3743032 A _43095 _43096 R _43093 _43094) (@lem3743033 A _43094 _43096)). Qed.
Lemma lem3743035 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : (term760 A _43095 _43096 R _43093 _43094) = (term772 A _43095 R _43093 _43094 _43096).
Proof. exact (TRANS (@lem3743011 A _43095 R _43093 _43094 _43096) (@lem3743034 A _43095 R _43093 _43094 _43096)). Qed.
Lemma lem3743037 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term773 A R y x.
Proof. exact (conj (@lem3742710 A x s R y h1) (@lem3742775 A x s R y h1)). Qed.
Lemma lem3743038 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term774 A R y x.
Proof. exact (conj (@lem3742701 A x) (@lem3743037 A x s R y h1)). Qed.
Lemma lem3743040 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : term772 A _43095 R _43093 _43094 _43096.
Proof. exact (EQ_MP (@lem3743035 A _43095 R _43093 _43094 _43096) (@lem3743008 A _43095 _43096 R _43093 _43094)). Qed.
Lemma lem3743041 {A : Type'} (_43095 : A) (R : type1402 A) (_43093 : A) (_43094 : A) (_43096 : A) : term772 A _43095 R _43093 _43094 _43096.
Proof. exact (@lem3743040 A _43095 R _43093 _43094 _43096). Qed.
Lemma lem3743042 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) : term775 A R y x.
Proof. exact (@lem3743041 A x R x (y x) x). Qed.
Lemma lem3743045 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term755 A y x.
Proof. exact (@lem3743042 A R y x (@lem3743038 A x s R y h1)). Qed.
Lemma lem3743046 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term776 A y x.
Proof. exact (fun h0 : (y x) = x => @lem3743045 A x s R y h1). Qed.
Lemma lem3743048 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3743049 {A : Type'} (y : A -> A) (x : A) : (term776 A y x) = (term755 A y x).
Proof. exact (@lem3743048 ((y x) = x)). Qed.
Lemma lem3743050 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term755 A y x.
Proof. exact (EQ_MP (@lem3743049 A y x) (@lem3743046 A x s R y h1)). Qed.
Lemma lem3743056 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3743057 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42927 : A) : (term623 A x s y _42927) = (term739 A x s y _42927).
Proof. exact (@lem3743056 ((y _42927) = x) (term606 A _42927 x) (term568 A s y _42927)). Qed.
Lemma lem3743073 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3743074 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term740 A x s y _42927) = (term741 A s y _42927 x).
Proof. exact (@lem3743073 (term568 A s y _42927) (term606 A _42927 x)). Qed.
Lemma lem3743082 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term569 A y _42927 x) = (term569 A y _42927 x).
Proof. exact (eq_refl (term569 A y _42927 x)). Qed.
Lemma lem3743083 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term739 A x s y _42927) = (term742 A s y _42927 x).
Proof. exact (MK_COMB (@lem3743082 A y _42927 x) (@lem3743074 A s y _42927 x)). Qed.
Lemma lem3743094 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term623 A x s y _42927) = (term742 A s y _42927 x).
Proof. exact (TRANS (@lem3743057 A x s y _42927) (@lem3743083 A s y _42927 x)). Qed.
Lemma lem3743095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3743096 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term743 A x s y _42927) = (term744 A s y _42927 x).
Proof. exact (MK_COMB (@lem3743095) (@lem3743094 A s y _42927 x)). Qed.
Lemma lem3743110 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3743111 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term777 A y _42927 x) = (term778 A y _42927 x).
Proof. exact (@lem3743110 ((y _42927) = x) (term606 A _42927 x)). Qed.
Lemma lem3743121 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) : (term779 A s y _42927) = (term779 A s y _42927).
Proof. exact (eq_refl (term779 A s y _42927)). Qed.
Lemma lem3743122 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term780 A s y _42927 x) = (term781 A s y _42927 x).
Proof. exact (MK_COMB (@lem3743121 A s y _42927) (@lem3743111 A y _42927 x)). Qed.
Lemma lem3743126 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3743127 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term781 A s y _42927 x) = (term742 A s y _42927 x).
Proof. exact (@lem3743126 ((y _42927) = x) (term568 A s y _42927) (term606 A _42927 x)). Qed.
Lemma lem3743147 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term780 A s y _42927 x) = (term742 A s y _42927 x).
Proof. exact (TRANS (@lem3743122 A s y _42927 x) (@lem3743127 A s y _42927 x)). Qed.
Lemma lem3743148 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : ((term623 A x s y _42927) = (term780 A s y _42927 x)) = ((term742 A s y _42927 x) = (term742 A s y _42927 x)).
Proof. exact (MK_COMB (@lem3743096 A s y _42927 x) (@lem3743147 A s y _42927 x)). Qed.
Lemma lem3743150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3743151 (x : Prop) : (x = x) = True.
Proof. exact (@lem3743150 Prop x). Qed.
Lemma lem3743152 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : ((term742 A s y _42927 x) = (term742 A s y _42927 x)) = True.
Proof. exact (@lem3743151 (term742 A s y _42927 x)). Qed.
Lemma lem3743153 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : ((term623 A x s y _42927) = (term780 A s y _42927 x)) = True.
Proof. exact (TRANS (@lem3743148 A s y _42927 x) (@lem3743152 A s y _42927 x)). Qed.
Lemma lem3743154 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : True = ((term623 A x s y _42927) = (term780 A s y _42927 x)).
Proof. exact (SYM (@lem3743153 A s y _42927 x)). Qed.
Lemma lem3743155 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) (x : A) : (term623 A x s y _42927) = (term780 A s y _42927 x).
Proof. exact (EQ_MP (@lem3743154 A s y _42927 x) (@lem0)). Qed.
Lemma lem3743156 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term780 A s y _42927 x.
Proof. exact (EQ_MP (@lem3743155 A s y _42927 x) (@lem3740205 A _42927 x s R y h1)). Qed.
Lemma lem3743158 (b : Prop) (a : Prop) : (a \/ b) = (term637 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3743159 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42927 : A) : (term780 A s y _42927 x) = (term782 A x s y _42927).
Proof. exact (@lem3743158 (term777 A y _42927 x) (term568 A s y _42927)). Qed.
Lemma lem3743161 (a : Prop) (b : Prop) : (term639 a b) = (term640 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3743162 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term783 A y _42927 x) = (term784 A y _42927 x).
Proof. exact (@lem3743161 (term606 A _42927 x) ((y _42927) = x)). Qed.
Lemma lem3743164 (a : Prop) : (term181 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3743165 {A : Type'} (_42927 : A) (x : A) : (term712 A _42927 x) = (_42927 = x).
Proof. exact (@lem3743164 (_42927 = x)). Qed.
Lemma lem3743166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3743167 {A : Type'} (_42927 : A) (x : A) : (term713 A _42927 x) = (term714 A _42927 x).
Proof. exact (MK_COMB (@lem3743166) (@lem3743165 A _42927 x)). Qed.
Lemma lem3743168 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term693 A y _42927 x) = (term693 A y _42927 x).
Proof. exact (eq_refl (term693 A y _42927 x)). Qed.
Lemma lem3743169 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term784 A y _42927 x) = (term785 A y _42927 x).
Proof. exact (MK_COMB (@lem3743167 A _42927 x) (@lem3743168 A y _42927 x)). Qed.
Lemma lem3743170 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term783 A y _42927 x) = (term785 A y _42927 x).
Proof. exact (TRANS (@lem3743162 A y _42927 x) (@lem3743169 A y _42927 x)). Qed.
Lemma lem3743171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3743172 {A : Type'} (y : A -> A) (_42927 : A) (x : A) : (term786 A y _42927 x) = (term787 A y _42927 x).
Proof. exact (MK_COMB (@lem3743171) (@lem3743170 A y _42927 x)). Qed.
Lemma lem3743173 {A : Type'} (s : A -> Prop) (y : A -> A) (_42927 : A) : (term568 A s y _42927) = (term568 A s y _42927).
Proof. exact (eq_refl (term568 A s y _42927)). Qed.
Lemma lem3743174 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42927 : A) : (term782 A x s y _42927) = (term788 A x s y _42927).
Proof. exact (MK_COMB (@lem3743172 A y _42927 x) (@lem3743173 A s y _42927)). Qed.
Lemma lem3743175 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (_42927 : A) : (term780 A s y _42927 x) = (term788 A x s y _42927).
Proof. exact (TRANS (@lem3743159 A x s y _42927) (@lem3743174 A x s y _42927)). Qed.
Lemma lem3743177 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term789 A y x.
Proof. exact (conj (@lem3742693 A x) (@lem3743050 A x s R y h1)). Qed.
Lemma lem3743179 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term788 A x s y _42927.
Proof. exact (EQ_MP (@lem3743175 A x s y _42927) (@lem3743156 A _42927 x s R y h1)). Qed.
Lemma lem3743180 {A : Type'} (_42927 : A) (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term788 A x s y _42927.
Proof. exact (@lem3743179 A _42927 x s R y h1). Qed.
Lemma lem3743181 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term790 A s y x.
Proof. exact (@lem3743180 A x x s R y h1). Qed.
Lemma lem3743184 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term568 A s y x.
Proof. exact (@lem3743181 A x s R y h1 (@lem3743177 A x s R y h1)). Qed.
Lemma lem3743185 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term791 A s y x.
Proof. exact (fun h0 : term675 A s y x => @lem3743184 A x s R y h1). Qed.
Lemma lem3743187 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3743188 {A : Type'} (s : A -> Prop) (y : A -> A) (x : A) : (term791 A s y x) = (term568 A s y x).
Proof. exact (@lem3743187 (term568 A s y x)). Qed.
Lemma lem3743189 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term561 A x s R y) : term568 A s y x.
Proof. exact (EQ_MP (@lem3743188 A s y x) (@lem3743185 A x s R y h1)). Qed.
Lemma lem3743192 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3743194 {A : Type'} (s : A -> Prop) (_42928 : A) : (term576 A s _42928) = (term792 A s _42928).
Proof. exact (@lem3743192 (@I (A -> Prop) s _42928)). Qed.
Lemma lem3743197 {A : Type'} (_42928 : A) (s : A -> Prop) (h1 : term588 A s) : term792 A s _42928.
Proof. exact (EQ_MP (@lem3743194 A s _42928) (@lem3740163 A _42928 s h1)). Qed.
Lemma lem3743198 {A : Type'} (_42928 : A) (s : A -> Prop) (h1 : term588 A s) : term792 A s _42928.
Proof. exact (@lem3743197 A _42928 s h1). Qed.
Lemma lem3743199 {A : Type'} (y : A -> A) (x : A) (s : A -> Prop) (h1 : term588 A s) : term793 A s y x.
Proof. exact (@lem3743198 A (y x) s h1). Qed.
Lemma lem3743202 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term588 A s) (h2 : term561 A x s R y) : False.
Proof. exact (@lem3743199 A y x s h1 (@lem3743189 A x s R y h2)). Qed.
Lemma lem3743203 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term588 A s) (h2 : term561 A x s R y) : term628.
Proof. exact (fun h0 : ~ False => @lem3743202 A x s R y h1 h2). Qed.
Lemma lem3743205 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3743206 : term628 = False.
Proof. exact (@lem3743205 False). Qed.
Lemma lem3743271 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3743272 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : term659 A s x'.
Proof. exact (fun h0 : term576 A s x' => @lem3743271 A s x' h1). Qed.
Lemma lem3743274 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3743275 {A : Type'} (s : A -> Prop) (x' : A) : (term659 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3743274 (@I (A -> Prop) s x')). Qed.
Lemma lem3743276 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem3743275 A s x') (@lem3743272 A s x' h1)). Qed.
Lemma lem3743279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3743281 {A : Type'} (s : A -> Prop) (_42934 : A) : (term576 A s _42934) = (term792 A s _42934).
Proof. exact (@lem3743279 (@I (A -> Prop) s _42934)). Qed.
Lemma lem3743284 {A : Type'} (_42934 : A) (s : A -> Prop) (h1 : term588 A s) : term792 A s _42934.
Proof. exact (EQ_MP (@lem3743281 A s _42934) (@lem3739583 A _42934 s h1)). Qed.
Lemma lem3743285 {A : Type'} (_42934 : A) (s : A -> Prop) (h1 : term588 A s) : term792 A s _42934.
Proof. exact (@lem3743284 A _42934 s h1). Qed.
Lemma lem3743286 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term588 A s) : term792 A s x'.
Proof. exact (@lem3743285 A x' s h1). Qed.
Lemma lem3743289 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (@lem3743286 A x' s h1 (@lem3743276 A s x' h2)). Qed.
Lemma lem3743290 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : term628.
Proof. exact (fun h0 : ~ False => @lem3743289 A s x' h1 h2). Qed.
Lemma lem3743292 (p : Prop) : (term626 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3743293 : term628 = False.
Proof. exact (@lem3743292 False). Qed.
Lemma lem3743294 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3743293) (@lem3743290 A s x' h1 h2)). Qed.
Lemma lem3743295 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term588 A s) (h2 : term561 A x s R y) : False.
Proof. exact (EQ_MP (@lem3743206) (@lem3743203 A x s R y h1 h2)). Qed.
Lemma lem3743296 {A : Type'} (x : A) (y : A -> A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') : False.
Proof. exact (EQ_MP (@lem3741706) (@lem3741703 A x y s R x'' h1 h2)). Qed.
Lemma lem3743297 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) : False.
Proof. exact (EQ_MP (@lem3740591) (@lem3740588 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3743298 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3740306 A x s y R x'' h1 h2) (fun h3 : False => @lem3739701 A R x'' h2)). Qed.
Lemma lem3743300 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743298 A x s y R x'' h1 h2) (@lem3739701 A R x'' h2)). Qed.
Lemma lem3743301 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x' => @lem3743294 A s x' h1 h2) (fun h3 : False => @lem3739585 A s x' h2)). Qed.
Lemma lem3743302 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3743301 A s x' h1 h2) (@lem3739585 A s x' h2)). Qed.
Lemma lem3743303 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3740393 A x s y R x'' h1 h2) (fun h3 : False => @lem3739239 A R x'' h2)). Qed.
Lemma lem3743304 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743303 A x s y R x'' h1 h2) (@lem3739239 A R x'' h2)). Qed.
Lemma lem3743305 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3743300 A x s y R x'' h1 h2) (fun h3 : False => @lem3739185 A R x'' h2)). Qed.
Lemma lem3743306 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743305 A x s y R x'' h1 h2) (@lem3739185 A R x'' h2)). Qed.
Lemma lem3743307 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x' => @lem3743302 A s x' h1 h2) (fun h3 : False => @lem3738985 A s x' h2)). Qed.
Lemma lem3743308 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3743307 A s x' h1 h2) (@lem3738985 A s x' h2)). Qed.
Lemma lem3743309 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3743304 A x s y R x'' h1 h2) (fun h3 : False => @lem3738375 A R x'' h2)). Qed.
Lemma lem3743310 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743309 A x s y R x'' h1 h2) (@lem3738375 A R x'' h2)). Qed.
Lemma lem3743311 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3743306 A x s y R x'' h1 h2) (fun h3 : False => @lem3738282 A R x'' h2)). Qed.
Lemma lem3743312 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743311 A x s y R x'' h1 h2) (@lem3738282 A R x'' h2)). Qed.
Lemma lem3743313 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x' => @lem3743308 A s x' h1 h2) (fun h3 : False => @lem3738985 A s x' h2)). Qed.
Lemma lem3743314 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3743313 A s x' h1 h2) (@lem3738985 A s x' h2)). Qed.
Lemma lem3743315 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : (term588 A s) = False.
Proof. exact (prop_ext (fun h3 : term588 A s => @lem3743314 A s x' h1 h2) (fun h3 : False => @lem3738981 A s h1)). Qed.
Lemma lem3743316 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3743315 A s x' h1 h2) (@lem3738981 A s h1)). Qed.
Lemma lem3743317 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term588 A s) (h2 : term561 A x s R y) : (term588 A s) = False.
Proof. exact (prop_ext (fun h3 : term588 A s => @lem3743295 A x s R y h1 h2) (fun h3 : False => @lem3738885 A s h1)). Qed.
Lemma lem3743318 {A : Type'} (x : A) (s : A -> Prop) (R : type1402 A) (y : A -> A) (h1 : term588 A s) (h2 : term561 A x s R y) : False.
Proof. exact (EQ_MP (@lem3743317 A x s R y h1 h2) (@lem3738885 A s h1)). Qed.
Lemma lem3743319 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3743310 A x s y R x'' h1 h2) (fun h3 : False => @lem3738375 A R x'' h2)). Qed.
Lemma lem3743320 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743319 A x s y R x'' h1 h2) (@lem3738375 A R x'' h2)). Qed.
Lemma lem3743321 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : (R x'' x'') = False.
Proof. exact (prop_ext (fun h3 : R x'' x'' => @lem3743312 A x s y R x'' h1 h2) (fun h3 : False => @lem3738282 A R x'' h2)). Qed.
Lemma lem3743322 {A : Type'} (x : A) (s : A -> Prop) (y : A -> A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : R x'' x'') : False.
Proof. exact (EQ_MP (@lem3743321 A x s y R x'' h1 h2) (@lem3738282 A R x'' h2)). Qed.
Lemma lem3743323 {A : Type'} (R : type1402 A) (y : A -> A) (x : A) (s : A -> Prop) (x' : A) (h1 : term588 A s) (h2 : term561 A x s R y) (h3 : term140 A x s x') : False.
Proof. exact (or_elim (@lem3737954 A x s x' h3) (fun h0 : x' = x => @lem3743318 A x s R y h1 h2) (fun h0 : @I (A -> Prop) s x' => @lem3743316 A s x' h1 h0)). Qed.
Lemma lem3743324 {A : Type'} (y : A -> A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term561 A x s R y) (h2 : term596 A s R x'') (h3 : term140 A x s x') : False.
Proof. exact (or_elim (@lem3737954 A x s x' h3) (fun h0 : x' = x => @lem3743296 A x y s R x'' h1 h2) (fun h0 : @I (A -> Prop) s x' => @lem3742623 A x y s R x'' h1 h2)). Qed.
Lemma lem3743325 {A : Type'} (y : A -> A) (y' : A) (R : type1402 A) (x'' : A) (z : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term561 A x s R y) (h2 : term206 A y' R x'' z) (h3 : term140 A x s x') : False.
Proof. exact (or_elim (@lem3737954 A x s x' h3) (fun h0 : x' = x => @lem3743297 A x s y y' R x'' z h1 h2) (fun h0 : @I (A -> Prop) s x' => @lem3740791 A x s y y' R x'' z h1 h2)). Qed.
Lemma lem3743326 {A : Type'} (y : A -> A) (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term561 A x s R y) (h2 : term597 A y' z s R x'') (h3 : term140 A x s x') : False.
Proof. exact (or_elim (@lem3738177 A y' z s R x'' h2) (fun h0 : term206 A y' R x'' z => @lem3743325 A y y' R x'' z x s x' h1 h0 h3) (fun h0 : term596 A s R x'' => @lem3743324 A y R x'' x s x' h1 h0 h3)). Qed.
Lemma lem3743327 {A : Type'} (y : A -> A) (x : A) (s : A -> Prop) (x' : A) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term140 A x s x') (h3 : R x'' x'') : False.
Proof. exact (or_elim (@lem3737954 A x s x' h2) (fun h0 : x' = x => @lem3743322 A x s y R x'' h1 h3) (fun h0 : @I (A -> Prop) s x' => @lem3743320 A x s y R x'' h1 h3)). Qed.
Lemma lem3743328 {A : Type'} (y : A -> A) (x : A) (x' : A) (y' : A) (z : A) (s : A -> Prop) (R : type1402 A) (x'' : A) (h1 : term561 A x s R y) (h2 : term140 A x s x') (h3 : term598 A y' z s R x'') : False.
Proof. exact (or_elim (@lem3738174 A y' z s R x'' h3) (fun h0 : R x'' x'' => @lem3743327 A y x s x' R x'' h1 h2 h0) (fun h0 : term597 A y' z s R x'' => @lem3743326 A y y' z R x'' x s x' h1 h0 h2)). Qed.
Lemma lem3743329 {A : Type'} (y : A -> A) (y' : A) (z : A) (R : type1402 A) (x'' : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term561 A x s R y) (h2 : term466 A y' z R x'' x s) (h3 : term140 A x s x') : False.
Proof. exact (or_elim (@lem3738167 A y' z R x'' x s h2) (fun h0 : term598 A y' z s R x'' => @lem3743328 A y x x' y' z s R x'' h1 h3 h0) (fun h0 : term588 A s => @lem3743323 A R y x s x' h0 h1 h3)). Qed.
Lemma lem3743330 {A : Type'} (y' : A) (x'' : A) (R : type1402 A) (y : A -> A) (x : A) (s : A -> Prop) (x' : A) (h1 : term469 A y' R x'' x s) (h2 : term561 A x s R y) (h3 : term140 A x s x') : False.
Proof. exact (ex_elim (@lem3737936 A y' R x'' x s h1) (fun z : A => fun h0 : term468 A y' R x'' x s z => @lem3743329 A y y' z R x'' x s x' h2 h0 h3)). Qed.
Lemma lem3743331 {A : Type'} (x'' : A) (R : type1402 A) (y : A -> A) (x : A) (s : A -> Prop) (x' : A) (h1 : term471 A R x'' x s) (h2 : term561 A x s R y) (h3 : term140 A x s x') : False.
Proof. exact (ex_elim (@lem3737935 A R x'' x s h1) (fun y' : A => fun h0 : term470 A R x'' x s y' => @lem3743330 A y' x'' R y x s x' h0 h2 h3)). Qed.
Lemma lem3743332 {A : Type'} (y : A -> A) (R : type1402 A) (x : A) (s : A -> Prop) (x' : A) (h1 : term561 A x s R y) (h2 : term135 A R x s) (h3 : term140 A x s x') : False.
Proof. exact (ex_elim (@lem3737604 A R x s h2) (fun x'' : A => fun h0 : term472 A R x s x'' => @lem3743331 A x'' R y x s x' h0 h1 h3)). Qed.
Lemma lem3743333 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (x' : A) (h1 : term160 A x s R) (h2 : term135 A R x s) (h3 : term140 A x s x') : False.
Proof. exact (ex_elim (@lem3737923 A x s R h1) (fun y : A -> A => fun h0 : term563 A x s R y => @lem3743332 A y R x s x' h0 h2 h3)). Qed.
Lemma lem3743334 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (x' : A) (h1 : term160 A x s R) (h2 : term135 A R x s) (h3 : term140 A x s x') : (term140 A x s x') = False.
Proof. exact (prop_ext (fun h4 : term140 A x s x' => @lem3743333 A R x s x' h1 h2 h3) (fun h4 : False => @lem3737933 A x s x' h3)). Qed.
Lemma lem3743335 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (x' : A) (h1 : term160 A x s R) (h2 : term135 A R x s) (h3 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem3743334 A R x s x' h1 h2 h3) (@lem3737933 A x s x' h3)). Qed.
Lemma lem3743336 {A : Type'} (x' : A) (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term160 A x s R) (h2 : term135 A R x s) : term794 A x s x'.
Proof. exact (fun h0 : term140 A x s x' => @lem3743335 A R x s x' h1 h2 h0). Qed.
Lemma lem3743337 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term794 A x s x') = (term164 A x s x').
Proof. exact (@lem69 (term140 A x s x')). Qed.
Lemma lem3743338 {A : Type'} (x' : A) (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term160 A x s R) (h2 : term135 A R x s) : term164 A x s x'.
Proof. exact (EQ_MP (@lem3743337 A x s x') (@lem3743336 A x' R x s h1 h2)). Qed.
Lemma lem3743343 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term160 A x s R) (h2 : term135 A R x s) : term167 A x s.
Proof. exact (fun x' : A => @lem3743338 A x' R x s h1 h2). Qed.
Lemma lem3743344 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) (h1 : term135 A R x s) : term168 A R x s.
Proof. exact (fun h0 : term160 A x s R => @lem3743343 A R x s h0 h1). Qed.
Lemma lem3743345 {A : Type'} (R : type1402 A) (x : A) (s : A -> Prop) : term169 A R x s.
Proof. exact (fun h0 : term135 A R x s => @lem3743344 A R x s h0). Qed.
Lemma lem3743350 {A : Type'} (R : type1402 A) (x : A) : term171 A R x.
Proof. exact (fun s : A -> Prop => @lem3743345 A R x s). Qed.
Lemma lem3743355 {A : Type'} (R : type1402 A) : term173 A R.
Proof. exact (fun x : A => @lem3743350 A R x). Qed.
Lemma lem3743360 {A : Type'} : term185 A.
Proof. exact (fun R : type1402 A => @lem3743355 A R). Qed.
Lemma lem3743361 {A : Type'} : term184 A.
Proof. exact (EQ_MP (@lem3737012 A) (@lem3743360 A)). Qed.
Lemma lem3743362 {A : Type'} (R : type1402 A) : term795 A R.
Proof. exact (@lem3743361 A R). Qed.
Lemma lem3743363 {A : Type'} (R : type1402 A) : (term795 A R) = (term175 A R).
Proof. exact (eq_refl (term795 A R)). Qed.
Lemma lem3743364 {A : Type'} (R : type1402 A) : term175 A R.
Proof. exact (EQ_MP (@lem3743363 A R) (@lem3743362 A R)). Qed.
Lemma lem3743366 {A : Type'} (R : type1402 A) : term175 A R.
Proof. exact (@lem3736530 A R (@lem3743364 A R)). Qed.
Lemma lem3743367 {A : Type'} (R : type1402 A) (h1 : term176 A R) : False.
Proof. exact (@lem3743366 A R (@lem3736514 A R h1)). Qed.
Lemma lem3743368 {A : Type'} (R : type1402 A) (h1 : term176 A R) : (term176 A R) = False.
Proof. exact (prop_ext (fun h2 : term176 A R => @lem3743367 A R h1) (fun h2 : False => @lem3736514 A R h1)). Qed.
Lemma lem3743369 {A : Type'} (R : type1402 A) (h1 : term176 A R) : False.
Proof. exact (EQ_MP (@lem3743368 A R h1) (@lem3736514 A R h1)). Qed.
Lemma lem3743370 {A : Type'} (R : type1402 A) : term175 A R.
Proof. exact (fun h0 : term176 A R => @lem3743369 A R h0). Qed.
Lemma lem3743371 {A : Type'} (R : type1402 A) : term173 A R.
Proof. exact (EQ_MP (@lem3736513 A R) (@lem3743370 A R)). Qed.
Lemma lem3743372 {A : Type'} (R : type1402 A) : term102 A R.
Proof. exact (EQ_MP (@lem3736509 A R) (@lem3743371 A R)). Qed.
Lemma lem3743373 {A : Type'} (R : type1402 A) : term52 A R.
Proof. exact (EQ_MP (@lem3736192 A R) (@lem3743372 A R)). Qed.
Lemma lem3743374 {A : Type'} (R : type1402 A) : term54 A R.
Proof. exact (EQ_MP (@lem3736040 A R) (@lem3743373 A R)). Qed.
Lemma lem3743375 {A : Type'} (R : type1402 A) : term25 A R.
Proof. exact (@lem3735728 A R (@lem3743374 A R)). Qed.
Lemma lem3743376 {A : Type'} (R : type1402 A) : term24 A R.
Proof. exact (EQ_MP (@lem3735695 A R) (@lem3743375 A R)). Qed.
Lemma lem3743381 {A : Type'} : term796 A.
Proof. exact (fun R : type1402 A => @lem3743376 A R). Qed.
