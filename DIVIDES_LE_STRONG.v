Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_LE_STRONG_term_abbrevs.
Require Import DIVIDES_LE_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_1_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3073436_spec.
Require Import thm3074596_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3082303 (m : nat) : term0 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem3082304 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3082305 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3082304 m) (@lem3082303 m)). Qed.
Lemma lem3082307 (m : nat) (h1 : term2 m) : term2 m.
Proof. exact (h1). Qed.
Lemma lem3082308 (n : nat) : term3 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem3082309 (n : nat) : (term3 n) = (term4 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem3082310 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem3082309 n) (@lem3082308 n)). Qed.
Lemma lem3082311 (n : nat) : (term4 n) = ((term4 n) = True).
Proof. exact (@lem7 (term4 n)). Qed.
Lemma lem3082445 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term5 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3082446 (p : Prop) (q : Prop) (p' : Prop) : term6 p q p'.
Proof. exact (fun q' : Prop => @lem3082445 p q p' q'). Qed.
Lemma lem3082447 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (fun p' : Prop => @lem3082446 p q p'). Qed.
Lemma lem3082448 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem3082447 (num_divides m n) (term9 m n)). Qed.
Lemma lem3082449 (m : nat) (n : nat) (p' : Prop) : term10 m n p'.
Proof. exact (@lem3082448 m n p'). Qed.
Lemma lem3082450 (m : nat) (n : nat) (p' : Prop) : (term10 m n p') = (term11 m n p').
Proof. exact (eq_refl (term10 m n p')). Qed.
Lemma lem3082451 (m : nat) (n : nat) (p' : Prop) : term11 m n p'.
Proof. exact (EQ_MP (@lem3082450 m n p') (@lem3082449 m n p')). Qed.
Lemma lem3082452 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term12 m n p' q'.
Proof. exact (@lem3082451 m n p' q'). Qed.
Lemma lem3082453 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term12 m n p' q') = (term13 m n p' q').
Proof. exact (eq_refl (term12 m n p' q')). Qed.
Lemma lem3082454 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term13 m n p' q'.
Proof. exact (EQ_MP (@lem3082453 m n p' q') (@lem3082452 m n p' q')). Qed.
Lemma lem3082456 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3082457 : num_divides = num_divides.
Proof. exact (eq_refl num_divides). Qed.
Lemma lem3082458 (m : nat) (h1 : m = (NUMERAL 0)) : (num_divides m) = term14.
Proof. exact (MK_COMB (@lem3082457) (@lem3082456 m h1)). Qed.
Lemma lem3082459 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3082460 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (num_divides m n) = (term15 n).
Proof. exact (MK_COMB (@lem3082458 m h1) (@lem3082459 n)). Qed.
Lemma lem3082461 (m : nat) (n : nat) (q' : Prop) : term16 m n q'.
Proof. exact (@lem3082454 m n (term15 n) q'). Qed.
Lemma lem3082462 (n : nat) (q' : Prop) (m : nat) (h1 : m = (NUMERAL 0)) : term17 m n q'.
Proof. exact (@lem3082461 m n q' (@lem3082460 n m h1)). Qed.
Lemma lem3083181 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3083182 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem3083183 (m : nat) (h1 : m = (NUMERAL 0)) : (term19 m) = term20.
Proof. exact (MK_COMB (@lem3083182) (@lem3083181 m h1)). Qed.
Lemma lem3083464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3083465 (m : nat) (h1 : m = (NUMERAL 0)) : (term21 m) = term22.
Proof. exact (MK_COMB (@lem3083464) (@lem3083183 m h1)). Qed.
Lemma lem3083747 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3083748 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3083749 (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m) = term23.
Proof. exact (MK_COMB (@lem3083748) (@lem3083747 m h1)). Qed.
Lemma lem3083750 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3083751 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m n) = (term4 n).
Proof. exact (MK_COMB (@lem3083749 m h1) (@lem3083750 n)). Qed.
Lemma lem3083753 (n : nat) : (term4 n) = True.
Proof. exact (EQ_MP (@lem3082311 n) (@lem3082310 n)). Qed.
Lemma lem3083754 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m n) = True.
Proof. exact (TRANS (@lem3083751 n m h1) (@lem3083753 n)). Qed.
Lemma lem3083755 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term24 m n) = term25.
Proof. exact (MK_COMB (@lem3083465 m h1) (@lem3083754 n m h1)). Qed.
Lemma lem3083757 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3083758 : term25 = term20.
Proof. exact (@lem3083757 term20). Qed.
Lemma lem3084039 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term24 m n) = term20.
Proof. exact (TRANS (@lem3083755 n m h1) (@lem3083758)). Qed.
Lemma lem3084040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3084041 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term26 m n) = term27.
Proof. exact (MK_COMB (@lem3084040) (@lem3084039 n m h1)). Qed.
Lemma lem3084420 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem3084421 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term9 m n) = (term28 n).
Proof. exact (MK_COMB (@lem3084041 n m h1) (@lem3084420 n)). Qed.
Lemma lem3084804 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term29 m n.
Proof. exact (fun h0 : term15 n => @lem3084421 n m h1). Qed.
Lemma lem3084805 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term30 m n.
Proof. exact (@lem3082462 n (term28 n) m h1). Qed.
Lemma lem3084806 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term31 m n) = (term32 n).
Proof. exact (@lem3084805 n m h1 (@lem3084804 n m h1)). Qed.
Lemma lem3085594 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term32 n) = (term31 m n).
Proof. exact (SYM (@lem3084806 n m h1)). Qed.
Lemma lem3085600 : term33.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem3085601 : term34.
Proof. exact (proj2 (@lem3085600)). Qed.
Lemma lem3085602 : term35.
Proof. exact (proj2 (@lem3085601)). Qed.
Lemma lem3085603 : term36.
Proof. exact (proj2 (@lem3085602)). Qed.
Lemma lem3085633 : term37.
Proof. exact (proj1 (@lem3085603)). Qed.
Lemma lem3085634 (n : nat) : term38 n.
Proof. exact (@lem3085633 n). Qed.
Lemma lem3085635 (n : nat) : (term38 n) = (term39 n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem3085636 (n : nat) : term39 n.
Proof. exact (EQ_MP (@lem3085635 n) (@lem3085634 n)). Qed.
Lemma lem3085637 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem3085638 (n : nat) (h1 : term19 n) : term40 n.
Proof. exact (@lem3085636 n (@lem3085637 n h1)). Qed.
Lemma lem3085639 (n : nat) : (term40 n) = ((term40 n) = True).
Proof. exact (@lem7 (term40 n)). Qed.
Lemma lem3085640 (n : nat) (h1 : term19 n) : (term40 n) = True.
Proof. exact (EQ_MP (@lem3085639 n) (@lem3085638 n h1)). Qed.
Lemma lem3085646 : term41.
Proof. exact (proj1 (@lem3085602)). Qed.
Lemma lem3085647 (n : nat) : term42 n.
Proof. exact (@lem3085646 n). Qed.
Lemma lem3085648 (n : nat) : (term42 n) = (term43 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem3085649 (n : nat) : term43 n.
Proof. exact (EQ_MP (@lem3085648 n) (@lem3085647 n)). Qed.
Lemma lem3085650 (n : nat) (h1 : term40 n) : term40 n.
Proof. exact (h1). Qed.
Lemma lem3085651 (n : nat) (h1 : term40 n) : term19 n.
Proof. exact (@lem3085649 n (@lem3085650 n h1)). Qed.
Lemma lem3085652 (n : nat) : (term19 n) = ((term19 n) = True).
Proof. exact (@lem7 (term19 n)). Qed.
Lemma lem3085653 (n : nat) (h1 : term40 n) : (term19 n) = True.
Proof. exact (EQ_MP (@lem3085652 n) (@lem3085651 n h1)). Qed.
Lemma lem3085688 : term44.
Proof. exact (proj1 (@lem3085600)). Qed.
Lemma lem3085689 (n : nat) : term45 n.
Proof. exact (@lem3085688 n). Qed.
Lemma lem3085690 (n : nat) : (term45 n) = (term46 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem3085691 (n : nat) : term46 n.
Proof. exact (EQ_MP (@lem3085690 n) (@lem3085689 n)). Qed.
Lemma lem3085692 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem3085693 (n : nat) (h1 : term2 n) : term19 n.
Proof. exact (@lem3085691 n (@lem3085692 n h1)). Qed.
Lemma lem3085694 (n : nat) : (term19 n) = ((term19 n) = True).
Proof. exact (@lem7 (term19 n)). Qed.
Lemma lem3085695 (n : nat) (h1 : term2 n) : (term19 n) = True.
Proof. exact (EQ_MP (@lem3085694 n) (@lem3085693 n h1)). Qed.
Lemma lem3085714 (m : nat) : term47 m.
Proof. exact (@lem3082292 m). Qed.
Lemma lem3085715 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem3085716 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem3085715 m) (@lem3085714 m)). Qed.
Lemma lem3085717 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem3085716 m n). Qed.
Lemma lem3085718 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem3085719 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem3085718 m n) (@lem3085717 m n)). Qed.
Lemma lem3085720 (m : nat) (n : nat) (h1 : num_divides m n) : num_divides m n.
Proof. exact (h1). Qed.
Lemma lem3085721 (m : nat) (n : nat) (h1 : num_divides m n) : term51 m n.
Proof. exact (@lem3085719 m n (@lem3085720 m n h1)). Qed.
Lemma lem3085722 (m : nat) (n : nat) : (term51 m n) = ((term51 m n) = True).
Proof. exact (@lem7 (term51 m n)). Qed.
Lemma lem3085723 (m : nat) (n : nat) (h1 : num_divides m n) : (term51 m n) = True.
Proof. exact (EQ_MP (@lem3085722 m n) (@lem3085721 m n h1)). Qed.
Lemma lem3085729 (m : nat) : term52 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem3085745 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term5 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3085746 (p : Prop) (q : Prop) (p' : Prop) : term6 p q p'.
Proof. exact (fun q' : Prop => @lem3085745 p q p' q'). Qed.
Lemma lem3085747 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (fun p' : Prop => @lem3085746 p q p'). Qed.
Lemma lem3085748 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem3085747 (num_divides m n) (term9 m n)). Qed.
Lemma lem3085749 (m : nat) (n : nat) (p' : Prop) : term10 m n p'.
Proof. exact (@lem3085748 m n p'). Qed.
Lemma lem3085750 (m : nat) (n : nat) (p' : Prop) : (term10 m n p') = (term11 m n p').
Proof. exact (eq_refl (term10 m n p')). Qed.
Lemma lem3085751 (m : nat) (n : nat) (p' : Prop) : term11 m n p'.
Proof. exact (EQ_MP (@lem3085750 m n p') (@lem3085749 m n p')). Qed.
Lemma lem3085752 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term12 m n p' q'.
Proof. exact (@lem3085751 m n p' q'). Qed.
Lemma lem3085753 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term12 m n p' q') = (term13 m n p' q').
Proof. exact (eq_refl (term12 m n p' q')). Qed.
Lemma lem3085754 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term13 m n p' q'.
Proof. exact (EQ_MP (@lem3085753 m n p' q') (@lem3085752 m n p' q')). Qed.
Lemma lem3085755 (m : nat) (n : nat) : (num_divides m n) = (num_divides m n).
Proof. exact (eq_refl (num_divides m n)). Qed.
Lemma lem3085756 (m : nat) (n : nat) (q' : Prop) : term53 m n q'.
Proof. exact (@lem3085754 m n (num_divides m n) q'). Qed.
Lemma lem3085757 (m : nat) (n : nat) (q' : Prop) : term54 m n q'.
Proof. exact (@lem3085756 m n q' (@lem3085755 m n)). Qed.
Lemma lem3085758 (m : nat) (n : nat) (h1 : num_divides m n) : num_divides m n.
Proof. exact (h1). Qed.
Lemma lem3085759 (m : nat) (n : nat) : (num_divides m n) = ((num_divides m n) = True).
Proof. exact (@lem7 (num_divides m n)). Qed.
Lemma lem3085766 (n : nat) : term55 n.
Proof. exact (fun h0 : term40 n => @lem3085653 n h0). Qed.
Lemma lem3085767 (m : nat) : term55 m.
Proof. exact (@lem3085766 m). Qed.
Lemma lem3085769 (n : nat) : term56 n.
Proof. exact (fun h0 : term19 n => @lem3085640 n h0). Qed.
Lemma lem3085770 (m : nat) : term56 m.
Proof. exact (@lem3085769 m). Qed.
Lemma lem3085783 (n : nat) : term57 n.
Proof. exact (fun h0 : term2 n => @lem3085695 n h0). Qed.
Lemma lem3085784 (m : nat) : term57 m.
Proof. exact (@lem3085783 m). Qed.
Lemma lem3085786 (m : nat) (h1 : term2 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem3085729 m (@lem3082307 m h1)). Qed.
Lemma lem3085787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3085788 (m : nat) (h1 : term2 m) : (term2 m) = (~ False).
Proof. exact (MK_COMB (@lem3085787) (@lem3085786 m h1)). Qed.
Lemma lem3085790 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3085791 (m : nat) (h1 : term2 m) : (term2 m) = True.
Proof. exact (TRANS (@lem3085788 m h1) (@lem3085790)). Qed.
Lemma lem3085792 (m : nat) (h1 : term2 m) : True = (term2 m).
Proof. exact (SYM (@lem3085791 m h1)). Qed.
Lemma lem3085793 (m : nat) (h1 : term2 m) : term2 m.
Proof. exact (EQ_MP (@lem3085792 m h1) (@lem0)). Qed.
Lemma lem3085794 (m : nat) (h1 : term2 m) : (term19 m) = True.
Proof. exact (@lem3085784 m (@lem3085793 m h1)). Qed.
Lemma lem3085795 (m : nat) (h1 : term2 m) : True = (term19 m).
Proof. exact (SYM (@lem3085794 m h1)). Qed.
Lemma lem3085796 (m : nat) (h1 : term2 m) : term19 m.
Proof. exact (EQ_MP (@lem3085795 m h1) (@lem0)). Qed.
Lemma lem3085797 (m : nat) (h1 : term2 m) : (term40 m) = True.
Proof. exact (@lem3085770 m (@lem3085796 m h1)). Qed.
Lemma lem3085798 (m : nat) (h1 : term2 m) : True = (term40 m).
Proof. exact (SYM (@lem3085797 m h1)). Qed.
Lemma lem3085799 (m : nat) (h1 : term2 m) : term40 m.
Proof. exact (EQ_MP (@lem3085798 m h1) (@lem0)). Qed.
Lemma lem3085800 (m : nat) (h1 : term2 m) : (term19 m) = True.
Proof. exact (@lem3085767 m (@lem3085799 m h1)). Qed.
Lemma lem3085801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3085802 (m : nat) (h1 : term2 m) : (term21 m) = (and True).
Proof. exact (MK_COMB (@lem3085801) (@lem3085800 m h1)). Qed.
Lemma lem3085803 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem3085804 (n : nat) (m : nat) (h1 : term2 m) : (term24 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem3085802 m h1) (@lem3085803 m n)). Qed.
Lemma lem3085806 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3085807 (m : nat) (n : nat) : (term58 m n) = (Peano.le m n).
Proof. exact (@lem3085806 (Peano.le m n)). Qed.
Lemma lem3085808 (n : nat) (m : nat) (h1 : term2 m) : (term24 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem3085804 n m h1) (@lem3085807 m n)). Qed.
Lemma lem3085809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3085810 (n : nat) (m : nat) (h1 : term2 m) : (term26 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem3085809) (@lem3085808 n m h1)). Qed.
Lemma lem3085909 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem3085910 (n : nat) (m : nat) (h1 : term2 m) : (term9 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem3085810 n m h1) (@lem3085909 n)). Qed.
Lemma lem3085912 (m : nat) (n : nat) : term60 m n.
Proof. exact (fun h0 : num_divides m n => @lem3085723 m n h0). Qed.
Lemma lem3085914 (m : nat) (n : nat) (h1 : num_divides m n) : (num_divides m n) = True.
Proof. exact (EQ_MP (@lem3085759 m n) (@lem3085758 m n h1)). Qed.
Lemma lem3085915 (m : nat) (n : nat) (h1 : num_divides m n) : True = (num_divides m n).
Proof. exact (SYM (@lem3085914 m n h1)). Qed.
Lemma lem3085916 (m : nat) (n : nat) (h1 : num_divides m n) : num_divides m n.
Proof. exact (EQ_MP (@lem3085915 m n h1) (@lem0)). Qed.
Lemma lem3085917 (m : nat) (n : nat) (h1 : num_divides m n) : (term51 m n) = True.
Proof. exact (@lem3085912 m n (@lem3085916 m n h1)). Qed.
Lemma lem3085918 (m : nat) (n : nat) (h1 : term2 m) (h2 : num_divides m n) : (term9 m n) = True.
Proof. exact (TRANS (@lem3085910 n m h1) (@lem3085917 m n h2)). Qed.
Lemma lem3085919 (n : nat) (m : nat) (h1 : term2 m) : term61 m n.
Proof. exact (fun h0 : num_divides m n => @lem3085918 m n h1 h0). Qed.
Lemma lem3085920 (m : nat) (n : nat) : term62 m n.
Proof. exact (@lem3085757 m n True). Qed.
Lemma lem3085921 (n : nat) (m : nat) (h1 : term2 m) : (term31 m n) = (term63 m n).
Proof. exact (@lem3085920 m n (@lem3085919 n m h1)). Qed.
Lemma lem3085923 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3085924 (m : nat) (n : nat) : (term63 m n) = True.
Proof. exact (@lem3085923 (num_divides m n)). Qed.
Lemma lem3085925 (n : nat) (m : nat) (h1 : term2 m) : (term31 m n) = True.
Proof. exact (TRANS (@lem3085921 n m h1) (@lem3085924 m n)). Qed.
Lemma lem3085926 (n : nat) (m : nat) (h1 : term2 m) : True = (term31 m n).
Proof. exact (SYM (@lem3085925 n m h1)). Qed.
Lemma lem3085927 (n : nat) (m : nat) (h1 : term2 m) : term31 m n.
Proof. exact (EQ_MP (@lem3085926 n m h1) (@lem0)). Qed.
Lemma lem3085931 (b : nat) (a : nat) : (num_divides a b) = (term64 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3085932 (n : nat) : (term15 n) = (term65 n).
Proof. exact (@lem3085931 n (NUMERAL 0)). Qed.
Lemma lem3085939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3085940 (n : nat) : (term66 n) = (term67 n).
Proof. exact (MK_COMB (@lem3085939) (@lem3085932 n)). Qed.
Lemma lem3085945 (n : nat) : (term28 n) = (term28 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem3085946 (n : nat) : (term32 n) = (term68 n).
Proof. exact (MK_COMB (@lem3085940 n) (@lem3085945 n)). Qed.
Lemma lem3085949 (n : nat) : (term68 n) = (term32 n).
Proof. exact (SYM (@lem3085946 n)). Qed.
Lemma lem3085951 (p : Prop) : p = (term69 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3085952 (n : nat) : (term68 n) = (term70 n).
Proof. exact (@lem3085951 (term68 n)). Qed.
Lemma lem3085953 (n : nat) : (term70 n) = (term68 n).
Proof. exact (SYM (@lem3085952 n)). Qed.
Lemma lem3085954 (n : nat) (h1 : term71 n) : term71 n.
Proof. exact (h1). Qed.
Lemma lem3085957 (n : nat) (h1 : term72 n) : term72 n.
Proof. exact (h1). Qed.
Lemma lem3085958 (n : nat) : term73 n.
Proof. exact (fun h0 : term72 n => @lem3085957 n h0). Qed.
Lemma lem3085959 (n : nat) (h1 : term73 n) : term73 n.
Proof. exact (h1). Qed.
Lemma lem3085960 (n : nat) (h1 : term72 n) : term72 n.
Proof. exact (h1). Qed.
Lemma lem3085961 (n : nat) (h1 : term72 n) (h2 : term73 n) : term72 n.
Proof. exact (@lem3085959 n h2 (@lem3085960 n h1)). Qed.
Lemma lem3085962 (n : nat) (h1 : term72 n) : term74 n.
Proof. exact (fun h0 : term73 n => @lem3085961 n h1 h0). Qed.
Lemma lem3085963 (n : nat) (h1 : term73 n) : term73 n.
Proof. exact (h1). Qed.
Lemma lem3085964 (n : nat) (h1 : term72 n) (h2 : term73 n) : term72 n.
Proof. exact (@lem3085962 n h1 (@lem3085963 n h2)). Qed.
Lemma lem3085965 (n : nat) (h1 : term73 n) : term73 n.
Proof. exact (fun h0 : term72 n => @lem3085964 n h0 h1). Qed.
Lemma lem3085966 (n : nat) : term75 n.
Proof. exact (fun h0 : term73 n => @lem3085965 n h0). Qed.
Lemma lem3085969 (n : nat) : term73 n.
Proof. exact (@lem3085966 n (@lem3085958 n)). Qed.
Lemma lem3085985 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3085986 : term76 = term77.
Proof. exact (@lem3085985 term78). Qed.
Lemma lem3086029 (n : nat) : (term79 n) = (term79 n).
Proof. exact (eq_refl (term79 n)). Qed.
Lemma lem3086030 (n : nat) : (term72 n) = (term80 n).
Proof. exact (MK_COMB (@lem3086029 n) (@lem3085986)). Qed.
Lemma lem3086033 : term81 = term82.
Proof. exact (fun_ext (fun n : nat => @lem3086030 n)). Qed.
Lemma lem3086034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086043 : term83 = term84.
Proof. exact (MK_COMB (@lem3086034) (@lem3086033)). Qed.
Lemma lem3086044 (m : nat) (n : nat) : ((term85 m n) = (term86 m n)) = ((term85 m n) = (term86 m n)).
Proof. exact (eq_refl ((term85 m n) = (term86 m n))). Qed.
Lemma lem3086045 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem3086044 m n)). Qed.
Lemma lem3086046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086047 (m : nat) : (term88 m) = (term88 m).
Proof. exact (MK_COMB (@lem3086046) (@lem3086045 m)). Qed.
Lemma lem3086048 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem3086047 m)). Qed.
Lemma lem3086049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086050 : term90 = term90.
Proof. exact (MK_COMB (@lem3086049) (@lem3086048)). Qed.
Lemma lem3086051 (m : nat) (n : nat) : ((term91 m n) = (term92 m n)) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl ((term91 m n) = (term92 m n))). Qed.
Lemma lem3086052 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem3086051 m n)). Qed.
Lemma lem3086053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086054 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem3086053) (@lem3086052 m)). Qed.
Lemma lem3086055 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem3086054 m)). Qed.
Lemma lem3086056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086057 : term96 = term96.
Proof. exact (MK_COMB (@lem3086056) (@lem3086055)). Qed.
Lemma lem3086058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086059 : term97 = term97.
Proof. exact (MK_COMB (@lem3086058) (@lem3086057)). Qed.
Lemma lem3086060 : term98 = term98.
Proof. exact (MK_COMB (@lem3086059) (@lem3086050)). Qed.
Lemma lem3086061 (m : nat) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem3086062 : term100 = term100.
Proof. exact (fun_ext (fun m : nat => @lem3086061 m)). Qed.
Lemma lem3086063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086064 : term101 = term101.
Proof. exact (MK_COMB (@lem3086063) (@lem3086062)). Qed.
Lemma lem3086065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086066 : term102 = term102.
Proof. exact (MK_COMB (@lem3086065) (@lem3086064)). Qed.
Lemma lem3086067 : term103 = term103.
Proof. exact (MK_COMB (@lem3086066) (@lem3086060)). Qed.
Lemma lem3086068 (n : nat) : ((term104 n) = n) = ((term104 n) = n).
Proof. exact (eq_refl ((term104 n) = n)). Qed.
Lemma lem3086069 : term105 = term105.
Proof. exact (fun_ext (fun n : nat => @lem3086068 n)). Qed.
Lemma lem3086070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086071 : term106 = term106.
Proof. exact (MK_COMB (@lem3086070) (@lem3086069)). Qed.
Lemma lem3086072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086073 : term107 = term107.
Proof. exact (MK_COMB (@lem3086072) (@lem3086071)). Qed.
Lemma lem3086074 : term108 = term108.
Proof. exact (MK_COMB (@lem3086073) (@lem3086067)). Qed.
Lemma lem3086075 (m : nat) : ((term109 m) = (NUMERAL 0)) = ((term109 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term109 m) = (NUMERAL 0))). Qed.
Lemma lem3086076 : term110 = term110.
Proof. exact (fun_ext (fun m : nat => @lem3086075 m)). Qed.
Lemma lem3086077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086078 : term111 = term111.
Proof. exact (MK_COMB (@lem3086077) (@lem3086076)). Qed.
Lemma lem3086079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086080 : term112 = term112.
Proof. exact (MK_COMB (@lem3086079) (@lem3086078)). Qed.
Lemma lem3086081 : term113 = term113.
Proof. exact (MK_COMB (@lem3086080) (@lem3086074)). Qed.
Lemma lem3086082 (n : nat) : ((term114 n) = (NUMERAL 0)) = ((term114 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term114 n) = (NUMERAL 0))). Qed.
Lemma lem3086083 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem3086082 n)). Qed.
Lemma lem3086084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086085 : term116 = term116.
Proof. exact (MK_COMB (@lem3086084) (@lem3086083)). Qed.
Lemma lem3086086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086087 : term117 = term117.
Proof. exact (MK_COMB (@lem3086086) (@lem3086085)). Qed.
Lemma lem3086088 : term78 = term78.
Proof. exact (MK_COMB (@lem3086087) (@lem3086081)). Qed.
Lemma lem3086089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3086090 : term77 = term77.
Proof. exact (MK_COMB (@lem3086089) (@lem3086088)). Qed.
Lemma lem3086095 (n : nat) : (term28 n) = (term28 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem3086096 (n : nat) (x : nat) : (n = (term114 x)) = (n = (term114 x)).
Proof. exact (eq_refl (n = (term114 x))). Qed.
Lemma lem3086097 (n : nat) : (term118 n) = (term118 n).
Proof. exact (fun_ext (fun x : nat => @lem3086096 n x)). Qed.
Lemma lem3086098 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3086099 (n : nat) : (term65 n) = (term65 n).
Proof. exact (MK_COMB (@lem3086098) (@lem3086097 n)). Qed.
Lemma lem3086100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3086101 (n : nat) : (term67 n) = (term67 n).
Proof. exact (MK_COMB (@lem3086100) (@lem3086099 n)). Qed.
Lemma lem3086102 (n : nat) : (term68 n) = (term68 n).
Proof. exact (MK_COMB (@lem3086101 n) (@lem3086095 n)). Qed.
Lemma lem3086103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3086104 (n : nat) : (term71 n) = (term71 n).
Proof. exact (MK_COMB (@lem3086103) (@lem3086102 n)). Qed.
Lemma lem3086105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3086106 (n : nat) : (term79 n) = (term79 n).
Proof. exact (MK_COMB (@lem3086105) (@lem3086104 n)). Qed.
Lemma lem3086107 (n : nat) : (term80 n) = (term80 n).
Proof. exact (MK_COMB (@lem3086106 n) (@lem3086090)). Qed.
Lemma lem3086108 : term82 = term82.
Proof. exact (fun_ext (fun n : nat => @lem3086107 n)). Qed.
Lemma lem3086109 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086110 : term84 = term84.
Proof. exact (MK_COMB (@lem3086109) (@lem3086108)). Qed.
Lemma lem3086189 : term83 = term84.
Proof. exact (TRANS (@lem3086043) (@lem3086110)). Qed.
Lemma lem3086190 : term84 = term83.
Proof. exact (SYM (@lem3086189)). Qed.
Lemma lem3086191 (n : nat) (h1 : term71 n) : term71 n.
Proof. exact (h1). Qed.
Lemma lem3086192 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem3086193 (n : nat) (x : nat) : (n = (term114 x)) = (n = (term114 x)).
Proof. exact (eq_refl (n = (term114 x))). Qed.
Lemma lem3086194 (n : nat) : (term118 n) = (term118 n).
Proof. exact (fun_ext (fun x : nat => @lem3086193 n x)). Qed.
Lemma lem3086195 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3086196 (n : nat) : (term65 n) = (term65 n).
Proof. exact (MK_COMB (@lem3086195) (@lem3086194 n)). Qed.
Lemma lem3086203 (n : nat) : (term119 n) = (term120 n).
Proof. exact (@lem17160 term20 (n = (NUMERAL 0))). Qed.
Lemma lem3086204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086205 (n : nat) : (term121 n) = (term121 n).
Proof. exact (MK_COMB (@lem3086204) (@lem3086196 n)). Qed.
Lemma lem3086206 (n : nat) : (term122 n) = (term123 n).
Proof. exact (MK_COMB (@lem3086205 n) (@lem3086203 n)). Qed.
Lemma lem3086207 (n : nat) : (term71 n) = (term122 n).
Proof. exact (@lem17362 (term65 n) (term28 n)). Qed.
Lemma lem3086208 (n : nat) : (term71 n) = (term123 n).
Proof. exact (TRANS (@lem3086207 n) (@lem3086206 n)). Qed.
Lemma lem3086215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3086216 (P : nat -> Prop) (Q : Prop) : (term126 P Q) = (term127 P Q).
Proof. exact (@lem3086215 nat P Q). Qed.
Lemma lem3086217 (n : nat) : (term128 n) = (term129 n).
Proof. exact (@lem3086216 (term118 n) (term120 n)). Qed.
Lemma lem3086218 (n : nat) (x : nat) : (term130 n x) = (n = (term114 x)).
Proof. exact (eq_refl (term130 n x)). Qed.
Lemma lem3086219 (n : nat) : (term131 n) = (term118 n).
Proof. exact (fun_ext (fun x : nat => @lem3086218 n x)). Qed.
Lemma lem3086220 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3086221 (n : nat) : (term132 n) = (term65 n).
Proof. exact (MK_COMB (@lem3086220) (@lem3086219 n)). Qed.
Lemma lem3086222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086223 (n : nat) : (term133 n) = (term121 n).
Proof. exact (MK_COMB (@lem3086222) (@lem3086221 n)). Qed.
Lemma lem3086224 (n : nat) : (term120 n) = (term120 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem3086225 (n : nat) : (term128 n) = (term123 n).
Proof. exact (MK_COMB (@lem3086223 n) (@lem3086224 n)). Qed.
Lemma lem3086226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3086227 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem3086226) (@lem3086225 n)). Qed.
Lemma lem3086228 (n : nat) (x : nat) : (term130 n x) = (n = (term114 x)).
Proof. exact (eq_refl (term130 n x)). Qed.
Lemma lem3086229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086230 (n : nat) (x : nat) : (term136 n x) = (term137 n x).
Proof. exact (MK_COMB (@lem3086229) (@lem3086228 n x)). Qed.
Lemma lem3086231 (n : nat) : (term120 n) = (term120 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem3086232 (x : nat) (n : nat) : (term138 x n) = (term139 x n).
Proof. exact (MK_COMB (@lem3086230 n x) (@lem3086231 n)). Qed.
Lemma lem3086233 (n : nat) : (term140 n) = (term141 n).
Proof. exact (fun_ext (fun x : nat => @lem3086232 x n)). Qed.
Lemma lem3086234 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3086235 (n : nat) : (term129 n) = (term142 n).
Proof. exact (MK_COMB (@lem3086234) (@lem3086233 n)). Qed.
Lemma lem3086236 (n : nat) : ((term128 n) = (term129 n)) = ((term123 n) = (term142 n)).
Proof. exact (MK_COMB (@lem3086227 n) (@lem3086235 n)). Qed.
Lemma lem3086238 (n : nat) : (term123 n) = (term142 n).
Proof. exact (EQ_MP (@lem3086236 n) (@lem3086217 n)). Qed.
Lemma lem3086239 (n : nat) : (term71 n) = (term142 n).
Proof. exact (TRANS (@lem3086208 n) (@lem3086238 n)). Qed.
Lemma lem3086240 (n : nat) (h1 : term71 n) : term142 n.
Proof. exact (EQ_MP (@lem3086239 n) (@lem3086191 n h1)). Qed.
Lemma lem3086241 (n : nat) : ((term114 n) = (NUMERAL 0)) = ((term114 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term114 n) = (NUMERAL 0))). Qed.
Lemma lem3086242 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem3086241 n)). Qed.
Lemma lem3086243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086244 : term116 = term116.
Proof. exact (MK_COMB (@lem3086243) (@lem3086242)). Qed.
Lemma lem3086245 (m : nat) : ((term109 m) = (NUMERAL 0)) = ((term109 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term109 m) = (NUMERAL 0))). Qed.
Lemma lem3086246 : term110 = term110.
Proof. exact (fun_ext (fun m : nat => @lem3086245 m)). Qed.
Lemma lem3086247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086248 : term111 = term111.
Proof. exact (MK_COMB (@lem3086247) (@lem3086246)). Qed.
Lemma lem3086249 (n : nat) : ((term104 n) = n) = ((term104 n) = n).
Proof. exact (eq_refl ((term104 n) = n)). Qed.
Lemma lem3086250 : term105 = term105.
Proof. exact (fun_ext (fun n : nat => @lem3086249 n)). Qed.
Lemma lem3086251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086252 : term106 = term106.
Proof. exact (MK_COMB (@lem3086251) (@lem3086250)). Qed.
Lemma lem3086253 (m : nat) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem3086254 : term100 = term100.
Proof. exact (fun_ext (fun m : nat => @lem3086253 m)). Qed.
Lemma lem3086255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086256 : term101 = term101.
Proof. exact (MK_COMB (@lem3086255) (@lem3086254)). Qed.
Lemma lem3086257 (m : nat) (n : nat) : ((term91 m n) = (term92 m n)) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl ((term91 m n) = (term92 m n))). Qed.
Lemma lem3086258 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem3086257 m n)). Qed.
Lemma lem3086259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086260 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem3086259) (@lem3086258 m)). Qed.
Lemma lem3086261 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem3086260 m)). Qed.
Lemma lem3086262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086263 : term96 = term96.
Proof. exact (MK_COMB (@lem3086262) (@lem3086261)). Qed.
Lemma lem3086264 (m : nat) (n : nat) : ((term85 m n) = (term86 m n)) = ((term85 m n) = (term86 m n)).
Proof. exact (eq_refl ((term85 m n) = (term86 m n))). Qed.
Lemma lem3086265 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem3086264 m n)). Qed.
Lemma lem3086266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086267 (m : nat) : (term88 m) = (term88 m).
Proof. exact (MK_COMB (@lem3086266) (@lem3086265 m)). Qed.
Lemma lem3086268 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem3086267 m)). Qed.
Lemma lem3086269 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086270 : term90 = term90.
Proof. exact (MK_COMB (@lem3086269) (@lem3086268)). Qed.
Lemma lem3086271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086272 : term97 = term97.
Proof. exact (MK_COMB (@lem3086271) (@lem3086263)). Qed.
Lemma lem3086273 : term98 = term98.
Proof. exact (MK_COMB (@lem3086272) (@lem3086270)). Qed.
Lemma lem3086274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086275 : term102 = term102.
Proof. exact (MK_COMB (@lem3086274) (@lem3086256)). Qed.
Lemma lem3086276 : term103 = term103.
Proof. exact (MK_COMB (@lem3086275) (@lem3086273)). Qed.
Lemma lem3086277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086278 : term107 = term107.
Proof. exact (MK_COMB (@lem3086277) (@lem3086252)). Qed.
Lemma lem3086279 : term108 = term108.
Proof. exact (MK_COMB (@lem3086278) (@lem3086276)). Qed.
Lemma lem3086280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086281 : term112 = term112.
Proof. exact (MK_COMB (@lem3086280) (@lem3086248)). Qed.
Lemma lem3086282 : term113 = term113.
Proof. exact (MK_COMB (@lem3086281) (@lem3086279)). Qed.
Lemma lem3086283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086284 : term117 = term117.
Proof. exact (MK_COMB (@lem3086283) (@lem3086244)). Qed.
Lemma lem3086321 : term78 = term78.
Proof. exact (MK_COMB (@lem3086284) (@lem3086282)). Qed.
Lemma lem3086322 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem3086321) (@lem3086192 h1)). Qed.
Lemma lem3086342 (m : nat) (n : nat) : ((term85 m n) = (term86 m n)) = ((term85 m n) = (term86 m n)).
Proof. exact (eq_refl ((term85 m n) = (term86 m n))). Qed.
Lemma lem3086343 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem3086342 m n)). Qed.
Lemma lem3086344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086345 (m : nat) : (term88 m) = (term88 m).
Proof. exact (MK_COMB (@lem3086344) (@lem3086343 m)). Qed.
Lemma lem3086346 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem3086345 m)). Qed.
Lemma lem3086347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086348 : term90 = term90.
Proof. exact (MK_COMB (@lem3086347) (@lem3086346)). Qed.
Lemma lem3086367 (m : nat) (n : nat) : ((term91 m n) = (term92 m n)) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl ((term91 m n) = (term92 m n))). Qed.
Lemma lem3086368 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem3086367 m n)). Qed.
Lemma lem3086369 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086370 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem3086369) (@lem3086368 m)). Qed.
Lemma lem3086371 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem3086370 m)). Qed.
Lemma lem3086372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086373 : term96 = term96.
Proof. exact (MK_COMB (@lem3086372) (@lem3086371)). Qed.
Lemma lem3086374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086375 : term97 = term97.
Proof. exact (MK_COMB (@lem3086374) (@lem3086373)). Qed.
Lemma lem3086376 : term98 = term98.
Proof. exact (MK_COMB (@lem3086375) (@lem3086348)). Qed.
Lemma lem3086389 (m : nat) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem3086390 : term100 = term100.
Proof. exact (fun_ext (fun m : nat => @lem3086389 m)). Qed.
Lemma lem3086391 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086392 : term101 = term101.
Proof. exact (MK_COMB (@lem3086391) (@lem3086390)). Qed.
Lemma lem3086393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086394 : term102 = term102.
Proof. exact (MK_COMB (@lem3086393) (@lem3086392)). Qed.
Lemma lem3086395 : term103 = term103.
Proof. exact (MK_COMB (@lem3086394) (@lem3086376)). Qed.
Lemma lem3086408 (n : nat) : ((term104 n) = n) = ((term104 n) = n).
Proof. exact (eq_refl ((term104 n) = n)). Qed.
Lemma lem3086409 : term105 = term105.
Proof. exact (fun_ext (fun n : nat => @lem3086408 n)). Qed.
Lemma lem3086410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086411 : term106 = term106.
Proof. exact (MK_COMB (@lem3086410) (@lem3086409)). Qed.
Lemma lem3086412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086413 : term107 = term107.
Proof. exact (MK_COMB (@lem3086412) (@lem3086411)). Qed.
Lemma lem3086414 : term108 = term108.
Proof. exact (MK_COMB (@lem3086413) (@lem3086395)). Qed.
Lemma lem3086427 (m : nat) : ((term109 m) = (NUMERAL 0)) = ((term109 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term109 m) = (NUMERAL 0))). Qed.
Lemma lem3086428 : term110 = term110.
Proof. exact (fun_ext (fun m : nat => @lem3086427 m)). Qed.
Lemma lem3086429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086430 : term111 = term111.
Proof. exact (MK_COMB (@lem3086429) (@lem3086428)). Qed.
Lemma lem3086431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086432 : term112 = term112.
Proof. exact (MK_COMB (@lem3086431) (@lem3086430)). Qed.
Lemma lem3086433 : term113 = term113.
Proof. exact (MK_COMB (@lem3086432) (@lem3086414)). Qed.
Lemma lem3086446 (n : nat) : ((term114 n) = (NUMERAL 0)) = ((term114 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term114 n) = (NUMERAL 0))). Qed.
Lemma lem3086447 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem3086446 n)). Qed.
Lemma lem3086448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086449 : term116 = term116.
Proof. exact (MK_COMB (@lem3086448) (@lem3086447)). Qed.
Lemma lem3086450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3086451 : term117 = term117.
Proof. exact (MK_COMB (@lem3086450) (@lem3086449)). Qed.
Lemma lem3086452 : term78 = term78.
Proof. exact (MK_COMB (@lem3086451) (@lem3086433)). Qed.
Lemma lem3086453 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem3086452) (@lem3086322 h1)). Qed.
Lemma lem3086493 (x : nat) (n : nat) (h1 : term139 x n) : term139 x n.
Proof. exact (h1). Qed.
Lemma lem3086494 (x : nat) (n : nat) (h1 : term139 x n) : term120 n.
Proof. exact (proj2 (@lem3086493 x n h1)). Qed.
Lemma lem3086499 (h1 : term78) : term116.
Proof. exact (proj1 (@lem3086453 h1)). Qed.
Lemma lem3086521 (n : nat) : ((term114 n) = (NUMERAL 0)) = ((term114 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term114 n) = (NUMERAL 0))). Qed.
Lemma lem3086522 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem3086521 n)). Qed.
Lemma lem3086523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086525 : term116 = term116.
Proof. exact (MK_COMB (@lem3086523) (@lem3086522)). Qed.
Lemma lem3086526 (h1 : term78) : term116.
Proof. exact (EQ_MP (@lem3086525) (@lem3086499 h1)). Qed.
Lemma lem3086568 (_32065 : nat) (h1 : term78) : term143 _32065.
Proof. exact (@lem3086526 h1 _32065). Qed.
Lemma lem3086569 (_32065 : nat) : (term143 _32065) = ((term114 _32065) = (NUMERAL 0)).
Proof. exact (eq_refl (term143 _32065)). Qed.
Lemma lem3086593 (x : nat) (n : nat) (h1 : term139 x n) : n = (term114 x).
Proof. exact (proj1 (@lem3086493 x n h1)). Qed.
Lemma lem3086597 (x : nat) (n : nat) (h1 : term139 x n) : term2 n.
Proof. exact (proj2 (@lem3086494 x n h1)). Qed.
Lemma lem3086638 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem3086639 (x : nat) (n : nat) (h1 : term139 x n) : (term145 n) = (term146 x).
Proof. exact (MK_COMB (@lem3086638) (@lem3086593 x n h1)). Qed.
Lemma lem3086640 (x : nat) : (term146 x) = (term147 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem3086641 (n : nat) : (term148 n) = (term148 n).
Proof. exact (eq_refl (term148 n)). Qed.
Lemma lem3086642 (n : nat) (x : nat) : ((term145 n) = (term146 x)) = ((term145 n) = (term147 x)).
Proof. exact (MK_COMB (@lem3086641 n) (@lem3086640 x)). Qed.
Lemma lem3086643 (n : nat) : (term145 n) = (term2 n).
Proof. exact (eq_refl (term145 n)). Qed.
Lemma lem3086644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3086645 (n : nat) : (term148 n) = (term149 n).
Proof. exact (MK_COMB (@lem3086644) (@lem3086643 n)). Qed.
Lemma lem3086646 (x : nat) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem3086647 (n : nat) (x : nat) : ((term145 n) = (term147 x)) = ((term2 n) = (term147 x)).
Proof. exact (MK_COMB (@lem3086645 n) (@lem3086646 x)). Qed.
Lemma lem3086648 (n : nat) (x : nat) : ((term145 n) = (term146 x)) = ((term2 n) = (term147 x)).
Proof. exact (TRANS (@lem3086642 n x) (@lem3086647 n x)). Qed.
Lemma lem3086649 (x : nat) (n : nat) (h1 : term139 x n) : (term2 n) = (term147 x).
Proof. exact (EQ_MP (@lem3086648 n x) (@lem3086639 x n h1)). Qed.
Lemma lem3086650 (x : nat) (n : nat) (h1 : term139 x n) : term147 x.
Proof. exact (EQ_MP (@lem3086649 x n h1) (@lem3086597 x n h1)). Qed.
Lemma lem3086811 (_32065 : nat) (h1 : term78) : (term114 _32065) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3086569 _32065) (@lem3086568 _32065 h1)). Qed.
Lemma lem3086812 (x : nat) (h1 : term78) : (term114 x) = (NUMERAL 0).
Proof. exact (@lem3086811 x h1). Qed.
Lemma lem3086813 (x : nat) (h1 : term78) : term150 x.
Proof. exact (fun h0 : term147 x => @lem3086812 x h1). Qed.
Lemma lem3086815 (p : Prop) : (term151 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3086816 (x : nat) : (term150 x) = ((term114 x) = (NUMERAL 0)).
Proof. exact (@lem3086815 ((term114 x) = (NUMERAL 0))). Qed.
Lemma lem3086817 (x : nat) (h1 : term78) : (term114 x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3086816 x) (@lem3086813 x h1)). Qed.
Lemma lem3086820 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3086822 (x : nat) : (term147 x) = (term152 x).
Proof. exact (@lem3086820 ((term114 x) = (NUMERAL 0))). Qed.
Lemma lem3086825 (x : nat) (n : nat) (h1 : term139 x n) : term152 x.
Proof. exact (EQ_MP (@lem3086822 x) (@lem3086650 x n h1)). Qed.
Lemma lem3086828 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : False.
Proof. exact (@lem3086825 x n h2 (@lem3086817 x h1)). Qed.
Lemma lem3086829 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : term153.
Proof. exact (fun h0 : ~ False => @lem3086828 x n h1 h2). Qed.
Lemma lem3086831 (p : Prop) : (term151 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3086832 : term153 = False.
Proof. exact (@lem3086831 False). Qed.
Lemma lem3086834 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : False.
Proof. exact (EQ_MP (@lem3086832) (@lem3086829 x n h1 h2)). Qed.
Lemma lem3086835 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : (term139 x n) = False.
Proof. exact (prop_ext (fun h3 : term139 x n => @lem3086834 x n h1 h2) (fun h3 : False => @lem3086493 x n h2)). Qed.
Lemma lem3086836 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : False.
Proof. exact (EQ_MP (@lem3086835 x n h1 h2) (@lem3086493 x n h2)). Qed.
Lemma lem3086837 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : term78 = False.
Proof. exact (prop_ext (fun h3 : term78 => @lem3086836 x n h1 h2) (fun h3 : False => @lem3086453 h1)). Qed.
Lemma lem3086838 (x : nat) (n : nat) (h1 : term78) (h2 : term139 x n) : False.
Proof. exact (EQ_MP (@lem3086837 x n h1 h2) (@lem3086453 h1)). Qed.
Lemma lem3086839 (n : nat) (h1 : term71 n) (h2 : term78) : False.
Proof. exact (ex_elim (@lem3086240 n h1) (fun x : nat => fun h0 : term141 n x => @lem3086838 x n h2 h0)). Qed.
Lemma lem3086840 (n : nat) (h1 : term71 n) (h2 : term78) : term78 = False.
Proof. exact (prop_ext (fun h3 : term78 => @lem3086839 n h1 h2) (fun h3 : False => @lem3086322 h2)). Qed.
Lemma lem3086841 (n : nat) (h1 : term71 n) (h2 : term78) : False.
Proof. exact (EQ_MP (@lem3086840 n h1 h2) (@lem3086322 h2)). Qed.
Lemma lem3086842 (n : nat) (h1 : term71 n) : term76.
Proof. exact (fun h0 : term78 => @lem3086841 n h1 h0). Qed.
Lemma lem3086843 : term76 = term77.
Proof. exact (@lem69 term78). Qed.
Lemma lem3086844 (n : nat) (h1 : term71 n) : term77.
Proof. exact (EQ_MP (@lem3086843) (@lem3086842 n h1)). Qed.
Lemma lem3086845 (n : nat) : term80 n.
Proof. exact (fun h0 : term71 n => @lem3086844 n h0). Qed.
Lemma lem3086850 : term84.
Proof. exact (fun n : nat => @lem3086845 n). Qed.
Lemma lem3086851 : term83.
Proof. exact (EQ_MP (@lem3086190) (@lem3086850)). Qed.
Lemma lem3086852 (n : nat) : term154 n.
Proof. exact (@lem3086851 n). Qed.
Lemma lem3086853 (n : nat) : (term154 n) = (term72 n).
Proof. exact (eq_refl (term154 n)). Qed.
Lemma lem3086854 (n : nat) : term72 n.
Proof. exact (EQ_MP (@lem3086853 n) (@lem3086852 n)). Qed.
Lemma lem3086856 (n : nat) : term72 n.
Proof. exact (@lem3085969 n (@lem3086854 n)). Qed.
Lemma lem3086857 (n : nat) (h1 : term71 n) : term76.
Proof. exact (@lem3086856 n (@lem3085954 n h1)). Qed.
Lemma lem3086858 (n : nat) (h1 : term71 n) : False.
Proof. exact (@lem3086857 n h1 (@lem81645)). Qed.
Lemma lem3086859 (n : nat) (h1 : term71 n) : (term71 n) = False.
Proof. exact (prop_ext (fun h2 : term71 n => @lem3086858 n h1) (fun h2 : False => @lem3085954 n h1)). Qed.
Lemma lem3086860 (n : nat) (h1 : term71 n) : False.
Proof. exact (EQ_MP (@lem3086859 n h1) (@lem3085954 n h1)). Qed.
Lemma lem3086861 (n : nat) : term70 n.
Proof. exact (fun h0 : term71 n => @lem3086860 n h0). Qed.
Lemma lem3086862 (n : nat) : term68 n.
Proof. exact (EQ_MP (@lem3085953 n) (@lem3086861 n)). Qed.
Lemma lem3086863 (n : nat) : term32 n.
Proof. exact (EQ_MP (@lem3085949 n) (@lem3086862 n)). Qed.
Lemma lem3086864 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term31 m n.
Proof. exact (EQ_MP (@lem3085594 n m h1) (@lem3086863 n)). Qed.
Lemma lem3086865 (m : nat) (n : nat) : term31 m n.
Proof. exact (or_elim (@lem3082305 m) (fun h0 : m = (NUMERAL 0) => @lem3086864 n m h0) (fun h0 : term2 m => @lem3085927 n m h0)). Qed.
Lemma lem3086870 (m : nat) : term155 m.
Proof. exact (fun n : nat => @lem3086865 m n). Qed.
Lemma lem3086875 : term156.
Proof. exact (fun m : nat => @lem3086870 m). Qed.
