Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LCANCEL_IMP_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_EQ_MUL_LCANCEL_spec.
Require Import REAL_LE_LT_spec.
Require Import REAL_LT_LCANCEL_IMP_spec.
Require Import REAL_LT_REFL_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1598630 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1598631 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1598630 h1 x). Qed.
Lemma lem1598632 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1598633 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1598632 x) (@lem1598631 x h1)). Qed.
Lemma lem1598634 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1598633 x h1 y). Qed.
Lemma lem1598635 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1598636 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1598635 x y) (@lem1598634 x y h1)). Qed.
Lemma lem1598637 (x : real) (y : real) (z : real) (h1 : term0) : term5 x y z.
Proof. exact (@lem1598636 x y h1 z). Qed.
Lemma lem1598638 (x : real) (y : real) (z : real) : (term5 x y z) = (term6 x y z).
Proof. exact (eq_refl (term5 x y z)). Qed.
Lemma lem1598639 (x : real) (y : real) (z : real) (h1 : term0) : term6 x y z.
Proof. exact (EQ_MP (@lem1598638 x y z) (@lem1598637 x y z h1)). Qed.
Lemma lem1598640 (y : real) (x : real) (z : real) (h1 : term7 y x z) : term7 y x z.
Proof. exact (h1). Qed.
Lemma lem1598641 (y : real) (x : real) (z : real) (h1 : term0) (h2 : term7 y x z) : real_lt y z.
Proof. exact (@lem1598639 x y z h1 (@lem1598640 y x z h2)). Qed.
Lemma lem1598642 (y : real) (x : real) (z : real) (h1 : term7 y x z) : term8 y z.
Proof. exact (fun h0 : term0 => @lem1598641 y x z h0 h1). Qed.
Lemma lem1598643 (y : real) (z : real) (h1 : term9 y z) : term9 y z.
Proof. exact (h1). Qed.
Lemma lem1598644 (y : real) (z : real) (h1 : term9 y z) : term8 y z.
Proof. exact (ex_elim (@lem1598643 y z h1) (fun x : real => fun h0 : term10 y z x => @lem1598642 y x z h0)). Qed.
Lemma lem1598645 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1598646 (y : real) (z : real) (h1 : term0) (h2 : term9 y z) : real_lt y z.
Proof. exact (@lem1598644 y z h2 (@lem1598645 h1)). Qed.
Lemma lem1598647 (y : real) (z : real) (h1 : term0) : term11 y z.
Proof. exact (fun h0 : term9 y z => @lem1598646 y z h1 h0). Qed.
Lemma lem1598648 (y : real) (h1 : term0) : term12 y.
Proof. exact (fun z : real => @lem1598647 y z h1). Qed.
Lemma lem1598649 (h1 : term0) : term13.
Proof. exact (fun y : real => @lem1598648 y h1). Qed.
Lemma lem1598650 : term14.
Proof. exact (fun h0 : term0 => @lem1598649 h0). Qed.
Lemma lem1598651 : term13.
Proof. exact (@lem1598650 (@lem1598529)). Qed.
Lemma lem1598652 (y : real) : term15 y.
Proof. exact (@lem1598651 y). Qed.
Lemma lem1598653 (y : real) : (term15 y) = (term12 y).
Proof. exact (eq_refl (term15 y)). Qed.
Lemma lem1598654 (y : real) : term12 y.
Proof. exact (EQ_MP (@lem1598653 y) (@lem1598652 y)). Qed.
Lemma lem1598655 (y : real) (z : real) : term16 y z.
Proof. exact (@lem1598654 y z). Qed.
Lemma lem1598656 (y : real) (z : real) : (term16 y z) = (term11 y z).
Proof. exact (eq_refl (term16 y z)). Qed.
Lemma lem1598658 (x : real) : term17 x.
Proof. exact (@lem9784 (x = term18)). Qed.
Lemma lem1598659 (x : real) : (term17 x) = (term19 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1598660 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1598659 x) (@lem1598658 x)). Qed.
Lemma lem1598662 (x : real) (h1 : term20 x) : term20 x.
Proof. exact (h1). Qed.
Lemma lem1598663 (x : real) : term21 x.
Proof. exact (@lem1586590 x). Qed.
Lemma lem1598664 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1598665 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1598664 x) (@lem1598663 x)). Qed.
Lemma lem1598666 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1598665 x y). Qed.
Lemma lem1598667 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1598668 (x : real) (y : real) : term24 x y.
Proof. exact (EQ_MP (@lem1598667 x y) (@lem1598666 x y)). Qed.
Lemma lem1598669 (x : real) (y : real) (z : real) : term25 x y z.
Proof. exact (@lem1598668 x y z). Qed.
Lemma lem1598670 (x : real) (y : real) (z : real) : (term25 x y z) = (((real_mul x y) = (real_mul x z)) = (term26 x y z)).
Proof. exact (eq_refl (term25 x y z)). Qed.
Lemma lem1598672 (x : real) : term27 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1598673 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1598674 (x : real) : term28 x.
Proof. exact (EQ_MP (@lem1598673 x) (@lem1598672 x)). Qed.
Lemma lem1598675 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1598674 x y). Qed.
Lemma lem1598676 (x : real) (y : real) : (term29 x y) = ((real_le x y) = (term30 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1598683 (x : real) (y : real) : (real_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem1598676 x y) (@lem1598675 x y)). Qed.
Lemma lem1598684 (y : real) (x : real) (z : real) : (term31 y x z) = (term32 y x z).
Proof. exact (@lem1598683 (real_mul x y) (real_mul x z)). Qed.
Lemma lem1598688 (x : real) (y : real) (z : real) : ((real_mul x y) = (real_mul x z)) = (term26 x y z).
Proof. exact (EQ_MP (@lem1598670 x y z) (@lem1598669 x y z)). Qed.
Lemma lem1598695 (y : real) (x : real) (z : real) : (term33 y x z) = (term33 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1598696 (x : real) (y : real) (z : real) : (term32 y x z) = (term34 x y z).
Proof. exact (MK_COMB (@lem1598695 y x z) (@lem1598688 x y z)). Qed.
Lemma lem1598699 (x : real) (y : real) (z : real) : (term31 y x z) = (term34 x y z).
Proof. exact (TRANS (@lem1598684 y x z) (@lem1598696 x y z)). Qed.
Lemma lem1598700 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1598701 (x : real) (y : real) (z : real) : (term36 y x z) = (term37 x y z).
Proof. exact (MK_COMB (@lem1598700 x) (@lem1598699 x y z)). Qed.
Lemma lem1598704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598705 (x : real) (y : real) (z : real) : (term38 y x z) = (term39 x y z).
Proof. exact (MK_COMB (@lem1598704) (@lem1598701 x y z)). Qed.
Lemma lem1598707 (x : real) (y : real) : (real_le x y) = (term30 x y).
Proof. exact (EQ_MP (@lem1598676 x y) (@lem1598675 x y)). Qed.
Lemma lem1598708 (y : real) (z : real) : (real_le y z) = (term30 y z).
Proof. exact (@lem1598707 y z). Qed.
Lemma lem1598713 (x : real) (y : real) (z : real) : (term40 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem1598705 x y z) (@lem1598708 y z)). Qed.
Lemma lem1598716 (x : real) (y : real) (z : real) : (term41 x y z) = (term40 x y z).
Proof. exact (SYM (@lem1598713 x y z)). Qed.
Lemma lem1598717 (x : real) : term42 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1598718 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1598719 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1598718 x) (@lem1598717 x)). Qed.
Lemma lem1598720 (x : real) : term44 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1598729 (x : real) (h1 : x = term18) : x = term18.
Proof. exact (h1). Qed.
Lemma lem1598730 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1598731 (x : real) (h1 : x = term18) : (term46 x) = term47.
Proof. exact (MK_COMB (@lem1598730) (@lem1598729 x h1)). Qed.
Lemma lem1598733 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1598720 x (@lem1598719 x)). Qed.
Lemma lem1598734 : term47 = False.
Proof. exact (@lem1598733 term18). Qed.
Lemma lem1598735 (x : real) (h1 : x = term18) : (term46 x) = False.
Proof. exact (TRANS (@lem1598731 x h1) (@lem1598734)). Qed.
Lemma lem1598736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1598737 (x : real) (h1 : x = term18) : (term35 x) = (and False).
Proof. exact (MK_COMB (@lem1598736) (@lem1598735 x h1)). Qed.
Lemma lem1598743 (x : real) (h1 : x = term18) : x = term18.
Proof. exact (h1). Qed.
Lemma lem1598744 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1598745 (x : real) (h1 : x = term18) : (real_mul x) = term48.
Proof. exact (MK_COMB (@lem1598744) (@lem1598743 x h1)). Qed.
Lemma lem1598746 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1598747 (y : real) (x : real) (h1 : x = term18) : (real_mul x y) = (term49 y).
Proof. exact (MK_COMB (@lem1598745 x h1) (@lem1598746 y)). Qed.
Lemma lem1598748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1598749 (y : real) (x : real) (h1 : x = term18) : (term50 x y) = (term51 y).
Proof. exact (MK_COMB (@lem1598748) (@lem1598747 y x h1)). Qed.
Lemma lem1598751 (x : real) (h1 : x = term18) : x = term18.
Proof. exact (h1). Qed.
Lemma lem1598752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1598753 (x : real) (h1 : x = term18) : (real_mul x) = term48.
Proof. exact (MK_COMB (@lem1598752) (@lem1598751 x h1)). Qed.
Lemma lem1598754 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1598755 (z : real) (x : real) (h1 : x = term18) : (real_mul x z) = (term49 z).
Proof. exact (MK_COMB (@lem1598753 x h1) (@lem1598754 z)). Qed.
Lemma lem1598756 (y : real) (z : real) (x : real) (h1 : x = term18) : (term52 y x z) = (term53 y z).
Proof. exact (MK_COMB (@lem1598749 y x h1) (@lem1598755 z x h1)). Qed.
Lemma lem1598759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1598760 (y : real) (z : real) (x : real) (h1 : x = term18) : (term33 y x z) = (term54 y z).
Proof. exact (MK_COMB (@lem1598759) (@lem1598756 y z x h1)). Qed.
Lemma lem1598766 (x : real) (h1 : x = term18) : x = term18.
Proof. exact (h1). Qed.
Lemma lem1598767 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1598768 (x : real) (h1 : x = term18) : (@eq real x) = term55.
Proof. exact (MK_COMB (@lem1598767) (@lem1598766 x h1)). Qed.
Lemma lem1598769 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1598770 (x : real) (h1 : x = term18) : (x = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1598768 x h1) (@lem1598769)). Qed.
Lemma lem1598772 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1598773 (x : real) : (x = x) = True.
Proof. exact (@lem1598772 real x). Qed.
Lemma lem1598774 : (term18 = term18) = True.
Proof. exact (@lem1598773 term18). Qed.
Lemma lem1598775 (x : real) (h1 : x = term18) : (x = term18) = True.
Proof. exact (TRANS (@lem1598770 x h1) (@lem1598774)). Qed.
Lemma lem1598776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1598777 (x : real) (h1 : x = term18) : (term56 x) = (or True).
Proof. exact (MK_COMB (@lem1598776) (@lem1598775 x h1)). Qed.
Lemma lem1598780 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1598781 (y : real) (z : real) (x : real) (h1 : x = term18) : (term26 x y z) = (term57 y z).
Proof. exact (MK_COMB (@lem1598777 x h1) (@lem1598780 y z)). Qed.
Lemma lem1598783 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1598784 (y : real) (z : real) : (term57 y z) = True.
Proof. exact (@lem1598783 (y = z)). Qed.
Lemma lem1598785 (y : real) (z : real) (x : real) (h1 : x = term18) : (term26 x y z) = True.
Proof. exact (TRANS (@lem1598781 y z x h1) (@lem1598784 y z)). Qed.
Lemma lem1598786 (y : real) (z : real) (x : real) (h1 : x = term18) : (term34 x y z) = (term58 y z).
Proof. exact (MK_COMB (@lem1598760 y z x h1) (@lem1598785 y z x h1)). Qed.
Lemma lem1598788 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1598789 (y : real) (z : real) : (term58 y z) = True.
Proof. exact (@lem1598788 (term53 y z)). Qed.
Lemma lem1598790 (y : real) (z : real) (x : real) (h1 : x = term18) : (term34 x y z) = True.
Proof. exact (TRANS (@lem1598786 y z x h1) (@lem1598789 y z)). Qed.
Lemma lem1598791 (y : real) (z : real) (x : real) (h1 : x = term18) : (term37 x y z) = (False /\ True).
Proof. exact (MK_COMB (@lem1598737 x h1) (@lem1598790 y z x h1)). Qed.
Lemma lem1598793 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1598794 : (False /\ True) = False.
Proof. exact (@lem1598793 True). Qed.
Lemma lem1598795 (y : real) (z : real) (x : real) (h1 : x = term18) : (term37 x y z) = False.
Proof. exact (TRANS (@lem1598791 y z x h1) (@lem1598794)). Qed.
Lemma lem1598796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598797 (y : real) (z : real) (x : real) (h1 : x = term18) : (term39 x y z) = (imp False).
Proof. exact (MK_COMB (@lem1598796) (@lem1598795 y z x h1)). Qed.
Lemma lem1598804 (y : real) (z : real) : (term30 y z) = (term30 y z).
Proof. exact (eq_refl (term30 y z)). Qed.
Lemma lem1598805 (y : real) (z : real) (x : real) (h1 : x = term18) : (term41 x y z) = (term59 y z).
Proof. exact (MK_COMB (@lem1598797 y z x h1) (@lem1598804 y z)). Qed.
Lemma lem1598807 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1598808 (y : real) (z : real) : (term59 y z) = True.
Proof. exact (@lem1598807 (term30 y z)). Qed.
Lemma lem1598809 (y : real) (z : real) (x : real) (h1 : x = term18) : (term41 x y z) = True.
Proof. exact (TRANS (@lem1598805 y z x h1) (@lem1598808 y z)). Qed.
Lemma lem1598810 (y : real) (z : real) (x : real) (h1 : x = term18) : True = (term41 x y z).
Proof. exact (SYM (@lem1598809 y z x h1)). Qed.
Lemma lem1598811 (y : real) (z : real) (x : real) (h1 : x = term18) : term41 x y z.
Proof. exact (EQ_MP (@lem1598810 y z x h1) (@lem0)). Qed.
Lemma lem1598817 (x : real) : term60 x.
Proof. exact (@lem82 (x = term18)). Qed.
Lemma lem1598843 (x : real) (h1 : term20 x) : (x = term18) = False.
Proof. exact (@lem1598817 x (@lem1598662 x h1)). Qed.
Lemma lem1598844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1598845 (x : real) (h1 : term20 x) : (term56 x) = (or False).
Proof. exact (MK_COMB (@lem1598844) (@lem1598843 x h1)). Qed.
Lemma lem1598848 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1598849 (y : real) (z : real) (x : real) (h1 : term20 x) : (term26 x y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1598845 x h1) (@lem1598848 y z)). Qed.
Lemma lem1598851 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1598852 (y : real) (z : real) : (term61 y z) = (y = z).
Proof. exact (@lem1598851 (y = z)). Qed.
Lemma lem1598855 (y : real) (z : real) (x : real) (h1 : term20 x) : (term26 x y z) = (y = z).
Proof. exact (TRANS (@lem1598849 y z x h1) (@lem1598852 y z)). Qed.
Lemma lem1598856 (y : real) (x : real) (z : real) : (term33 y x z) = (term33 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1598857 (y : real) (z : real) (x : real) (h1 : term20 x) : (term34 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1598856 y x z) (@lem1598855 y z x h1)). Qed.
Lemma lem1598860 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1598861 (y : real) (z : real) (x : real) (h1 : term20 x) : (term37 x y z) = (term63 x y z).
Proof. exact (MK_COMB (@lem1598860 x) (@lem1598857 y z x h1)). Qed.
Lemma lem1598864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598865 (y : real) (z : real) (x : real) (h1 : term20 x) : (term39 x y z) = (term64 x y z).
Proof. exact (MK_COMB (@lem1598864) (@lem1598861 y z x h1)). Qed.
Lemma lem1598872 (y : real) (z : real) : (term30 y z) = (term30 y z).
Proof. exact (eq_refl (term30 y z)). Qed.
Lemma lem1598873 (y : real) (z : real) (x : real) (h1 : term20 x) : (term41 x y z) = (term65 x y z).
Proof. exact (MK_COMB (@lem1598865 y z x h1) (@lem1598872 y z)). Qed.
Lemma lem1598876 (y : real) (z : real) (x : real) (h1 : term20 x) : (term65 x y z) = (term41 x y z).
Proof. exact (SYM (@lem1598873 y z x h1)). Qed.
Lemma lem1598877 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term63 x y z.
Proof. exact (h1). Qed.
Lemma lem1598878 (x : real) (y : real) (z : real) (h1 : term62 x y z) : term62 x y z.
Proof. exact (h1). Qed.
Lemma lem1598879 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term52 y x z.
Proof. exact (h1). Qed.
Lemma lem1598880 (y : real) (z : real) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem1598881 (x : real) (h1 : term46 x) : term46 x.
Proof. exact (h1). Qed.
Lemma lem1598923 (y : real) (z : real) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem1598924 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1598925 (y : real) (z : real) (h1 : y = z) : (real_lt y) = (real_lt z).
Proof. exact (MK_COMB (@lem1598924) (@lem1598923 y z h1)). Qed.
Lemma lem1598926 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1598927 (y : real) (z : real) (h1 : y = z) : (real_lt y z) = (real_lt z z).
Proof. exact (MK_COMB (@lem1598925 y z h1) (@lem1598926 z)). Qed.
Lemma lem1598928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1598929 (y : real) (z : real) (h1 : y = z) : (term66 y z) = (term67 z).
Proof. exact (MK_COMB (@lem1598928) (@lem1598927 y z h1)). Qed.
Lemma lem1598933 (y : real) (z : real) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem1598934 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1598935 (y : real) (z : real) (h1 : y = z) : (@eq real y) = (@eq real z).
Proof. exact (MK_COMB (@lem1598934) (@lem1598933 y z h1)). Qed.
Lemma lem1598936 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1598937 (y : real) (z : real) (h1 : y = z) : (y = z) = (z = z).
Proof. exact (MK_COMB (@lem1598935 y z h1) (@lem1598936 z)). Qed.
Lemma lem1598939 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1598940 (x : real) : (x = x) = True.
Proof. exact (@lem1598939 real x). Qed.
Lemma lem1598941 (z : real) : (z = z) = True.
Proof. exact (@lem1598940 z). Qed.
Lemma lem1598942 (y : real) (z : real) (h1 : y = z) : (y = z) = True.
Proof. exact (TRANS (@lem1598937 y z h1) (@lem1598941 z)). Qed.
Lemma lem1598943 (y : real) (z : real) (h1 : y = z) : (term30 y z) = (term68 z).
Proof. exact (MK_COMB (@lem1598929 y z h1) (@lem1598942 y z h1)). Qed.
Lemma lem1598945 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1598946 (z : real) : (term68 z) = True.
Proof. exact (@lem1598945 (real_lt z z)). Qed.
Lemma lem1598947 (y : real) (z : real) (h1 : y = z) : (term30 y z) = True.
Proof. exact (TRANS (@lem1598943 y z h1) (@lem1598946 z)). Qed.
Lemma lem1598948 (y : real) (z : real) (h1 : y = z) : True = (term30 y z).
Proof. exact (SYM (@lem1598947 y z h1)). Qed.
Lemma lem1598949 (y : real) (z : real) (h1 : y = z) : term30 y z.
Proof. exact (EQ_MP (@lem1598948 y z h1) (@lem0)). Qed.
Lemma lem1598951 (y : real) (z : real) : term11 y z.
Proof. exact (EQ_MP (@lem1598656 y z) (@lem1598655 y z)). Qed.
Lemma lem1598965 (x : real) : (term46 x) = ((term46 x) = True).
Proof. exact (@lem7 (term46 x)). Qed.
Lemma lem1598967 (y : real) (x : real) (z : real) : (term52 y x z) = ((term52 y x z) = True).
Proof. exact (@lem7 (term52 y x z)). Qed.
Lemma lem1598972 (x : real) (h1 : term46 x) : (term46 x) = True.
Proof. exact (EQ_MP (@lem1598965 x) (@lem1598881 x h1)). Qed.
Lemma lem1598973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1598974 (x : real) (h1 : term46 x) : (term35 x) = (and True).
Proof. exact (MK_COMB (@lem1598973) (@lem1598972 x h1)). Qed.
Lemma lem1598976 (y : real) (x : real) (z : real) (h1 : term52 y x z) : (term52 y x z) = True.
Proof. exact (EQ_MP (@lem1598967 y x z) (@lem1598879 y x z h1)). Qed.
Lemma lem1598977 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : (term7 y x z) = (True /\ True).
Proof. exact (MK_COMB (@lem1598974 x h1) (@lem1598976 y x z h2)). Qed.
Lemma lem1598979 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1598980 : (True /\ True) = True.
Proof. exact (@lem1598979 True). Qed.
Lemma lem1598981 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : (term7 y x z) = True.
Proof. exact (TRANS (@lem1598977 y x z h1 h2) (@lem1598980)). Qed.
Lemma lem1598982 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : True = (term7 y x z).
Proof. exact (SYM (@lem1598981 y x z h1 h2)). Qed.
Lemma lem1598983 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : term7 y x z.
Proof. exact (EQ_MP (@lem1598982 y x z h1 h2) (@lem0)). Qed.
Lemma lem1598984 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : term9 y z.
Proof. exact (ex_intro (term10 y z) x (@lem1598983 y x z h1 h2)). Qed.
Lemma lem1598985 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : real_lt y z.
Proof. exact (@lem1598951 y z (@lem1598984 y x z h1 h2)). Qed.
Lemma lem1598987 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : term30 y z.
Proof. exact (or_intro1 (@lem1598985 y x z h1 h2) (y = z)). Qed.
Lemma lem1598988 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term62 x y z.
Proof. exact (proj2 (@lem1598877 x y z h1)). Qed.
Lemma lem1598989 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term46 x.
Proof. exact (proj1 (@lem1598877 x y z h1)). Qed.
Lemma lem1598990 (y : real) (z : real) (h1 : y = z) : (y = z) = (term30 y z).
Proof. exact (prop_ext (fun h2 : y = z => @lem1598949 y z h1) (fun h2 : term30 y z => @lem1598880 y z h1)). Qed.
Lemma lem1598991 (y : real) (z : real) (h1 : y = z) : term30 y z.
Proof. exact (EQ_MP (@lem1598990 y z h1) (@lem1598880 y z h1)). Qed.
Lemma lem1598992 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : (term52 y x z) = (term30 y z).
Proof. exact (prop_ext (fun h3 : term52 y x z => @lem1598987 y x z h1 h2) (fun h3 : term30 y z => @lem1598879 y x z h2)). Qed.
Lemma lem1598993 (y : real) (x : real) (z : real) (h1 : term46 x) (h2 : term52 y x z) : term30 y z.
Proof. exact (EQ_MP (@lem1598992 y x z h1 h2) (@lem1598879 y x z h2)). Qed.
Lemma lem1598994 (y : real) (z : real) (x : real) (h1 : term62 x y z) (h2 : term46 x) : term30 y z.
Proof. exact (or_elim (@lem1598878 x y z h1) (fun h0 : term52 y x z => @lem1598993 y x z h2 h0) (fun h0 : y = z => @lem1598991 y z h0)). Qed.
Lemma lem1598995 (y : real) (z : real) (x : real) (h1 : term62 x y z) (h2 : term46 x) : (term46 x) = (term30 y z).
Proof. exact (prop_ext (fun h3 : term46 x => @lem1598994 y z x h1 h2) (fun h3 : term30 y z => @lem1598881 x h2)). Qed.
Lemma lem1598996 (y : real) (z : real) (x : real) (h1 : term62 x y z) (h2 : term46 x) : term30 y z.
Proof. exact (EQ_MP (@lem1598995 y z x h1 h2) (@lem1598881 x h2)). Qed.
Lemma lem1598997 (y : real) (z : real) (x : real) (h1 : term63 x y z) (h2 : term46 x) : (term62 x y z) = (term30 y z).
Proof. exact (prop_ext (fun h3 : term62 x y z => @lem1598996 y z x h3 h2) (fun h3 : term30 y z => @lem1598988 x y z h1)). Qed.
Lemma lem1598998 (y : real) (z : real) (x : real) (h1 : term63 x y z) (h2 : term46 x) : term30 y z.
Proof. exact (EQ_MP (@lem1598997 y z x h1 h2) (@lem1598988 x y z h1)). Qed.
Lemma lem1598999 (x : real) (y : real) (z : real) (h1 : term63 x y z) : (term46 x) = (term30 y z).
Proof. exact (prop_ext (fun h2 : term46 x => @lem1598998 y z x h1 h2) (fun h2 : term30 y z => @lem1598989 x y z h1)). Qed.
Lemma lem1599000 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term30 y z.
Proof. exact (EQ_MP (@lem1598999 x y z h1) (@lem1598989 x y z h1)). Qed.
Lemma lem1599001 (x : real) (y : real) (z : real) : term65 x y z.
Proof. exact (fun h0 : term63 x y z => @lem1599000 x y z h0). Qed.
Lemma lem1599002 (y : real) (z : real) (x : real) (h1 : term20 x) : term41 x y z.
Proof. exact (EQ_MP (@lem1598876 y z x h1) (@lem1599001 x y z)). Qed.
Lemma lem1599003 (x : real) (y : real) (z : real) : term41 x y z.
Proof. exact (or_elim (@lem1598660 x) (fun h0 : x = term18 => @lem1598811 y z x h0) (fun h0 : term20 x => @lem1599002 y z x h0)). Qed.
Lemma lem1599004 (x : real) (y : real) (z : real) : term40 x y z.
Proof. exact (EQ_MP (@lem1598716 x y z) (@lem1599003 x y z)). Qed.
Lemma lem1599009 (x : real) (y : real) : term69 x y.
Proof. exact (fun z : real => @lem1599004 x y z). Qed.
Lemma lem1599014 (x : real) : term70 x.
Proof. exact (fun y : real => @lem1599009 x y). Qed.
Lemma lem1599019 : term71.
Proof. exact (fun x : real => @lem1599014 x). Qed.
