Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SQUARE_ABS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ABS_POS_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW2_ABS_spec.
Require Import REAL_POW_LE2_spec.
Require Import REAL_POW_LT2_spec.
Require Import thm0_spec.
Require Import thm1013352_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm912803_spec.
Lemma lem1643627 : term0 = term1.
Proof. exact (@lem912803). Qed.
Lemma lem1643628 (h1 : term0 = term1) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term1 h1). Qed.
Lemma lem1643629 : (term0 = term1) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term0 = term1 => @lem1643628 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem1643627)). Qed.
Lemma lem1643630 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1643629) (@lem1643627)). Qed.
Lemma lem1643631 (t1 : Prop) : term3 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1643632 (t1 : Prop) : (term3 t1) = (term4 t1).
Proof. exact (eq_refl (term3 t1)). Qed.
Lemma lem1643633 (t1 : Prop) : term4 t1.
Proof. exact (EQ_MP (@lem1643632 t1) (@lem1643631 t1)). Qed.
Lemma lem1643634 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (@lem1643633 t1 t2). Qed.
Lemma lem1643635 (t1 : Prop) (t2 : Prop) : (term5 t1 t2) = (term6 t1 t2).
Proof. exact (eq_refl (term5 t1 t2)). Qed.
Lemma lem1643636 (t1 : Prop) (t2 : Prop) : term6 t1 t2.
Proof. exact (EQ_MP (@lem1643635 t1 t2) (@lem1643634 t1 t2)). Qed.
Lemma lem1643637 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term7 t1 t2 t3.
Proof. exact (@lem1643636 t1 t2 t3). Qed.
Lemma lem1643638 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term7 t1 t2 t3) = ((term8 t1 t2 t3) = (term9 t1 t2 t3)).
Proof. exact (eq_refl (term7 t1 t2 t3)). Qed.
Lemma lem1643639 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term8 t1 t2 t3) = (term9 t1 t2 t3).
Proof. exact (EQ_MP (@lem1643638 t1 t2 t3) (@lem1643637 t1 t2 t3)). Qed.
Lemma lem1643640 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term9 t1 t2 t3) = (term8 t1 t2 t3).
Proof. exact (SYM (@lem1643639 t1 t2 t3)). Qed.
Lemma lem1643642 (x : real) (h1 : (term10 x) = (term11 x)) : (term10 x) = (term11 x).
Proof. exact (h1). Qed.
Lemma lem1643643 (x : real) (h1 : (term10 x) = (term11 x)) : (term11 x) = (term10 x).
Proof. exact (SYM (@lem1643642 x h1)). Qed.
Lemma lem1643644 (x : real) (h1 : (term11 x) = (term10 x)) : (term11 x) = (term10 x).
Proof. exact (h1). Qed.
Lemma lem1643645 (x : real) (h1 : (term11 x) = (term10 x)) : (term10 x) = (term11 x).
Proof. exact (SYM (@lem1643644 x h1)). Qed.
Lemma lem1643646 (x : real) : ((term10 x) = (term11 x)) = ((term11 x) = (term10 x)).
Proof. exact (prop_ext (fun h1 : (term10 x) = (term11 x) => @lem1643643 x h1) (fun h1 : (term11 x) = (term10 x) => @lem1643645 x h1)). Qed.
Lemma lem1643647 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1643646 x)). Qed.
Lemma lem1643648 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643649 : term14 = term15.
Proof. exact (MK_COMB (@lem1643648) (@lem1643647)). Qed.
Lemma lem1643650 : term15.
Proof. exact (EQ_MP (@lem1643649) (@lem1643626)). Qed.
Lemma lem1643651 (x : real) : term16 x.
Proof. exact (@lem1643650 x). Qed.
Lemma lem1643652 (x : real) : (term16 x) = ((term11 x) = (term10 x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1643657 (x : real) : (term11 x) = (term10 x).
Proof. exact (EQ_MP (@lem1643652 x) (@lem1643651 x)). Qed.
Lemma lem1643658 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1643659 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1643658) (@lem1643657 x)). Qed.
Lemma lem1643661 (x : real) : (term11 x) = (term10 x).
Proof. exact (EQ_MP (@lem1643652 x) (@lem1643651 x)). Qed.
Lemma lem1643662 (y : real) : (term11 y) = (term10 y).
Proof. exact (@lem1643661 y). Qed.
Lemma lem1643663 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1643659 x) (@lem1643662 y)). Qed.
Lemma lem1643664 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1643665 (x : real) (y : real) : ((term22 x y) = (term19 x y)) = ((term22 x y) = (term20 x y)).
Proof. exact (MK_COMB (@lem1643664 x y) (@lem1643663 x y)). Qed.
Lemma lem1643666 (x : real) (y : real) : ((term22 x y) = (term20 x y)) = ((term22 x y) = (term19 x y)).
Proof. exact (SYM (@lem1643665 x y)). Qed.
Lemma lem1643668 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1643669 (x : real) (y : real) : ((term22 x y) = (term20 x y)) = (term24 x y).
Proof. exact (@lem1643668 ((term22 x y) = (term20 x y))). Qed.
Lemma lem1643670 (x : real) (y : real) : (term24 x y) = ((term22 x y) = (term20 x y)).
Proof. exact (SYM (@lem1643669 x y)). Qed.
Lemma lem1643671 (x : real) (y : real) (h1 : term25 x y) : term25 x y.
Proof. exact (h1). Qed.
Lemma lem1643674 (x : real) (y : real) (h1 : term26 x y) : term26 x y.
Proof. exact (h1). Qed.
Lemma lem1643675 (x : real) (y : real) : term27 x y.
Proof. exact (fun h0 : term26 x y => @lem1643674 x y h0). Qed.
Lemma lem1643676 (x : real) (y : real) (h1 : term27 x y) : term27 x y.
Proof. exact (h1). Qed.
Lemma lem1643677 (x : real) (y : real) (h1 : term26 x y) : term26 x y.
Proof. exact (h1). Qed.
Lemma lem1643678 (x : real) (y : real) (h1 : term26 x y) (h2 : term27 x y) : term26 x y.
Proof. exact (@lem1643676 x y h2 (@lem1643677 x y h1)). Qed.
Lemma lem1643679 (x : real) (y : real) (h1 : term26 x y) : term28 x y.
Proof. exact (fun h0 : term27 x y => @lem1643678 x y h1 h0). Qed.
Lemma lem1643680 (x : real) (y : real) (h1 : term27 x y) : term27 x y.
Proof. exact (h1). Qed.
Lemma lem1643681 (x : real) (y : real) (h1 : term26 x y) (h2 : term27 x y) : term26 x y.
Proof. exact (@lem1643679 x y h1 (@lem1643680 x y h2)). Qed.
Lemma lem1643682 (x : real) (y : real) (h1 : term27 x y) : term27 x y.
Proof. exact (fun h0 : term26 x y => @lem1643681 x y h0 h1). Qed.
Lemma lem1643683 (x : real) (y : real) : term29 x y.
Proof. exact (fun h0 : term27 x y => @lem1643682 x y h0). Qed.
Lemma lem1643686 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1643683 x y (@lem1643675 x y)). Qed.
Lemma lem1643730 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1643731 : ((term2 = (NUMERAL 0)) = False) = term30.
Proof. exact (@lem1643730 (term2 = (NUMERAL 0))). Qed.
Lemma lem1643732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1643733 : term31 = term32.
Proof. exact (MK_COMB (@lem1643732) (@lem1643731)). Qed.
Lemma lem1643741 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1643742 : term33 = term34.
Proof. exact (@lem1643741 term35). Qed.
Lemma lem1643759 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1643760 : term37 = term38.
Proof. exact (MK_COMB (@lem1643759) (@lem1643742)). Qed.
Lemma lem1643763 : term39 = term40.
Proof. exact (MK_COMB (@lem1643733) (@lem1643760)). Qed.
Lemma lem1643766 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1643767 : term42 = term43.
Proof. exact (MK_COMB (@lem1643766) (@lem1643763)). Qed.
Lemma lem1643770 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1643771 : term45 = term46.
Proof. exact (MK_COMB (@lem1643770) (@lem1643767)). Qed.
Lemma lem1643774 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1643775 (x : real) (y : real) : (term26 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1643774 x y) (@lem1643771)). Qed.
Lemma lem1643778 (y : real) : (term49 y) = (term50 y).
Proof. exact (fun_ext (fun x : real => @lem1643775 x y)). Qed.
Lemma lem1643779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643780 (y : real) : (term51 y) = (term52 y).
Proof. exact (MK_COMB (@lem1643779) (@lem1643778 y)). Qed.
Lemma lem1643785 : term53 = term54.
Proof. exact (fun_ext (fun y : real => @lem1643780 y)). Qed.
Lemma lem1643786 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643795 : term55 = term56.
Proof. exact (MK_COMB (@lem1643786) (@lem1643785)). Qed.
Lemma lem1643804 (x : real) (y : real) (n : nat) : (term57 x y n) = (term57 x y n).
Proof. exact (eq_refl (term57 x y n)). Qed.
Lemma lem1643805 (x : real) (n : nat) : (term58 x n) = (term58 x n).
Proof. exact (fun_ext (fun y : real => @lem1643804 x y n)). Qed.
Lemma lem1643806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643807 (x : real) (n : nat) : (term59 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem1643806) (@lem1643805 x n)). Qed.
Lemma lem1643808 (n : nat) : (term60 n) = (term60 n).
Proof. exact (fun_ext (fun x : real => @lem1643807 x n)). Qed.
Lemma lem1643809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643810 (n : nat) : (term61 n) = (term61 n).
Proof. exact (MK_COMB (@lem1643809) (@lem1643808 n)). Qed.
Lemma lem1643811 : term62 = term62.
Proof. exact (fun_ext (fun n : nat => @lem1643810 n)). Qed.
Lemma lem1643812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1643813 : term35 = term35.
Proof. exact (MK_COMB (@lem1643812) (@lem1643811)). Qed.
Lemma lem1643814 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1643815 : term34 = term34.
Proof. exact (MK_COMB (@lem1643814) (@lem1643813)). Qed.
Lemma lem1643816 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1643817 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1643816 x)). Qed.
Lemma lem1643818 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643819 : term65 = term65.
Proof. exact (MK_COMB (@lem1643818) (@lem1643817)). Qed.
Lemma lem1643820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1643821 : term36 = term36.
Proof. exact (MK_COMB (@lem1643820) (@lem1643819)). Qed.
Lemma lem1643822 : term38 = term38.
Proof. exact (MK_COMB (@lem1643821) (@lem1643815)). Qed.
Lemma lem1643827 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1643828 : term40 = term40.
Proof. exact (MK_COMB (@lem1643827) (@lem1643822)). Qed.
Lemma lem1643843 (x : real) (y : real) (n : nat) : (term66 x y n) = (term66 x y n).
Proof. exact (eq_refl (term66 x y n)). Qed.
Lemma lem1643844 (x : real) (n : nat) : (term67 x n) = (term67 x n).
Proof. exact (fun_ext (fun y : real => @lem1643843 x y n)). Qed.
Lemma lem1643845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643846 (x : real) (n : nat) : (term68 x n) = (term68 x n).
Proof. exact (MK_COMB (@lem1643845) (@lem1643844 x n)). Qed.
Lemma lem1643847 (n : nat) : (term69 n) = (term69 n).
Proof. exact (fun_ext (fun x : real => @lem1643846 x n)). Qed.
Lemma lem1643848 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643849 (n : nat) : (term70 n) = (term70 n).
Proof. exact (MK_COMB (@lem1643848) (@lem1643847 n)). Qed.
Lemma lem1643850 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem1643849 n)). Qed.
Lemma lem1643851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1643852 : term72 = term72.
Proof. exact (MK_COMB (@lem1643851) (@lem1643850)). Qed.
Lemma lem1643853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1643854 : term41 = term41.
Proof. exact (MK_COMB (@lem1643853) (@lem1643852)). Qed.
Lemma lem1643855 : term43 = term43.
Proof. exact (MK_COMB (@lem1643854) (@lem1643828)). Qed.
Lemma lem1643862 (y : real) (x : real) : ((term73 x y) = (real_lt y x)) = ((term73 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term73 x y) = (real_lt y x))). Qed.
Lemma lem1643863 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1643862 y x)). Qed.
Lemma lem1643864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643865 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1643864) (@lem1643863 x)). Qed.
Lemma lem1643866 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1643865 x)). Qed.
Lemma lem1643867 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643868 : term77 = term77.
Proof. exact (MK_COMB (@lem1643867) (@lem1643866)). Qed.
Lemma lem1643869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1643870 : term44 = term44.
Proof. exact (MK_COMB (@lem1643869) (@lem1643868)). Qed.
Lemma lem1643871 : term46 = term46.
Proof. exact (MK_COMB (@lem1643870) (@lem1643855)). Qed.
Lemma lem1643880 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1643881 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1643880 x y) (@lem1643871)). Qed.
Lemma lem1643882 (y : real) : (term50 y) = (term50 y).
Proof. exact (fun_ext (fun x : real => @lem1643881 x y)). Qed.
Lemma lem1643883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643884 (y : real) : (term52 y) = (term52 y).
Proof. exact (MK_COMB (@lem1643883) (@lem1643882 y)). Qed.
Lemma lem1643885 : term54 = term54.
Proof. exact (fun_ext (fun y : real => @lem1643884 y)). Qed.
Lemma lem1643886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1643887 : term56 = term56.
Proof. exact (MK_COMB (@lem1643886) (@lem1643885)). Qed.
Lemma lem1643976 : term55 = term56.
Proof. exact (TRANS (@lem1643795) (@lem1643887)). Qed.
Lemma lem1643977 : term56 = term55.
Proof. exact (SYM (@lem1643976)). Qed.
Lemma lem1643978 (x : real) (y : real) (h1 : term25 x y) : term25 x y.
Proof. exact (h1). Qed.
Lemma lem1643979 (h1 : term77) : term77.
Proof. exact (h1). Qed.
Lemma lem1643980 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem1643982 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1643983 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1644002 (x : real) (y : real) : (term25 x y) = (term78 x y).
Proof. exact (@lem17646 (term22 x y) (term20 x y)). Qed.
Lemma lem1644007 (x : real) (y : real) : (term79 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1644009 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem1644010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1644011 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1644010) (@lem1644007 x y)). Qed.
Lemma lem1644012 (y : real) (x : real) : (term82 y x) = (term83 y x).
Proof. exact (MK_COMB (@lem1644011 x y) (@lem1644009 y x)). Qed.
Lemma lem1644017 (y : real) (x : real) : (term84 y x) = (term84 y x).
Proof. exact (eq_refl (term84 y x)). Qed.
Lemma lem1644018 (y : real) (x : real) : (term85 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1644017 y x) (@lem1644012 y x)). Qed.
Lemma lem1644019 (y : real) (x : real) : ((term73 x y) = (real_lt y x)) = (term85 y x).
Proof. exact (@lem17784 (term73 x y) (real_lt y x)). Qed.
Lemma lem1644020 (y : real) (x : real) : ((term73 x y) = (real_lt y x)) = (term86 y x).
Proof. exact (TRANS (@lem1644019 y x) (@lem1644018 y x)). Qed.
Lemma lem1644021 (x : real) : (term74 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1644020 y x)). Qed.
Lemma lem1644022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644023 (x : real) : (term75 x) = (term88 x).
Proof. exact (MK_COMB (@lem1644022) (@lem1644021 x)). Qed.
Lemma lem1644024 : term76 = term89.
Proof. exact (fun_ext (fun x : real => @lem1644023 x)). Qed.
Lemma lem1644025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644026 : term77 = term90.
Proof. exact (MK_COMB (@lem1644025) (@lem1644024)). Qed.
Lemma lem1644032 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1644033 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1644032 real P Q). Qed.
Lemma lem1644034 (x : real) : (term95 x) = (term96 x).
Proof. exact (@lem1644033 (term97 x) (term98 x)). Qed.
Lemma lem1644035 (y : real) (x : real) : (term99 x y) = (term100 y x).
Proof. exact (eq_refl (term99 x y)). Qed.
Lemma lem1644036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1644037 (y : real) (x : real) : (term101 x y) = (term84 y x).
Proof. exact (MK_COMB (@lem1644036) (@lem1644035 y x)). Qed.
Lemma lem1644038 (y : real) (x : real) : (term102 x y) = (term83 y x).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem1644039 (y : real) (x : real) : (term103 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1644037 y x) (@lem1644038 y x)). Qed.
Lemma lem1644040 (x : real) : (term104 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1644039 y x)). Qed.
Lemma lem1644041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644042 (x : real) : (term95 x) = (term88 x).
Proof. exact (MK_COMB (@lem1644041) (@lem1644040 x)). Qed.
Lemma lem1644043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1644044 (x : real) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1644043) (@lem1644042 x)). Qed.
Lemma lem1644045 (y : real) (x : real) : (term99 x y) = (term100 y x).
Proof. exact (eq_refl (term99 x y)). Qed.
Lemma lem1644046 (x : real) : (term107 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1644045 y x)). Qed.
Lemma lem1644047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644048 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1644047) (@lem1644046 x)). Qed.
Lemma lem1644049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1644050 (x : real) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1644049) (@lem1644048 x)). Qed.
Lemma lem1644051 (y : real) (x : real) : (term102 x y) = (term83 y x).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem1644052 (x : real) : (term112 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1644051 y x)). Qed.
Lemma lem1644053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644054 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1644053) (@lem1644052 x)). Qed.
Lemma lem1644055 (x : real) : (term96 x) = (term115 x).
Proof. exact (MK_COMB (@lem1644050 x) (@lem1644054 x)). Qed.
Lemma lem1644056 (x : real) : ((term95 x) = (term96 x)) = ((term88 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1644044 x) (@lem1644055 x)). Qed.
Lemma lem1644057 (x : real) : (term88 x) = (term115 x).
Proof. exact (EQ_MP (@lem1644056 x) (@lem1644034 x)). Qed.
Lemma lem1644154 : term89 = term116.
Proof. exact (fun_ext (fun x : real => @lem1644057 x)). Qed.
Lemma lem1644155 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644156 : term90 = term117.
Proof. exact (MK_COMB (@lem1644155) (@lem1644154)). Qed.
Lemma lem1644158 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1644159 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1644158 real P Q). Qed.
Lemma lem1644160 : term118 = term119.
Proof. exact (@lem1644159 term120 term121). Qed.
Lemma lem1644161 (x : real) : (term122 x) = (term109 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1644162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1644163 (x : real) : (term123 x) = (term111 x).
Proof. exact (MK_COMB (@lem1644162) (@lem1644161 x)). Qed.
Lemma lem1644164 (x : real) : (term124 x) = (term114 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1644165 (x : real) : (term125 x) = (term115 x).
Proof. exact (MK_COMB (@lem1644163 x) (@lem1644164 x)). Qed.
Lemma lem1644166 : term126 = term116.
Proof. exact (fun_ext (fun x : real => @lem1644165 x)). Qed.
Lemma lem1644167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644168 : term118 = term117.
Proof. exact (MK_COMB (@lem1644167) (@lem1644166)). Qed.
Lemma lem1644169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1644170 : term127 = term128.
Proof. exact (MK_COMB (@lem1644169) (@lem1644168)). Qed.
Lemma lem1644171 (x : real) : (term122 x) = (term109 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1644172 : term129 = term120.
Proof. exact (fun_ext (fun x : real => @lem1644171 x)). Qed.
Lemma lem1644173 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644174 : term130 = term131.
Proof. exact (MK_COMB (@lem1644173) (@lem1644172)). Qed.
Lemma lem1644175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1644176 : term132 = term133.
Proof. exact (MK_COMB (@lem1644175) (@lem1644174)). Qed.
Lemma lem1644177 (x : real) : (term124 x) = (term114 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1644178 : term134 = term121.
Proof. exact (fun_ext (fun x : real => @lem1644177 x)). Qed.
Lemma lem1644179 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644180 : term135 = term136.
Proof. exact (MK_COMB (@lem1644179) (@lem1644178)). Qed.
Lemma lem1644181 : term119 = term137.
Proof. exact (MK_COMB (@lem1644176) (@lem1644180)). Qed.
Lemma lem1644182 : (term118 = term119) = (term117 = term137).
Proof. exact (MK_COMB (@lem1644170) (@lem1644181)). Qed.
Lemma lem1644183 : term117 = term137.
Proof. exact (EQ_MP (@lem1644182) (@lem1644160)). Qed.
Lemma lem1644290 : term90 = term137.
Proof. exact (TRANS (@lem1644156) (@lem1644183)). Qed.
Lemma lem1644291 : term77 = term137.
Proof. exact (TRANS (@lem1644026) (@lem1644290)). Qed.
Lemma lem1644292 (h1 : term77) : term137.
Proof. exact (EQ_MP (@lem1644291) (@lem1643979 h1)). Qed.
Lemma lem1644295 (n : nat) : (term138 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1644302 (x : real) (y : real) : (term139 x y) = (term140 x y).
Proof. exact (@lem17045 (term141 x) (real_lt x y)). Qed.
Lemma lem1644303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1644304 (n : nat) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem1644303) (@lem1644295 n)). Qed.
Lemma lem1644305 (n : nat) (x : real) (y : real) : (term144 n x y) = (term145 n x y).
Proof. exact (MK_COMB (@lem1644304 n) (@lem1644302 x y)). Qed.
Lemma lem1644306 (n : nat) (x : real) (y : real) : (term146 n x y) = (term144 n x y).
Proof. exact (@lem17045 (term147 n) (term148 x y)). Qed.
Lemma lem1644307 (n : nat) (x : real) (y : real) : (term146 n x y) = (term145 n x y).
Proof. exact (TRANS (@lem1644306 n x y) (@lem1644305 n x y)). Qed.
Lemma lem1644308 (x : real) (y : real) (n : nat) : (term149 x y n) = (term149 x y n).
Proof. exact (eq_refl (term149 x y n)). Qed.
Lemma lem1644309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1644310 (n : nat) (x : real) (y : real) : (term150 n x y) = (term151 n x y).
Proof. exact (MK_COMB (@lem1644309) (@lem1644307 n x y)). Qed.
Lemma lem1644311 (x : real) (y : real) (n : nat) : (term152 x y n) = (term153 x y n).
Proof. exact (MK_COMB (@lem1644310 n x y) (@lem1644308 x y n)). Qed.
Lemma lem1644312 (x : real) (y : real) (n : nat) : (term66 x y n) = (term152 x y n).
Proof. exact (@lem17265 (term154 n x y) (term149 x y n)). Qed.
Lemma lem1644313 (x : real) (y : real) (n : nat) : (term66 x y n) = (term153 x y n).
Proof. exact (TRANS (@lem1644312 x y n) (@lem1644311 x y n)). Qed.
Lemma lem1644314 (x : real) (n : nat) : (term67 x n) = (term155 x n).
Proof. exact (fun_ext (fun y : real => @lem1644313 x y n)). Qed.
Lemma lem1644315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644316 (x : real) (n : nat) : (term68 x n) = (term156 x n).
Proof. exact (MK_COMB (@lem1644315) (@lem1644314 x n)). Qed.
Lemma lem1644317 (n : nat) : (term69 n) = (term157 n).
Proof. exact (fun_ext (fun x : real => @lem1644316 x n)). Qed.
Lemma lem1644318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644319 (n : nat) : (term70 n) = (term158 n).
Proof. exact (MK_COMB (@lem1644318) (@lem1644317 n)). Qed.
Lemma lem1644320 : term71 = term159.
Proof. exact (fun_ext (fun n : nat => @lem1644319 n)). Qed.
Lemma lem1644321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644382 : term72 = term160.
Proof. exact (MK_COMB (@lem1644321) (@lem1644320)). Qed.
Lemma lem1644383 (h1 : term72) : term160.
Proof. exact (EQ_MP (@lem1644382) (@lem1643980 h1)). Qed.
Lemma lem1644389 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1644390 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1644391 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1644390 x)). Qed.
Lemma lem1644392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644401 : term65 = term65.
Proof. exact (MK_COMB (@lem1644392) (@lem1644391)). Qed.
Lemma lem1644402 (h1 : term65) : term65.
Proof. exact (EQ_MP (@lem1644401) (@lem1643982 h1)). Qed.
Lemma lem1644409 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem17045 (term141 x) (real_le x y)). Qed.
Lemma lem1644410 (x : real) (y : real) (n : nat) : (term163 x y n) = (term163 x y n).
Proof. exact (eq_refl (term163 x y n)). Qed.
Lemma lem1644411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1644412 (x : real) (y : real) : (term164 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1644411) (@lem1644409 x y)). Qed.
Lemma lem1644413 (x : real) (y : real) (n : nat) : (term166 x y n) = (term167 x y n).
Proof. exact (MK_COMB (@lem1644412 x y) (@lem1644410 x y n)). Qed.
Lemma lem1644414 (x : real) (y : real) (n : nat) : (term57 x y n) = (term166 x y n).
Proof. exact (@lem17265 (term168 x y) (term163 x y n)). Qed.
Lemma lem1644415 (x : real) (y : real) (n : nat) : (term57 x y n) = (term167 x y n).
Proof. exact (TRANS (@lem1644414 x y n) (@lem1644413 x y n)). Qed.
Lemma lem1644416 (x : real) (n : nat) : (term58 x n) = (term169 x n).
Proof. exact (fun_ext (fun y : real => @lem1644415 x y n)). Qed.
Lemma lem1644417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644418 (x : real) (n : nat) : (term59 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem1644417) (@lem1644416 x n)). Qed.
Lemma lem1644419 (n : nat) : (term60 n) = (term171 n).
Proof. exact (fun_ext (fun x : real => @lem1644418 x n)). Qed.
Lemma lem1644420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644421 (n : nat) : (term61 n) = (term172 n).
Proof. exact (MK_COMB (@lem1644420) (@lem1644419 n)). Qed.
Lemma lem1644422 : term62 = term173.
Proof. exact (fun_ext (fun n : nat => @lem1644421 n)). Qed.
Lemma lem1644423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644484 : term35 = term174.
Proof. exact (MK_COMB (@lem1644423) (@lem1644422)). Qed.
Lemma lem1644485 (h1 : term35) : term174.
Proof. exact (EQ_MP (@lem1644484) (@lem1643983 h1)). Qed.
Lemma lem1644575 (x : real) (y : real) (h1 : term25 x y) : term78 x y.
Proof. exact (EQ_MP (@lem1644002 x y) (@lem1643978 x y h1)). Qed.
Lemma lem1644588 (y : real) (x : real) : (term83 y x) = (term83 y x).
Proof. exact (eq_refl (term83 y x)). Qed.
Lemma lem1644589 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1644588 y x)). Qed.
Lemma lem1644590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644591 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1644590) (@lem1644589 x)). Qed.
Lemma lem1644592 : term121 = term121.
Proof. exact (fun_ext (fun x : real => @lem1644591 x)). Qed.
Lemma lem1644593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644594 : term136 = term136.
Proof. exact (MK_COMB (@lem1644593) (@lem1644592)). Qed.
Lemma lem1644611 (y : real) (x : real) : (term100 y x) = (term100 y x).
Proof. exact (eq_refl (term100 y x)). Qed.
Lemma lem1644612 (x : real) : (term97 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1644611 y x)). Qed.
Lemma lem1644613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644614 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1644613) (@lem1644612 x)). Qed.
Lemma lem1644615 : term120 = term120.
Proof. exact (fun_ext (fun x : real => @lem1644614 x)). Qed.
Lemma lem1644616 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644617 : term131 = term131.
Proof. exact (MK_COMB (@lem1644616) (@lem1644615)). Qed.
Lemma lem1644618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1644619 : term133 = term133.
Proof. exact (MK_COMB (@lem1644618) (@lem1644617)). Qed.
Lemma lem1644620 : term137 = term137.
Proof. exact (MK_COMB (@lem1644619) (@lem1644594)). Qed.
Lemma lem1644621 (h1 : term77) : term137.
Proof. exact (EQ_MP (@lem1644620) (@lem1644292 h1)). Qed.
Lemma lem1644668 (x : real) (y : real) (n : nat) : (term153 x y n) = (term153 x y n).
Proof. exact (eq_refl (term153 x y n)). Qed.
Lemma lem1644669 (x : real) (n : nat) : (term155 x n) = (term155 x n).
Proof. exact (fun_ext (fun y : real => @lem1644668 x y n)). Qed.
Lemma lem1644670 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644671 (x : real) (n : nat) : (term156 x n) = (term156 x n).
Proof. exact (MK_COMB (@lem1644670) (@lem1644669 x n)). Qed.
Lemma lem1644672 (n : nat) : (term157 n) = (term157 n).
Proof. exact (fun_ext (fun x : real => @lem1644671 x n)). Qed.
Lemma lem1644673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644674 (n : nat) : (term158 n) = (term158 n).
Proof. exact (MK_COMB (@lem1644673) (@lem1644672 n)). Qed.
Lemma lem1644675 : term159 = term159.
Proof. exact (fun_ext (fun n : nat => @lem1644674 n)). Qed.
Lemma lem1644676 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644677 : term160 = term160.
Proof. exact (MK_COMB (@lem1644676) (@lem1644675)). Qed.
Lemma lem1644678 (h1 : term72) : term160.
Proof. exact (EQ_MP (@lem1644677) (@lem1644383 h1)). Qed.
Lemma lem1644694 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1644705 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1644706 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1644705 x)). Qed.
Lemma lem1644707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644708 : term65 = term65.
Proof. exact (MK_COMB (@lem1644707) (@lem1644706)). Qed.
Lemma lem1644709 (h1 : term65) : term65.
Proof. exact (EQ_MP (@lem1644708) (@lem1644402 h1)). Qed.
Lemma lem1644746 (x : real) (y : real) (n : nat) : (term167 x y n) = (term167 x y n).
Proof. exact (eq_refl (term167 x y n)). Qed.
Lemma lem1644747 (x : real) (n : nat) : (term169 x n) = (term169 x n).
Proof. exact (fun_ext (fun y : real => @lem1644746 x y n)). Qed.
Lemma lem1644748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644749 (x : real) (n : nat) : (term170 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem1644748) (@lem1644747 x n)). Qed.
Lemma lem1644750 (n : nat) : (term171 n) = (term171 n).
Proof. exact (fun_ext (fun x : real => @lem1644749 x n)). Qed.
Lemma lem1644751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644752 (n : nat) : (term172 n) = (term172 n).
Proof. exact (MK_COMB (@lem1644751) (@lem1644750 n)). Qed.
Lemma lem1644753 : term173 = term173.
Proof. exact (fun_ext (fun n : nat => @lem1644752 n)). Qed.
Lemma lem1644754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644755 : term174 = term174.
Proof. exact (MK_COMB (@lem1644754) (@lem1644753)). Qed.
Lemma lem1644756 (h1 : term35) : term174.
Proof. exact (EQ_MP (@lem1644755) (@lem1644485 h1)). Qed.
Lemma lem1644757 (h1 : term77) : term136.
Proof. exact (proj2 (@lem1644621 h1)). Qed.
Lemma lem1644758 (h1 : term77) : term131.
Proof. exact (proj1 (@lem1644621 h1)). Qed.
Lemma lem1644759 (x : real) (y : real) (h1 : term175 x y) : term175 x y.
Proof. exact (h1). Qed.
Lemma lem1644760 (x : real) (y : real) (h1 : term176 x y) : term176 x y.
Proof. exact (h1). Qed.
Lemma lem1644801 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1644802 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1644801 x)). Qed.
Lemma lem1644803 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644805 : term65 = term65.
Proof. exact (MK_COMB (@lem1644803) (@lem1644802)). Qed.
Lemma lem1644806 (h1 : term65) : term65.
Proof. exact (EQ_MP (@lem1644805) (@lem1644709 h1)). Qed.
Lemma lem1644820 (x : real) (y : real) (n : nat) : (term167 x y n) = (term167 x y n).
Proof. exact (eq_refl (term167 x y n)). Qed.
Lemma lem1644821 (x : real) (n : nat) : (term169 x n) = (term169 x n).
Proof. exact (fun_ext (fun y : real => @lem1644820 x y n)). Qed.
Lemma lem1644822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644823 (x : real) (n : nat) : (term170 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem1644822) (@lem1644821 x n)). Qed.
Lemma lem1644824 (n : nat) : (term171 n) = (term171 n).
Proof. exact (fun_ext (fun x : real => @lem1644823 x n)). Qed.
Lemma lem1644825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644826 (n : nat) : (term172 n) = (term172 n).
Proof. exact (MK_COMB (@lem1644825) (@lem1644824 n)). Qed.
Lemma lem1644827 : term173 = term173.
Proof. exact (fun_ext (fun n : nat => @lem1644826 n)). Qed.
Lemma lem1644828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644830 : term174 = term174.
Proof. exact (MK_COMB (@lem1644828) (@lem1644827)). Qed.
Lemma lem1644831 (h1 : term35) : term174.
Proof. exact (EQ_MP (@lem1644830) (@lem1644756 h1)). Qed.
Lemma lem1644891 (x : real) (y : real) (n : nat) : (term153 x y n) = (term153 x y n).
Proof. exact (eq_refl (term153 x y n)). Qed.
Lemma lem1644892 (x : real) (n : nat) : (term155 x n) = (term155 x n).
Proof. exact (fun_ext (fun y : real => @lem1644891 x y n)). Qed.
Lemma lem1644893 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644894 (x : real) (n : nat) : (term156 x n) = (term156 x n).
Proof. exact (MK_COMB (@lem1644893) (@lem1644892 x n)). Qed.
Lemma lem1644895 (n : nat) : (term157 n) = (term157 n).
Proof. exact (fun_ext (fun x : real => @lem1644894 x n)). Qed.
Lemma lem1644896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644897 (n : nat) : (term158 n) = (term158 n).
Proof. exact (MK_COMB (@lem1644896) (@lem1644895 n)). Qed.
Lemma lem1644898 : term159 = term159.
Proof. exact (fun_ext (fun n : nat => @lem1644897 n)). Qed.
Lemma lem1644899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1644901 : term160 = term160.
Proof. exact (MK_COMB (@lem1644899) (@lem1644898)). Qed.
Lemma lem1644902 (h1 : term72) : term160.
Proof. exact (EQ_MP (@lem1644901) (@lem1644678 h1)). Qed.
Lemma lem1644906 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1644908 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1644909 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1644908 x)). Qed.
Lemma lem1644910 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644912 : term65 = term65.
Proof. exact (MK_COMB (@lem1644910) (@lem1644909)). Qed.
Lemma lem1644913 (h1 : term65) : term65.
Proof. exact (EQ_MP (@lem1644912) (@lem1644709 h1)). Qed.
Lemma lem1644946 (y : real) (x : real) : (term100 y x) = (term100 y x).
Proof. exact (eq_refl (term100 y x)). Qed.
Lemma lem1644947 (x : real) : (term97 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1644946 y x)). Qed.
Lemma lem1644948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644949 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1644948) (@lem1644947 x)). Qed.
Lemma lem1644950 : term120 = term120.
Proof. exact (fun_ext (fun x : real => @lem1644949 x)). Qed.
Lemma lem1644951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644953 : term131 = term131.
Proof. exact (MK_COMB (@lem1644951) (@lem1644950)). Qed.
Lemma lem1644954 (h1 : term77) : term131.
Proof. exact (EQ_MP (@lem1644953) (@lem1644758 h1)). Qed.
Lemma lem1644962 (y : real) (x : real) : (term83 y x) = (term83 y x).
Proof. exact (eq_refl (term83 y x)). Qed.
Lemma lem1644963 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1644962 y x)). Qed.
Lemma lem1644964 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644965 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1644964) (@lem1644963 x)). Qed.
Lemma lem1644966 : term121 = term121.
Proof. exact (fun_ext (fun x : real => @lem1644965 x)). Qed.
Lemma lem1644967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1644969 : term136 = term136.
Proof. exact (MK_COMB (@lem1644967) (@lem1644966)). Qed.
Lemma lem1644970 (h1 : term77) : term136.
Proof. exact (EQ_MP (@lem1644969) (@lem1644757 h1)). Qed.
Lemma lem1644988 (_25498 : real) (h1 : term65) : term177 _25498.
Proof. exact (@lem1644806 h1 _25498). Qed.
Lemma lem1644989 (_25498 : real) : (term177 _25498) = (term63 _25498).
Proof. exact (eq_refl (term177 _25498)). Qed.
Lemma lem1644991 (_25499 : nat) (h1 : term35) : term178 _25499.
Proof. exact (@lem1644831 h1 _25499). Qed.
Lemma lem1644992 (_25499 : nat) : (term178 _25499) = (term172 _25499).
Proof. exact (eq_refl (term178 _25499)). Qed.
Lemma lem1644993 (_25499 : nat) (h1 : term35) : term172 _25499.
Proof. exact (EQ_MP (@lem1644992 _25499) (@lem1644991 _25499 h1)). Qed.
Lemma lem1644994 (_25499 : nat) (_25500 : real) (h1 : term35) : term179 _25499 _25500.
Proof. exact (@lem1644993 _25499 h1 _25500). Qed.
Lemma lem1644995 (_25500 : real) (_25499 : nat) : (term179 _25499 _25500) = (term170 _25500 _25499).
Proof. exact (eq_refl (term179 _25499 _25500)). Qed.
Lemma lem1644996 (_25500 : real) (_25499 : nat) (h1 : term35) : term170 _25500 _25499.
Proof. exact (EQ_MP (@lem1644995 _25500 _25499) (@lem1644994 _25499 _25500 h1)). Qed.
Lemma lem1644997 (_25500 : real) (_25499 : nat) (_25501 : real) (h1 : term35) : term180 _25500 _25499 _25501.
Proof. exact (@lem1644996 _25500 _25499 h1 _25501). Qed.
Lemma lem1644998 (_25500 : real) (_25501 : real) (_25499 : nat) : (term180 _25500 _25499 _25501) = (term167 _25500 _25501 _25499).
Proof. exact (eq_refl (term180 _25500 _25499 _25501)). Qed.
Lemma lem1644999 (_25500 : real) (_25501 : real) (_25499 : nat) (h1 : term35) : term167 _25500 _25501 _25499.
Proof. exact (EQ_MP (@lem1644998 _25500 _25501 _25499) (@lem1644997 _25500 _25499 _25501 h1)). Qed.
Lemma lem1645012 (_25506 : nat) (h1 : term72) : term181 _25506.
Proof. exact (@lem1644902 h1 _25506). Qed.
Lemma lem1645013 (_25506 : nat) : (term181 _25506) = (term158 _25506).
Proof. exact (eq_refl (term181 _25506)). Qed.
Lemma lem1645014 (_25506 : nat) (h1 : term72) : term158 _25506.
Proof. exact (EQ_MP (@lem1645013 _25506) (@lem1645012 _25506 h1)). Qed.
Lemma lem1645015 (_25506 : nat) (_25507 : real) (h1 : term72) : term182 _25506 _25507.
Proof. exact (@lem1645014 _25506 h1 _25507). Qed.
Lemma lem1645016 (_25507 : real) (_25506 : nat) : (term182 _25506 _25507) = (term156 _25507 _25506).
Proof. exact (eq_refl (term182 _25506 _25507)). Qed.
Lemma lem1645017 (_25507 : real) (_25506 : nat) (h1 : term72) : term156 _25507 _25506.
Proof. exact (EQ_MP (@lem1645016 _25507 _25506) (@lem1645015 _25506 _25507 h1)). Qed.
Lemma lem1645018 (_25507 : real) (_25506 : nat) (_25508 : real) (h1 : term72) : term183 _25507 _25506 _25508.
Proof. exact (@lem1645017 _25507 _25506 h1 _25508). Qed.
Lemma lem1645019 (_25507 : real) (_25508 : real) (_25506 : nat) : (term183 _25507 _25506 _25508) = (term153 _25507 _25508 _25506).
Proof. exact (eq_refl (term183 _25507 _25506 _25508)). Qed.
Lemma lem1645020 (_25507 : real) (_25508 : real) (_25506 : nat) (h1 : term72) : term153 _25507 _25508 _25506.
Proof. exact (EQ_MP (@lem1645019 _25507 _25508 _25506) (@lem1645018 _25507 _25506 _25508 h1)). Qed.
Lemma lem1645021 (_25509 : real) (h1 : term65) : term177 _25509.
Proof. exact (@lem1644913 h1 _25509). Qed.
Lemma lem1645022 (_25509 : real) : (term177 _25509) = (term63 _25509).
Proof. exact (eq_refl (term177 _25509)). Qed.
Lemma lem1645033 (_25513 : real) (h1 : term77) : term122 _25513.
Proof. exact (@lem1644954 h1 _25513). Qed.
Lemma lem1645034 (_25513 : real) : (term122 _25513) = (term109 _25513).
Proof. exact (eq_refl (term122 _25513)). Qed.
Lemma lem1645035 (_25513 : real) (h1 : term77) : term109 _25513.
Proof. exact (EQ_MP (@lem1645034 _25513) (@lem1645033 _25513 h1)). Qed.
Lemma lem1645036 (_25513 : real) (_25514 : real) (h1 : term77) : term99 _25513 _25514.
Proof. exact (@lem1645035 _25513 h1 _25514). Qed.
Lemma lem1645037 (_25514 : real) (_25513 : real) : (term99 _25513 _25514) = (term100 _25514 _25513).
Proof. exact (eq_refl (term99 _25513 _25514)). Qed.
Lemma lem1645039 (_25515 : real) (h1 : term77) : term124 _25515.
Proof. exact (@lem1644970 h1 _25515). Qed.
Lemma lem1645040 (_25515 : real) : (term124 _25515) = (term114 _25515).
Proof. exact (eq_refl (term124 _25515)). Qed.
Lemma lem1645041 (_25515 : real) (h1 : term77) : term114 _25515.
Proof. exact (EQ_MP (@lem1645040 _25515) (@lem1645039 _25515 h1)). Qed.
Lemma lem1645042 (_25515 : real) (_25516 : real) (h1 : term77) : term102 _25515 _25516.
Proof. exact (@lem1645041 _25515 h1 _25516). Qed.
Lemma lem1645043 (_25516 : real) (_25515 : real) : (term102 _25515 _25516) = (term83 _25516 _25515).
Proof. exact (eq_refl (term102 _25515 _25516)). Qed.
Lemma lem1645077 (_25500 : real) (_25501 : real) (_25499 : nat) : (term167 _25500 _25501 _25499) = (term184 _25500 _25501 _25499).
Proof. exact (@lem1643640 (term185 _25500) (term73 _25500 _25501) (term163 _25500 _25501 _25499)). Qed.
Lemma lem1645078 (_25500 : real) (_25501 : real) (_25499 : nat) (h1 : term35) : term184 _25500 _25501 _25499.
Proof. exact (EQ_MP (@lem1645077 _25500 _25501 _25499) (@lem1644999 _25500 _25501 _25499 h1)). Qed.
Lemma lem1645094 (x : real) (y : real) (h1 : term175 x y) : term186 x y.
Proof. exact (proj2 (@lem1644759 x y h1)). Qed.
Lemma lem1645098 (_25507 : real) (_25508 : real) (_25506 : nat) : (term153 _25507 _25508 _25506) = (term187 _25507 _25508 _25506).
Proof. exact (@lem1643640 (_25506 = (NUMERAL 0)) (term140 _25507 _25508) (term149 _25507 _25508 _25506)). Qed.
Lemma lem1645105 (_25507 : real) (_25508 : real) (_25506 : nat) : (term188 _25507 _25508 _25506) = (term189 _25507 _25508 _25506).
Proof. exact (@lem1643640 (term185 _25507) (term190 _25507 _25508) (term149 _25507 _25508 _25506)). Qed.
Lemma lem1645106 (_25506 : nat) : (term143 _25506) = (term143 _25506).
Proof. exact (eq_refl (term143 _25506)). Qed.
Lemma lem1645109 (_25507 : real) (_25508 : real) (_25506 : nat) : (term187 _25507 _25508 _25506) = (term191 _25507 _25508 _25506).
Proof. exact (MK_COMB (@lem1645106 _25506) (@lem1645105 _25507 _25508 _25506)). Qed.
Lemma lem1645111 (_25507 : real) (_25508 : real) (_25506 : nat) : (term153 _25507 _25508 _25506) = (term191 _25507 _25508 _25506).
Proof. exact (TRANS (@lem1645098 _25507 _25508 _25506) (@lem1645109 _25507 _25508 _25506)). Qed.
Lemma lem1645112 (_25507 : real) (_25508 : real) (_25506 : nat) (h1 : term72) : term191 _25507 _25508 _25506.
Proof. exact (EQ_MP (@lem1645111 _25507 _25508 _25506) (@lem1645020 _25507 _25508 _25506 h1)). Qed.
Lemma lem1645114 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1645134 (_25514 : real) (_25513 : real) (h1 : term77) : term100 _25514 _25513.
Proof. exact (EQ_MP (@lem1645037 _25514 _25513) (@lem1645036 _25513 _25514 h1)). Qed.
Lemma lem1645140 (_25516 : real) (_25515 : real) (h1 : term77) : term83 _25516 _25515.
Proof. exact (EQ_MP (@lem1645043 _25516 _25515) (@lem1645042 _25515 _25516 h1)). Qed.
Lemma lem1645142 (x : real) (y : real) (h1 : term176 x y) : term192 x y.
Proof. exact (proj1 (@lem1644760 x y h1)). Qed.
Lemma lem1645243 (_25498 : real) (h1 : term65) : term63 _25498.
Proof. exact (EQ_MP (@lem1644989 _25498) (@lem1644988 _25498 h1)). Qed.
Lemma lem1645244 (x : real) (h1 : term65) : term63 x.
Proof. exact (@lem1645243 x h1). Qed.
Lemma lem1645245 (x : real) (h1 : term65) : term193 x.
Proof. exact (fun h0 : term194 x => @lem1645244 x h1). Qed.
Lemma lem1645247 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645248 (x : real) : (term193 x) = (term63 x).
Proof. exact (@lem1645247 (term63 x)). Qed.
Lemma lem1645249 (x : real) (h1 : term65) : term63 x.
Proof. exact (EQ_MP (@lem1645248 x) (@lem1645245 x h1)). Qed.
Lemma lem1645251 (x : real) (y : real) (h1 : term175 x y) : term22 x y.
Proof. exact (proj1 (@lem1644759 x y h1)). Qed.
Lemma lem1645252 (x : real) (y : real) (h1 : term175 x y) : term196 x y.
Proof. exact (fun h0 : term192 x y => @lem1645251 x y h1). Qed.
Lemma lem1645254 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645255 (x : real) (y : real) : (term196 x y) = (term22 x y).
Proof. exact (@lem1645254 (term22 x y)). Qed.
Lemma lem1645256 (x : real) (y : real) (h1 : term175 x y) : term22 x y.
Proof. exact (EQ_MP (@lem1645255 x y) (@lem1645252 x y h1)). Qed.
Lemma lem1645262 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645263 (_25500 : real) (_25501 : real) (_25499 : nat) : (term184 _25500 _25501 _25499) = (term197 _25500 _25501 _25499).
Proof. exact (@lem1645262 (term73 _25500 _25501) (term185 _25500) (term163 _25500 _25501 _25499)). Qed.
Lemma lem1645277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1645278 (_25501 : real) (_25499 : nat) (_25500 : real) : (term198 _25500 _25501 _25499) = (term199 _25501 _25499 _25500).
Proof. exact (@lem1645277 (term163 _25500 _25501 _25499) (term185 _25500)). Qed.
Lemma lem1645284 (_25500 : real) (_25501 : real) : (term200 _25500 _25501) = (term200 _25500 _25501).
Proof. exact (eq_refl (term200 _25500 _25501)). Qed.
Lemma lem1645285 (_25501 : real) (_25499 : nat) (_25500 : real) : (term197 _25500 _25501 _25499) = (term201 _25501 _25499 _25500).
Proof. exact (MK_COMB (@lem1645284 _25500 _25501) (@lem1645278 _25501 _25499 _25500)). Qed.
Lemma lem1645289 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645290 (_25499 : nat) (_25501 : real) (_25500 : real) : (term201 _25501 _25499 _25500) = (term202 _25499 _25501 _25500).
Proof. exact (@lem1645289 (term163 _25500 _25501 _25499) (term73 _25500 _25501) (term185 _25500)). Qed.
Lemma lem1645306 (_25499 : nat) (_25501 : real) (_25500 : real) : (term197 _25500 _25501 _25499) = (term202 _25499 _25501 _25500).
Proof. exact (TRANS (@lem1645285 _25501 _25499 _25500) (@lem1645290 _25499 _25501 _25500)). Qed.
Lemma lem1645307 (_25499 : nat) (_25501 : real) (_25500 : real) : (term184 _25500 _25501 _25499) = (term202 _25499 _25501 _25500).
Proof. exact (TRANS (@lem1645263 _25500 _25501 _25499) (@lem1645306 _25499 _25501 _25500)). Qed.
Lemma lem1645308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1645309 (_25499 : nat) (_25501 : real) (_25500 : real) : (term203 _25500 _25501 _25499) = (term204 _25499 _25501 _25500).
Proof. exact (MK_COMB (@lem1645308) (@lem1645307 _25499 _25501 _25500)). Qed.
Lemma lem1645323 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1645324 (_25501 : real) (_25500 : real) : (term162 _25500 _25501) = (term205 _25501 _25500).
Proof. exact (@lem1645323 (term73 _25500 _25501) (term185 _25500)). Qed.
Lemma lem1645330 (_25500 : real) (_25501 : real) (_25499 : nat) : (term206 _25500 _25501 _25499) = (term206 _25500 _25501 _25499).
Proof. exact (eq_refl (term206 _25500 _25501 _25499)). Qed.
Lemma lem1645331 (_25499 : nat) (_25501 : real) (_25500 : real) : (term207 _25499 _25500 _25501) = (term202 _25499 _25501 _25500).
Proof. exact (MK_COMB (@lem1645330 _25500 _25501 _25499) (@lem1645324 _25501 _25500)). Qed.
Lemma lem1645342 (_25499 : nat) (_25501 : real) (_25500 : real) : ((term184 _25500 _25501 _25499) = (term207 _25499 _25500 _25501)) = ((term202 _25499 _25501 _25500) = (term202 _25499 _25501 _25500)).
Proof. exact (MK_COMB (@lem1645309 _25499 _25501 _25500) (@lem1645331 _25499 _25501 _25500)). Qed.
Lemma lem1645344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1645345 (x : Prop) : (x = x) = True.
Proof. exact (@lem1645344 Prop x). Qed.
Lemma lem1645346 (_25499 : nat) (_25501 : real) (_25500 : real) : ((term202 _25499 _25501 _25500) = (term202 _25499 _25501 _25500)) = True.
Proof. exact (@lem1645345 (term202 _25499 _25501 _25500)). Qed.
Lemma lem1645347 (_25499 : nat) (_25500 : real) (_25501 : real) : ((term184 _25500 _25501 _25499) = (term207 _25499 _25500 _25501)) = True.
Proof. exact (TRANS (@lem1645342 _25499 _25501 _25500) (@lem1645346 _25499 _25501 _25500)). Qed.
Lemma lem1645348 (_25499 : nat) (_25500 : real) (_25501 : real) : True = ((term184 _25500 _25501 _25499) = (term207 _25499 _25500 _25501)).
Proof. exact (SYM (@lem1645347 _25499 _25500 _25501)). Qed.
Lemma lem1645349 (_25499 : nat) (_25500 : real) (_25501 : real) : (term184 _25500 _25501 _25499) = (term207 _25499 _25500 _25501).
Proof. exact (EQ_MP (@lem1645348 _25499 _25500 _25501) (@lem0)). Qed.
Lemma lem1645350 (_25499 : nat) (_25500 : real) (_25501 : real) (h1 : term35) : term207 _25499 _25500 _25501.
Proof. exact (EQ_MP (@lem1645349 _25499 _25500 _25501) (@lem1645078 _25500 _25501 _25499 h1)). Qed.
Lemma lem1645352 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1645353 (_25500 : real) (_25501 : real) (_25499 : nat) : (term207 _25499 _25500 _25501) = (term209 _25500 _25501 _25499).
Proof. exact (@lem1645352 (term162 _25500 _25501) (term163 _25500 _25501 _25499)). Qed.
Lemma lem1645355 (a : Prop) (b : Prop) : (term210 a b) = (term211 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1645356 (_25500 : real) (_25501 : real) : (term212 _25500 _25501) = (term213 _25500 _25501).
Proof. exact (@lem1645355 (term185 _25500) (term73 _25500 _25501)). Qed.
Lemma lem1645358 (a : Prop) : (term214 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1645359 (_25500 : real) : (term215 _25500) = (term141 _25500).
Proof. exact (@lem1645358 (term141 _25500)). Qed.
Lemma lem1645360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1645361 (_25500 : real) : (term216 _25500) = (term217 _25500).
Proof. exact (MK_COMB (@lem1645360) (@lem1645359 _25500)). Qed.
Lemma lem1645363 (a : Prop) : (term214 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1645364 (_25500 : real) (_25501 : real) : (term79 _25500 _25501) = (real_le _25500 _25501).
Proof. exact (@lem1645363 (real_le _25500 _25501)). Qed.
Lemma lem1645365 (_25500 : real) (_25501 : real) : (term213 _25500 _25501) = (term168 _25500 _25501).
Proof. exact (MK_COMB (@lem1645361 _25500) (@lem1645364 _25500 _25501)). Qed.
Lemma lem1645366 (_25500 : real) (_25501 : real) : (term212 _25500 _25501) = (term168 _25500 _25501).
Proof. exact (TRANS (@lem1645356 _25500 _25501) (@lem1645365 _25500 _25501)). Qed.
Lemma lem1645367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1645368 (_25500 : real) (_25501 : real) : (term218 _25500 _25501) = (term219 _25500 _25501).
Proof. exact (MK_COMB (@lem1645367) (@lem1645366 _25500 _25501)). Qed.
Lemma lem1645369 (_25500 : real) (_25501 : real) (_25499 : nat) : (term163 _25500 _25501 _25499) = (term163 _25500 _25501 _25499).
Proof. exact (eq_refl (term163 _25500 _25501 _25499)). Qed.
Lemma lem1645370 (_25500 : real) (_25501 : real) (_25499 : nat) : (term209 _25500 _25501 _25499) = (term57 _25500 _25501 _25499).
Proof. exact (MK_COMB (@lem1645368 _25500 _25501) (@lem1645369 _25500 _25501 _25499)). Qed.
Lemma lem1645371 (_25500 : real) (_25501 : real) (_25499 : nat) : (term207 _25499 _25500 _25501) = (term57 _25500 _25501 _25499).
Proof. exact (TRANS (@lem1645353 _25500 _25501 _25499) (@lem1645370 _25500 _25501 _25499)). Qed.
Lemma lem1645373 (x : real) (y : real) (h1 : term65) (h2 : term175 x y) : term220 x y.
Proof. exact (conj (@lem1645249 x h1) (@lem1645256 x y h2)). Qed.
Lemma lem1645375 (_25500 : real) (_25501 : real) (_25499 : nat) (h1 : term35) : term57 _25500 _25501 _25499.
Proof. exact (EQ_MP (@lem1645371 _25500 _25501 _25499) (@lem1645350 _25499 _25500 _25501 h1)). Qed.
Lemma lem1645376 (x : real) (y : real) (_25499 : nat) (h1 : term35) : term221 x y _25499.
Proof. exact (@lem1645375 (real_abs x) (real_abs y) _25499 h1). Qed.
Lemma lem1645379 (_25499 : nat) (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term222 x y _25499.
Proof. exact (@lem1645376 x y _25499 h1 (@lem1645373 x y h2 h3)). Qed.
Lemma lem1645380 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term20 x y.
Proof. exact (@lem1645379 term2 x y h1 h2 h3). Qed.
Lemma lem1645381 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term223 x y.
Proof. exact (fun h0 : term186 x y => @lem1645380 x y h1 h2 h3). Qed.
Lemma lem1645383 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645384 (x : real) (y : real) : (term223 x y) = (term20 x y).
Proof. exact (@lem1645383 (term20 x y)). Qed.
Lemma lem1645385 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term20 x y.
Proof. exact (EQ_MP (@lem1645384 x y) (@lem1645381 x y h1 h2 h3)). Qed.
Lemma lem1645388 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1645390 (x : real) (y : real) : (term186 x y) = (term224 x y).
Proof. exact (@lem1645388 (term20 x y)). Qed.
Lemma lem1645393 (x : real) (y : real) (h1 : term175 x y) : term224 x y.
Proof. exact (EQ_MP (@lem1645390 x y) (@lem1645094 x y h1)). Qed.
Lemma lem1645396 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : False.
Proof. exact (@lem1645393 x y h3 (@lem1645385 x y h1 h2 h3)). Qed.
Lemma lem1645397 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term225.
Proof. exact (fun h0 : ~ False => @lem1645396 x y h1 h2 h3). Qed.
Lemma lem1645399 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645400 : term225 = False.
Proof. exact (@lem1645399 False). Qed.
Lemma lem1645401 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : False.
Proof. exact (EQ_MP (@lem1645400) (@lem1645397 x y h1 h2 h3)). Qed.
Lemma lem1645500 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1645501 (h1 : term30) : term226.
Proof. exact (fun h0 : term2 = (NUMERAL 0) => @lem1645500 h1). Qed.
Lemma lem1645503 (p : Prop) : (term227 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1645504 : term226 = term30.
Proof. exact (@lem1645503 (term2 = (NUMERAL 0))). Qed.
Lemma lem1645505 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1645504) (@lem1645501 h1)). Qed.
Lemma lem1645507 (_25509 : real) (h1 : term65) : term63 _25509.
Proof. exact (EQ_MP (@lem1645022 _25509) (@lem1645021 _25509 h1)). Qed.
Lemma lem1645508 (y : real) (h1 : term65) : term63 y.
Proof. exact (@lem1645507 y h1). Qed.
Lemma lem1645509 (y : real) (h1 : term65) : term193 y.
Proof. exact (fun h0 : term194 y => @lem1645508 y h1). Qed.
Lemma lem1645511 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645512 (y : real) : (term193 y) = (term63 y).
Proof. exact (@lem1645511 (term63 y)). Qed.
Lemma lem1645513 (y : real) (h1 : term65) : term63 y.
Proof. exact (EQ_MP (@lem1645512 y) (@lem1645509 y h1)). Qed.
Lemma lem1645515 (x : real) (y : real) (h1 : term176 x y) : term20 x y.
Proof. exact (proj2 (@lem1644760 x y h1)). Qed.
Lemma lem1645516 (x : real) (y : real) (h1 : term176 x y) : term223 x y.
Proof. exact (fun h0 : term186 x y => @lem1645515 x y h1). Qed.
Lemma lem1645518 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645519 (x : real) (y : real) : (term223 x y) = (term20 x y).
Proof. exact (@lem1645518 (term20 x y)). Qed.
Lemma lem1645520 (x : real) (y : real) (h1 : term176 x y) : term20 x y.
Proof. exact (EQ_MP (@lem1645519 x y) (@lem1645516 x y h1)). Qed.
Lemma lem1645531 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1645532 (_25514 : real) (_25513 : real) : (term228 _25513 _25514) = (term100 _25514 _25513).
Proof. exact (@lem1645531 (term73 _25513 _25514) (term190 _25514 _25513)). Qed.
Lemma lem1645538 (_25514 : real) (_25513 : real) : (term229 _25514 _25513) = (term229 _25514 _25513).
Proof. exact (eq_refl (term229 _25514 _25513)). Qed.
Lemma lem1645539 (_25514 : real) (_25513 : real) : ((term100 _25514 _25513) = (term228 _25513 _25514)) = ((term100 _25514 _25513) = (term100 _25514 _25513)).
Proof. exact (MK_COMB (@lem1645538 _25514 _25513) (@lem1645532 _25514 _25513)). Qed.
Lemma lem1645541 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1645542 (x : Prop) : (x = x) = True.
Proof. exact (@lem1645541 Prop x). Qed.
Lemma lem1645543 (_25514 : real) (_25513 : real) : ((term100 _25514 _25513) = (term100 _25514 _25513)) = True.
Proof. exact (@lem1645542 (term100 _25514 _25513)). Qed.
Lemma lem1645544 (_25513 : real) (_25514 : real) : ((term100 _25514 _25513) = (term228 _25513 _25514)) = True.
Proof. exact (TRANS (@lem1645539 _25514 _25513) (@lem1645543 _25514 _25513)). Qed.
Lemma lem1645545 (_25513 : real) (_25514 : real) : True = ((term100 _25514 _25513) = (term228 _25513 _25514)).
Proof. exact (SYM (@lem1645544 _25513 _25514)). Qed.
Lemma lem1645546 (_25513 : real) (_25514 : real) : (term100 _25514 _25513) = (term228 _25513 _25514).
Proof. exact (EQ_MP (@lem1645545 _25513 _25514) (@lem0)). Qed.
Lemma lem1645547 (_25513 : real) (_25514 : real) (h1 : term77) : term228 _25513 _25514.
Proof. exact (EQ_MP (@lem1645546 _25513 _25514) (@lem1645134 _25514 _25513 h1)). Qed.
Lemma lem1645549 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1645550 (_25514 : real) (_25513 : real) : (term228 _25513 _25514) = (term230 _25514 _25513).
Proof. exact (@lem1645549 (term73 _25513 _25514) (term190 _25514 _25513)). Qed.
Lemma lem1645552 (a : Prop) : (term214 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1645553 (_25513 : real) (_25514 : real) : (term79 _25513 _25514) = (real_le _25513 _25514).
Proof. exact (@lem1645552 (real_le _25513 _25514)). Qed.
Lemma lem1645554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1645555 (_25513 : real) (_25514 : real) : (term231 _25513 _25514) = (term232 _25513 _25514).
Proof. exact (MK_COMB (@lem1645554) (@lem1645553 _25513 _25514)). Qed.
Lemma lem1645556 (_25514 : real) (_25513 : real) : (term190 _25514 _25513) = (term190 _25514 _25513).
Proof. exact (eq_refl (term190 _25514 _25513)). Qed.
Lemma lem1645557 (_25514 : real) (_25513 : real) : (term230 _25514 _25513) = (term233 _25514 _25513).
Proof. exact (MK_COMB (@lem1645555 _25513 _25514) (@lem1645556 _25514 _25513)). Qed.
Lemma lem1645558 (_25514 : real) (_25513 : real) : (term228 _25513 _25514) = (term233 _25514 _25513).
Proof. exact (TRANS (@lem1645550 _25514 _25513) (@lem1645557 _25514 _25513)). Qed.
Lemma lem1645561 (_25514 : real) (_25513 : real) (h1 : term77) : term233 _25514 _25513.
Proof. exact (EQ_MP (@lem1645558 _25514 _25513) (@lem1645547 _25513 _25514 h1)). Qed.
Lemma lem1645562 (y : real) (x : real) (h1 : term77) : term234 y x.
Proof. exact (@lem1645561 (term10 y) (term10 x) h1). Qed.
Lemma lem1645565 (x : real) (y : real) (h1 : term77) (h2 : term176 x y) : term235 y x.
Proof. exact (@lem1645562 y x h1 (@lem1645520 x y h2)). Qed.
Lemma lem1645566 (x : real) (y : real) (h1 : term77) (h2 : term176 x y) : term236 y x.
Proof. exact (fun h0 : term237 y x => @lem1645565 x y h1 h2). Qed.
Lemma lem1645568 (p : Prop) : (term227 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1645569 (y : real) (x : real) : (term236 y x) = (term235 y x).
Proof. exact (@lem1645568 (term237 y x)). Qed.
Lemma lem1645570 (x : real) (y : real) (h1 : term77) (h2 : term176 x y) : term235 y x.
Proof. exact (EQ_MP (@lem1645569 y x) (@lem1645566 x y h1 h2)). Qed.
Lemma lem1645598 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1645599 (_25506 : nat) (_25507 : real) (_25508 : real) : (term238 _25507 _25508 _25506) = (term239 _25506 _25507 _25508).
Proof. exact (@lem1645598 (term149 _25507 _25508 _25506) (term190 _25507 _25508)). Qed.
Lemma lem1645605 (_25507 : real) : (term240 _25507) = (term240 _25507).
Proof. exact (eq_refl (term240 _25507)). Qed.
Lemma lem1645606 (_25506 : nat) (_25507 : real) (_25508 : real) : (term189 _25507 _25508 _25506) = (term241 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645605 _25507) (@lem1645599 _25506 _25507 _25508)). Qed.
Lemma lem1645610 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645611 (_25506 : nat) (_25507 : real) (_25508 : real) : (term241 _25506 _25507 _25508) = (term242 _25506 _25507 _25508).
Proof. exact (@lem1645610 (term149 _25507 _25508 _25506) (term185 _25507) (term190 _25507 _25508)). Qed.
Lemma lem1645627 (_25506 : nat) (_25507 : real) (_25508 : real) : (term189 _25507 _25508 _25506) = (term242 _25506 _25507 _25508).
Proof. exact (TRANS (@lem1645606 _25506 _25507 _25508) (@lem1645611 _25506 _25507 _25508)). Qed.
Lemma lem1645628 (_25506 : nat) : (term143 _25506) = (term143 _25506).
Proof. exact (eq_refl (term143 _25506)). Qed.
Lemma lem1645629 (_25506 : nat) (_25507 : real) (_25508 : real) : (term191 _25507 _25508 _25506) = (term243 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645628 _25506) (@lem1645627 _25506 _25507 _25508)). Qed.
Lemma lem1645640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1645641 (_25506 : nat) (_25507 : real) (_25508 : real) : (term244 _25507 _25508 _25506) = (term245 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645640) (@lem1645629 _25506 _25507 _25508)). Qed.
Lemma lem1645645 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645646 (_25507 : real) (_25508 : real) (_25506 : nat) : (term246 _25507 _25508 _25506) = (term247 _25507 _25508 _25506).
Proof. exact (@lem1645645 (_25506 = (NUMERAL 0)) (term190 _25507 _25508) (term248 _25507 _25508 _25506)). Qed.
Lemma lem1645662 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645663 (_25507 : real) (_25508 : real) (_25506 : nat) : (term249 _25507 _25508 _25506) = (term189 _25507 _25508 _25506).
Proof. exact (@lem1645662 (term185 _25507) (term190 _25507 _25508) (term149 _25507 _25508 _25506)). Qed.
Lemma lem1645677 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1645678 (_25506 : nat) (_25507 : real) (_25508 : real) : (term238 _25507 _25508 _25506) = (term239 _25506 _25507 _25508).
Proof. exact (@lem1645677 (term149 _25507 _25508 _25506) (term190 _25507 _25508)). Qed.
Lemma lem1645684 (_25507 : real) : (term240 _25507) = (term240 _25507).
Proof. exact (eq_refl (term240 _25507)). Qed.
Lemma lem1645685 (_25506 : nat) (_25507 : real) (_25508 : real) : (term189 _25507 _25508 _25506) = (term241 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645684 _25507) (@lem1645678 _25506 _25507 _25508)). Qed.
Lemma lem1645689 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1645690 (_25506 : nat) (_25507 : real) (_25508 : real) : (term241 _25506 _25507 _25508) = (term242 _25506 _25507 _25508).
Proof. exact (@lem1645689 (term149 _25507 _25508 _25506) (term185 _25507) (term190 _25507 _25508)). Qed.
Lemma lem1645706 (_25506 : nat) (_25507 : real) (_25508 : real) : (term189 _25507 _25508 _25506) = (term242 _25506 _25507 _25508).
Proof. exact (TRANS (@lem1645685 _25506 _25507 _25508) (@lem1645690 _25506 _25507 _25508)). Qed.
Lemma lem1645707 (_25506 : nat) (_25507 : real) (_25508 : real) : (term249 _25507 _25508 _25506) = (term242 _25506 _25507 _25508).
Proof. exact (TRANS (@lem1645663 _25507 _25508 _25506) (@lem1645706 _25506 _25507 _25508)). Qed.
Lemma lem1645708 (_25506 : nat) : (term143 _25506) = (term143 _25506).
Proof. exact (eq_refl (term143 _25506)). Qed.
Lemma lem1645709 (_25506 : nat) (_25507 : real) (_25508 : real) : (term247 _25507 _25508 _25506) = (term243 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645708 _25506) (@lem1645707 _25506 _25507 _25508)). Qed.
Lemma lem1645720 (_25506 : nat) (_25507 : real) (_25508 : real) : (term246 _25507 _25508 _25506) = (term243 _25506 _25507 _25508).
Proof. exact (TRANS (@lem1645646 _25507 _25508 _25506) (@lem1645709 _25506 _25507 _25508)). Qed.
Lemma lem1645721 (_25506 : nat) (_25507 : real) (_25508 : real) : ((term191 _25507 _25508 _25506) = (term246 _25507 _25508 _25506)) = ((term243 _25506 _25507 _25508) = (term243 _25506 _25507 _25508)).
Proof. exact (MK_COMB (@lem1645641 _25506 _25507 _25508) (@lem1645720 _25506 _25507 _25508)). Qed.
Lemma lem1645723 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1645724 (x : Prop) : (x = x) = True.
Proof. exact (@lem1645723 Prop x). Qed.
Lemma lem1645725 (_25506 : nat) (_25507 : real) (_25508 : real) : ((term243 _25506 _25507 _25508) = (term243 _25506 _25507 _25508)) = True.
Proof. exact (@lem1645724 (term243 _25506 _25507 _25508)). Qed.
Lemma lem1645726 (_25507 : real) (_25508 : real) (_25506 : nat) : ((term191 _25507 _25508 _25506) = (term246 _25507 _25508 _25506)) = True.
Proof. exact (TRANS (@lem1645721 _25506 _25507 _25508) (@lem1645725 _25506 _25507 _25508)). Qed.
Lemma lem1645727 (_25507 : real) (_25508 : real) (_25506 : nat) : True = ((term191 _25507 _25508 _25506) = (term246 _25507 _25508 _25506)).
Proof. exact (SYM (@lem1645726 _25507 _25508 _25506)). Qed.
Lemma lem1645728 (_25507 : real) (_25508 : real) (_25506 : nat) : (term191 _25507 _25508 _25506) = (term246 _25507 _25508 _25506).
Proof. exact (EQ_MP (@lem1645727 _25507 _25508 _25506) (@lem0)). Qed.
Lemma lem1645729 (_25507 : real) (_25508 : real) (_25506 : nat) (h1 : term72) : term246 _25507 _25508 _25506.
Proof. exact (EQ_MP (@lem1645728 _25507 _25508 _25506) (@lem1645112 _25507 _25508 _25506 h1)). Qed.
Lemma lem1645731 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1645732 (_25506 : nat) (_25507 : real) (_25508 : real) : (term246 _25507 _25508 _25506) = (term250 _25506 _25507 _25508).
Proof. exact (@lem1645731 (term251 _25507 _25508 _25506) (term190 _25507 _25508)). Qed.
Lemma lem1645734 (a : Prop) (b : Prop) : (term210 a b) = (term211 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1645735 (_25507 : real) (_25508 : real) (_25506 : nat) : (term252 _25507 _25508 _25506) = (term253 _25507 _25508 _25506).
Proof. exact (@lem1645734 (_25506 = (NUMERAL 0)) (term248 _25507 _25508 _25506)). Qed.
Lemma lem1645737 (a : Prop) (b : Prop) : (term210 a b) = (term211 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1645738 (_25507 : real) (_25508 : real) (_25506 : nat) : (term254 _25507 _25508 _25506) = (term255 _25507 _25508 _25506).
Proof. exact (@lem1645737 (term185 _25507) (term149 _25507 _25508 _25506)). Qed.
Lemma lem1645740 (a : Prop) : (term214 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1645741 (_25507 : real) : (term215 _25507) = (term141 _25507).
Proof. exact (@lem1645740 (term141 _25507)). Qed.
Lemma lem1645742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1645743 (_25507 : real) : (term216 _25507) = (term217 _25507).
Proof. exact (MK_COMB (@lem1645742) (@lem1645741 _25507)). Qed.
Lemma lem1645744 (_25507 : real) (_25508 : real) (_25506 : nat) : (term256 _25507 _25508 _25506) = (term256 _25507 _25508 _25506).
Proof. exact (eq_refl (term256 _25507 _25508 _25506)). Qed.
Lemma lem1645745 (_25507 : real) (_25508 : real) (_25506 : nat) : (term255 _25507 _25508 _25506) = (term257 _25507 _25508 _25506).
Proof. exact (MK_COMB (@lem1645743 _25507) (@lem1645744 _25507 _25508 _25506)). Qed.
Lemma lem1645746 (_25507 : real) (_25508 : real) (_25506 : nat) : (term254 _25507 _25508 _25506) = (term257 _25507 _25508 _25506).
Proof. exact (TRANS (@lem1645738 _25507 _25508 _25506) (@lem1645745 _25507 _25508 _25506)). Qed.
Lemma lem1645747 (_25506 : nat) : (term258 _25506) = (term258 _25506).
Proof. exact (eq_refl (term258 _25506)). Qed.
Lemma lem1645748 (_25507 : real) (_25508 : real) (_25506 : nat) : (term253 _25507 _25508 _25506) = (term259 _25507 _25508 _25506).
Proof. exact (MK_COMB (@lem1645747 _25506) (@lem1645746 _25507 _25508 _25506)). Qed.
Lemma lem1645749 (_25507 : real) (_25508 : real) (_25506 : nat) : (term252 _25507 _25508 _25506) = (term259 _25507 _25508 _25506).
Proof. exact (TRANS (@lem1645735 _25507 _25508 _25506) (@lem1645748 _25507 _25508 _25506)). Qed.
Lemma lem1645750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1645751 (_25507 : real) (_25508 : real) (_25506 : nat) : (term260 _25507 _25508 _25506) = (term261 _25507 _25508 _25506).
Proof. exact (MK_COMB (@lem1645750) (@lem1645749 _25507 _25508 _25506)). Qed.
Lemma lem1645752 (_25507 : real) (_25508 : real) : (term190 _25507 _25508) = (term190 _25507 _25508).
Proof. exact (eq_refl (term190 _25507 _25508)). Qed.
Lemma lem1645753 (_25506 : nat) (_25507 : real) (_25508 : real) : (term250 _25506 _25507 _25508) = (term262 _25506 _25507 _25508).
Proof. exact (MK_COMB (@lem1645751 _25507 _25508 _25506) (@lem1645752 _25507 _25508)). Qed.
Lemma lem1645754 (_25506 : nat) (_25507 : real) (_25508 : real) : (term246 _25507 _25508 _25506) = (term262 _25506 _25507 _25508).
Proof. exact (TRANS (@lem1645732 _25506 _25507 _25508) (@lem1645753 _25506 _25507 _25508)). Qed.
Lemma lem1645756 (x : real) (y : real) (h1 : term77) (h2 : term65) (h3 : term176 x y) : term263 y x.
Proof. exact (conj (@lem1645513 y h2) (@lem1645570 x y h1 h3)). Qed.
Lemma lem1645757 (x : real) (y : real) (h1 : term77) (h2 : term65) (h3 : term30) (h4 : term176 x y) : term264 y x.
Proof. exact (conj (@lem1645505 h3) (@lem1645756 x y h1 h2 h4)). Qed.
Lemma lem1645759 (_25506 : nat) (_25507 : real) (_25508 : real) (h1 : term72) : term262 _25506 _25507 _25508.
Proof. exact (EQ_MP (@lem1645754 _25506 _25507 _25508) (@lem1645729 _25507 _25508 _25506 h1)). Qed.
Lemma lem1645760 (y : real) (x : real) (h1 : term72) : term265 y x.
Proof. exact (@lem1645759 term2 (real_abs y) (real_abs x) h1). Qed.
Lemma lem1645763 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term266 y x.
Proof. exact (@lem1645760 y x h1 (@lem1645757 x y h2 h3 h4 h5)). Qed.
Lemma lem1645764 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term267 y x.
Proof. exact (fun h0 : term268 y x => @lem1645763 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1645766 (p : Prop) : (term227 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1645767 (y : real) (x : real) : (term267 y x) = (term266 y x).
Proof. exact (@lem1645766 (term268 y x)). Qed.
Lemma lem1645768 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term266 y x.
Proof. exact (EQ_MP (@lem1645767 y x) (@lem1645764 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645770 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1645773 (_25515 : real) (_25516 : real) : (term83 _25516 _25515) = (term269 _25515 _25516).
Proof. exact (@lem1645770 (real_lt _25516 _25515) (real_le _25515 _25516)). Qed.
Lemma lem1645776 (_25515 : real) (_25516 : real) (h1 : term77) : term269 _25515 _25516.
Proof. exact (EQ_MP (@lem1645773 _25515 _25516) (@lem1645140 _25516 _25515 h1)). Qed.
Lemma lem1645777 (x : real) (y : real) (h1 : term77) : term270 x y.
Proof. exact (@lem1645776 (real_abs x) (real_abs y) h1). Qed.
Lemma lem1645780 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term22 x y.
Proof. exact (@lem1645777 x y h2 (@lem1645768 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645781 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term196 x y.
Proof. exact (fun h0 : term192 x y => @lem1645780 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1645783 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645784 (x : real) (y : real) : (term196 x y) = (term22 x y).
Proof. exact (@lem1645783 (term22 x y)). Qed.
Lemma lem1645785 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term22 x y.
Proof. exact (EQ_MP (@lem1645784 x y) (@lem1645781 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645788 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1645790 (x : real) (y : real) : (term192 x y) = (term271 x y).
Proof. exact (@lem1645788 (term22 x y)). Qed.
Lemma lem1645793 (x : real) (y : real) (h1 : term176 x y) : term271 x y.
Proof. exact (EQ_MP (@lem1645790 x y) (@lem1645142 x y h1)). Qed.
Lemma lem1645796 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (@lem1645793 x y h5 (@lem1645785 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645797 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term225.
Proof. exact (fun h0 : ~ False => @lem1645796 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1645799 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1645800 : term225 = False.
Proof. exact (@lem1645799 False). Qed.
Lemma lem1645801 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (EQ_MP (@lem1645800) (@lem1645797 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645802 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term30 = False.
Proof. exact (prop_ext (fun h6 : term30 => @lem1645801 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1645114 h4)). Qed.
Lemma lem1645803 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (EQ_MP (@lem1645802 x y h1 h2 h3 h4 h5) (@lem1645114 h4)). Qed.
Lemma lem1645804 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term30 = False.
Proof. exact (prop_ext (fun h6 : term30 => @lem1645803 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1644906 h4)). Qed.
Lemma lem1645805 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (EQ_MP (@lem1645804 x y h1 h2 h3 h4 h5) (@lem1644906 h4)). Qed.
Lemma lem1645806 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term65 = False.
Proof. exact (prop_ext (fun h6 : term65 => @lem1645805 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1644913 h3)). Qed.
Lemma lem1645807 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (EQ_MP (@lem1645806 x y h1 h2 h3 h4 h5) (@lem1644913 h3)). Qed.
Lemma lem1645808 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : term30 = False.
Proof. exact (prop_ext (fun h6 : term30 => @lem1645807 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1644906 h4)). Qed.
Lemma lem1645809 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term30) (h5 : term176 x y) : False.
Proof. exact (EQ_MP (@lem1645808 x y h1 h2 h3 h4 h5) (@lem1644906 h4)). Qed.
Lemma lem1645810 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : term65 = False.
Proof. exact (prop_ext (fun h4 : term65 => @lem1645401 x y h1 h2 h3) (fun h4 : False => @lem1644806 h2)). Qed.
Lemma lem1645811 (x : real) (y : real) (h1 : term35) (h2 : term65) (h3 : term175 x y) : False.
Proof. exact (EQ_MP (@lem1645810 x y h1 h2 h3) (@lem1644806 h2)). Qed.
Lemma lem1645812 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : False.
Proof. exact (or_elim (@lem1644575 x y h5) (fun h0 : term175 x y => @lem1645811 x y h2 h4 h0) (fun h0 : term176 x y => @lem1645809 x y h1 h3 h4 h6 h0)). Qed.
Lemma lem1645813 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : term65 = False.
Proof. exact (prop_ext (fun h7 : term65 => @lem1645812 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1644709 h4)). Qed.
Lemma lem1645814 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : False.
Proof. exact (EQ_MP (@lem1645813 x y h1 h2 h3 h4 h5 h6) (@lem1644709 h4)). Qed.
Lemma lem1645815 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : term30 = False.
Proof. exact (prop_ext (fun h7 : term30 => @lem1645814 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1644694 h6)). Qed.
Lemma lem1645816 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : False.
Proof. exact (EQ_MP (@lem1645815 x y h1 h2 h3 h4 h5 h6) (@lem1644694 h6)). Qed.
Lemma lem1645817 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : term65 = False.
Proof. exact (prop_ext (fun h7 : term65 => @lem1645816 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1644402 h4)). Qed.
Lemma lem1645818 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : False.
Proof. exact (EQ_MP (@lem1645817 x y h1 h2 h3 h4 h5 h6) (@lem1644402 h4)). Qed.
Lemma lem1645819 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : term30 = False.
Proof. exact (prop_ext (fun h7 : term30 => @lem1645818 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1644389 h6)). Qed.
Lemma lem1645820 (x : real) (y : real) (h1 : term72) (h2 : term35) (h3 : term77) (h4 : term65) (h5 : term25 x y) (h6 : term30) : False.
Proof. exact (EQ_MP (@lem1645819 x y h1 h2 h3 h4 h5 h6) (@lem1644389 h6)). Qed.
Lemma lem1645821 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term25 x y) (h5 : term30) : term33.
Proof. exact (fun h0 : term35 => @lem1645820 x y h1 h0 h2 h3 h4 h5). Qed.
Lemma lem1645822 : term33 = term34.
Proof. exact (@lem69 term35). Qed.
Lemma lem1645823 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term65) (h4 : term25 x y) (h5 : term30) : term34.
Proof. exact (EQ_MP (@lem1645822) (@lem1645821 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1645824 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term25 x y) (h4 : term30) : term38.
Proof. exact (fun h0 : term65 => @lem1645823 x y h1 h2 h0 h3 h4). Qed.
Lemma lem1645825 (x : real) (y : real) (h1 : term72) (h2 : term77) (h3 : term25 x y) : term40.
Proof. exact (fun h0 : term30 => @lem1645824 x y h1 h2 h3 h0). Qed.
Lemma lem1645826 (x : real) (y : real) (h1 : term77) (h2 : term25 x y) : term43.
Proof. exact (fun h0 : term72 => @lem1645825 x y h0 h1 h2). Qed.
Lemma lem1645827 (x : real) (y : real) (h1 : term25 x y) : term46.
Proof. exact (fun h0 : term77 => @lem1645826 x y h0 h1). Qed.
Lemma lem1645828 (x : real) (y : real) : term48 x y.
Proof. exact (fun h0 : term25 x y => @lem1645827 x y h0). Qed.
Lemma lem1645833 (y : real) : term52 y.
Proof. exact (fun x : real => @lem1645828 x y). Qed.
Lemma lem1645838 : term56.
Proof. exact (fun y : real => @lem1645833 y). Qed.
Lemma lem1645839 : term55.
Proof. exact (EQ_MP (@lem1643977) (@lem1645838)). Qed.
Lemma lem1645840 (y : real) : term272 y.
Proof. exact (@lem1645839 y). Qed.
Lemma lem1645841 (y : real) : (term272 y) = (term51 y).
Proof. exact (eq_refl (term272 y)). Qed.
Lemma lem1645842 (y : real) : term51 y.
Proof. exact (EQ_MP (@lem1645841 y) (@lem1645840 y)). Qed.
Lemma lem1645843 (y : real) (x : real) : term273 y x.
Proof. exact (@lem1645842 y x). Qed.
Lemma lem1645844 (x : real) (y : real) : (term273 y x) = (term26 x y).
Proof. exact (eq_refl (term273 y x)). Qed.
Lemma lem1645845 (x : real) (y : real) : term26 x y.
Proof. exact (EQ_MP (@lem1645844 x y) (@lem1645843 y x)). Qed.
Lemma lem1645847 (x : real) (y : real) : term26 x y.
Proof. exact (@lem1643686 x y (@lem1645845 x y)). Qed.
Lemma lem1645848 (x : real) (y : real) (h1 : term25 x y) : term45.
Proof. exact (@lem1645847 x y (@lem1643671 x y h1)). Qed.
Lemma lem1645849 (x : real) (y : real) (h1 : term25 x y) : term42.
Proof. exact (@lem1645848 x y h1 (@lem1495933)). Qed.
Lemma lem1645850 (x : real) (y : real) (h1 : term25 x y) : term39.
Proof. exact (@lem1645849 x y h1 (@lem1638321)). Qed.
Lemma lem1645851 (x : real) (y : real) (h1 : term25 x y) : term37.
Proof. exact (@lem1645850 x y h1 (@lem1643630)). Qed.
Lemma lem1645852 (x : real) (y : real) (h1 : term25 x y) : term33.
Proof. exact (@lem1645851 x y h1 (@lem1532076)). Qed.
Lemma lem1645853 (x : real) (y : real) (h1 : term25 x y) : False.
Proof. exact (@lem1645852 x y h1 (@lem1636714)). Qed.
Lemma lem1645854 (x : real) (y : real) (h1 : term25 x y) : (term25 x y) = False.
Proof. exact (prop_ext (fun h2 : term25 x y => @lem1645853 x y h1) (fun h2 : False => @lem1643671 x y h1)). Qed.
Lemma lem1645855 (x : real) (y : real) (h1 : term25 x y) : False.
Proof. exact (EQ_MP (@lem1645854 x y h1) (@lem1643671 x y h1)). Qed.
Lemma lem1645856 (x : real) (y : real) : term24 x y.
Proof. exact (fun h0 : term25 x y => @lem1645855 x y h0). Qed.
Lemma lem1645857 (x : real) (y : real) : (term22 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem1643670 x y) (@lem1645856 x y)). Qed.
Lemma lem1645858 (x : real) (y : real) : (term22 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem1643666 x y) (@lem1645857 x y)). Qed.
Lemma lem1645863 (x : real) : term274 x.
Proof. exact (fun y : real => @lem1645858 x y). Qed.
Lemma lem1645868 : term275.
Proof. exact (fun x : real => @lem1645863 x). Qed.
