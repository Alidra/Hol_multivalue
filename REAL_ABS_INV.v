Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_INV_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_MUL_RINV_spec.
Require Import REAL_MUL_RINV_UNIQ_spec.
Require Import TREAL_INV_0_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm1528207_spec.
Require Import thm1528208_spec.
Require Import thm1528530_spec.
Require Import thm1528531_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1594666 (x : real) : term0 x.
Proof. exact (@lem1591985 x). Qed.
Lemma lem1594667 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1594671 (x : real) (y : real) (h1 : (term2 x y) = (term3 x y)) : (term2 x y) = (term3 x y).
Proof. exact (h1). Qed.
Lemma lem1594672 (x : real) (y : real) (h1 : (term2 x y) = (term3 x y)) : (term3 x y) = (term2 x y).
Proof. exact (SYM (@lem1594671 x y h1)). Qed.
Lemma lem1594673 (x : real) (y : real) (h1 : (term3 x y) = (term2 x y)) : (term3 x y) = (term2 x y).
Proof. exact (h1). Qed.
Lemma lem1594674 (x : real) (y : real) (h1 : (term3 x y) = (term2 x y)) : (term2 x y) = (term3 x y).
Proof. exact (SYM (@lem1594673 x y h1)). Qed.
Lemma lem1594675 (x : real) (y : real) : ((term2 x y) = (term3 x y)) = ((term3 x y) = (term2 x y)).
Proof. exact (prop_ext (fun h1 : (term2 x y) = (term3 x y) => @lem1594672 x y h1) (fun h1 : (term3 x y) = (term2 x y) => @lem1594674 x y h1)). Qed.
Lemma lem1594676 (x : real) : (term4 x) = (term5 x).
Proof. exact (fun_ext (fun y : real => @lem1594675 x y)). Qed.
Lemma lem1594677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1594678 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1594677) (@lem1594676 x)). Qed.
Lemma lem1594679 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1594678 x)). Qed.
Lemma lem1594680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1594681 : term10 = term11.
Proof. exact (MK_COMB (@lem1594680) (@lem1594679)). Qed.
Lemma lem1594682 : term11.
Proof. exact (EQ_MP (@lem1594681) (@lem1582313)). Qed.
Lemma lem1594683 (x : real) : term12 x.
Proof. exact (@lem1594682 x). Qed.
Lemma lem1594684 (x : real) : (term12 x) = (term7 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1594685 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1594684 x) (@lem1594683 x)). Qed.
Lemma lem1594686 (x : real) (y : real) : term13 x y.
Proof. exact (@lem1594685 x y). Qed.
Lemma lem1594687 (x : real) (y : real) : (term13 x y) = ((term3 x y) = (term2 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1594689 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1594690 (x : real) (h1 : term14) : term15 x.
Proof. exact (@lem1594689 h1 x). Qed.
Lemma lem1594691 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1594692 (x : real) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1594691 x) (@lem1594690 x h1)). Qed.
Lemma lem1594693 (x : real) (y : real) (h1 : term14) : term17 x y.
Proof. exact (@lem1594692 x h1 y). Qed.
Lemma lem1594694 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1594695 (x : real) (y : real) (h1 : term14) : term18 x y.
Proof. exact (EQ_MP (@lem1594694 x y) (@lem1594693 x y h1)). Qed.
Lemma lem1594696 (x : real) (y : real) (h1 : (real_mul x y) = term19) : (real_mul x y) = term19.
Proof. exact (h1). Qed.
Lemma lem1594697 (x : real) (y : real) (h1 : term14) (h2 : (real_mul x y) = term19) : (real_inv x) = y.
Proof. exact (@lem1594695 x y h1 (@lem1594696 x y h2)). Qed.
Lemma lem1594698 (x : real) (y : real) (h1 : (real_mul x y) = term19) : term20 x y.
Proof. exact (fun h0 : term14 => @lem1594697 x y h0 h1). Qed.
Lemma lem1594699 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1594700 (x : real) (y : real) (h1 : term14) (h2 : (real_mul x y) = term19) : (real_inv x) = y.
Proof. exact (@lem1594698 x y h2 (@lem1594699 h1)). Qed.
Lemma lem1594701 (x : real) (y : real) (h1 : term14) : term18 x y.
Proof. exact (fun h0 : (real_mul x y) = term19 => @lem1594700 x y h1 h0). Qed.
Lemma lem1594702 (x : real) (h1 : term14) : term16 x.
Proof. exact (fun y : real => @lem1594701 x y h1). Qed.
Lemma lem1594703 (h1 : term14) : term14.
Proof. exact (fun x : real => @lem1594702 x h1). Qed.
Lemma lem1594704 : term21.
Proof. exact (fun h0 : term14 => @lem1594703 h0). Qed.
Lemma lem1594705 : term14.
Proof. exact (@lem1594704 (@lem1587797)). Qed.
Lemma lem1594706 (x : real) : term15 x.
Proof. exact (@lem1594705 x). Qed.
Lemma lem1594707 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1594708 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem1594707 x) (@lem1594706 x)). Qed.
Lemma lem1594709 (x : real) (y : real) : term17 x y.
Proof. exact (@lem1594708 x y). Qed.
Lemma lem1594710 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1594712 (x : real) : term22 x.
Proof. exact (@lem9784 (x = term23)). Qed.
Lemma lem1594713 (x : real) : (term22 x) = (term24 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1594714 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem1594713 x) (@lem1594712 x)). Qed.
Lemma lem1594716 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1594717 (x : real) (h1 : (term26 x) = (term27 x)) : (term26 x) = (term27 x).
Proof. exact (h1). Qed.
Lemma lem1594718 (x : real) (h1 : (term26 x) = (term27 x)) : (term27 x) = (term26 x).
Proof. exact (SYM (@lem1594717 x h1)). Qed.
Lemma lem1594719 (x : real) (h1 : (term27 x) = (term26 x)) : (term27 x) = (term26 x).
Proof. exact (h1). Qed.
Lemma lem1594720 (x : real) (h1 : (term27 x) = (term26 x)) : (term26 x) = (term27 x).
Proof. exact (SYM (@lem1594719 x h1)). Qed.
Lemma lem1594721 (x : real) : ((term26 x) = (term27 x)) = ((term27 x) = (term26 x)).
Proof. exact (prop_ext (fun h1 : (term26 x) = (term27 x) => @lem1594718 x h1) (fun h1 : (term27 x) = (term26 x) => @lem1594720 x h1)). Qed.
Lemma lem1594722 (x : real) : ((term27 x) = (term26 x)) = ((term26 x) = (term27 x)).
Proof. exact (SYM (@lem1594721 x)). Qed.
Lemma lem1594726 (x : real) (h1 : x = term23) : x = term23.
Proof. exact (h1). Qed.
Lemma lem1594727 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1594728 (x : real) (h1 : x = term23) : (real_abs x) = term28.
Proof. exact (MK_COMB (@lem1594727) (@lem1594726 x h1)). Qed.
Lemma lem1594730 : term28 = term23.
Proof. exact (@lem1528208 (@lem1528207)). Qed.
Lemma lem1594731 (x : real) (h1 : x = term23) : (real_abs x) = term23.
Proof. exact (TRANS (@lem1594728 x h1) (@lem1594730)). Qed.
Lemma lem1594732 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1594733 (x : real) (h1 : x = term23) : (term27 x) = term29.
Proof. exact (MK_COMB (@lem1594732) (@lem1594731 x h1)). Qed.
Lemma lem1594735 : term29 = term23.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1594736 (x : real) (h1 : x = term23) : (term27 x) = term23.
Proof. exact (TRANS (@lem1594733 x h1) (@lem1594735)). Qed.
Lemma lem1594737 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594738 (x : real) (h1 : x = term23) : (term30 x) = term31.
Proof. exact (MK_COMB (@lem1594737) (@lem1594736 x h1)). Qed.
Lemma lem1594740 (x : real) (h1 : x = term23) : x = term23.
Proof. exact (h1). Qed.
Lemma lem1594741 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1594742 (x : real) (h1 : x = term23) : (real_inv x) = term29.
Proof. exact (MK_COMB (@lem1594741) (@lem1594740 x h1)). Qed.
Lemma lem1594744 : term29 = term23.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1594745 (x : real) (h1 : x = term23) : (real_inv x) = term23.
Proof. exact (TRANS (@lem1594742 x h1) (@lem1594744)). Qed.
Lemma lem1594746 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1594747 (x : real) (h1 : x = term23) : (term26 x) = term28.
Proof. exact (MK_COMB (@lem1594746) (@lem1594745 x h1)). Qed.
Lemma lem1594749 : term28 = term23.
Proof. exact (@lem1528208 (@lem1528207)). Qed.
Lemma lem1594750 (x : real) (h1 : x = term23) : (term26 x) = term23.
Proof. exact (TRANS (@lem1594747 x h1) (@lem1594749)). Qed.
Lemma lem1594751 (x : real) (h1 : x = term23) : ((term27 x) = (term26 x)) = (term23 = term23).
Proof. exact (MK_COMB (@lem1594738 x h1) (@lem1594750 x h1)). Qed.
Lemma lem1594753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594754 (x : real) : (x = x) = True.
Proof. exact (@lem1594753 real x). Qed.
Lemma lem1594755 : (term23 = term23) = True.
Proof. exact (@lem1594754 term23). Qed.
Lemma lem1594756 (x : real) (h1 : x = term23) : ((term27 x) = (term26 x)) = True.
Proof. exact (TRANS (@lem1594751 x h1) (@lem1594755)). Qed.
Lemma lem1594757 (x : real) (h1 : x = term23) : True = ((term27 x) = (term26 x)).
Proof. exact (SYM (@lem1594756 x h1)). Qed.
Lemma lem1594758 (x : real) (h1 : x = term23) : (term27 x) = (term26 x).
Proof. exact (EQ_MP (@lem1594757 x h1) (@lem0)). Qed.
Lemma lem1594777 (x : real) (y : real) : term18 x y.
Proof. exact (EQ_MP (@lem1594710 x y) (@lem1594709 x y)). Qed.
Lemma lem1594778 (x : real) : term32 x.
Proof. exact (@lem1594777 (real_abs x) (term26 x)). Qed.
Lemma lem1594782 (x : real) (y : real) : (term3 x y) = (term2 x y).
Proof. exact (EQ_MP (@lem1594687 x y) (@lem1594686 x y)). Qed.
Lemma lem1594783 (x : real) : (term33 x) = (term34 x).
Proof. exact (@lem1594782 x (real_inv x)). Qed.
Lemma lem1594784 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594785 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1594784) (@lem1594783 x)). Qed.
Lemma lem1594786 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1594787 (x : real) : ((term33 x) = term19) = ((term34 x) = term19).
Proof. exact (MK_COMB (@lem1594785 x) (@lem1594786)). Qed.
Lemma lem1594790 (x : real) : ((term34 x) = term19) = ((term33 x) = term19).
Proof. exact (SYM (@lem1594787 x)). Qed.
Lemma lem1594792 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1594667 x) (@lem1594666 x)). Qed.
Lemma lem1594793 (x : real) (h1 : term25 x) : (term37 x) = term19.
Proof. exact (@lem1594792 x (@lem1594716 x h1)). Qed.
Lemma lem1594794 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1594795 (x : real) (h1 : term25 x) : (term39 x) = term40.
Proof. exact (MK_COMB (@lem1594794) (@lem1594793 x h1)). Qed.
Lemma lem1594796 : term40 = (term41 = term19).
Proof. exact (eq_refl term40). Qed.
Lemma lem1594797 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1594798 (x : real) : ((term39 x) = term40) = ((term39 x) = (term41 = term19)).
Proof. exact (MK_COMB (@lem1594797 x) (@lem1594796)). Qed.
Lemma lem1594799 (x : real) : (term39 x) = ((term34 x) = term19).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1594800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1594801 (x : real) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem1594800) (@lem1594799 x)). Qed.
Lemma lem1594802 : (term41 = term19) = (term41 = term19).
Proof. exact (eq_refl (term41 = term19)). Qed.
Lemma lem1594803 (x : real) : ((term39 x) = (term41 = term19)) = (((term34 x) = term19) = (term41 = term19)).
Proof. exact (MK_COMB (@lem1594801 x) (@lem1594802)). Qed.
Lemma lem1594804 (x : real) : ((term39 x) = term40) = (((term34 x) = term19) = (term41 = term19)).
Proof. exact (TRANS (@lem1594798 x) (@lem1594803 x)). Qed.
Lemma lem1594805 (x : real) (h1 : term25 x) : ((term34 x) = term19) = (term41 = term19).
Proof. exact (EQ_MP (@lem1594804 x) (@lem1594795 x h1)). Qed.
Lemma lem1594806 (x : real) (h1 : term25 x) : (term41 = term19) = ((term34 x) = term19).
Proof. exact (SYM (@lem1594805 x h1)). Qed.
Lemma lem1594810 : term41 = term19.
Proof. exact (@lem1528531 (@lem1528530)). Qed.
Lemma lem1594811 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594812 : term44 = term45.
Proof. exact (MK_COMB (@lem1594811) (@lem1594810)). Qed.
Lemma lem1594813 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1594814 : (term41 = term19) = (term19 = term19).
Proof. exact (MK_COMB (@lem1594812) (@lem1594813)). Qed.
Lemma lem1594816 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594817 (x : real) : (x = x) = True.
Proof. exact (@lem1594816 real x). Qed.
Lemma lem1594818 : (term19 = term19) = True.
Proof. exact (@lem1594817 term19). Qed.
Lemma lem1594819 : (term41 = term19) = True.
Proof. exact (TRANS (@lem1594814) (@lem1594818)). Qed.
Lemma lem1594820 : True = (term41 = term19).
Proof. exact (SYM (@lem1594819)). Qed.
Lemma lem1594821 : term41 = term19.
Proof. exact (EQ_MP (@lem1594820) (@lem0)). Qed.
Lemma lem1594822 (x : real) (h1 : term25 x) : (term34 x) = term19.
Proof. exact (EQ_MP (@lem1594806 x h1) (@lem1594821)). Qed.
Lemma lem1594823 (x : real) (h1 : term25 x) : (term33 x) = term19.
Proof. exact (EQ_MP (@lem1594790 x) (@lem1594822 x h1)). Qed.
Lemma lem1594825 (x : real) (h1 : term25 x) : (term27 x) = (term26 x).
Proof. exact (@lem1594778 x (@lem1594823 x h1)). Qed.
Lemma lem1594826 (x : real) : (term27 x) = (term26 x).
Proof. exact (or_elim (@lem1594714 x) (fun h0 : x = term23 => @lem1594758 x h0) (fun h0 : term25 x => @lem1594825 x h0)). Qed.
Lemma lem1594827 (x : real) : (term26 x) = (term27 x).
Proof. exact (EQ_MP (@lem1594722 x) (@lem1594826 x)). Qed.
Lemma lem1594832 : term46.
Proof. exact (fun x : real => @lem1594827 x). Qed.
