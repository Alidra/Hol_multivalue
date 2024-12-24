Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_MUL2_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483464_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1491661 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491662 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1491661 (term4 x)). Qed.
Lemma lem1491663 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (real_mul x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1491664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491666 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1491664) (@lem1491663 x y)). Qed.
Lemma lem1491667 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1491666 x y)). Qed.
Lemma lem1491668 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491669 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1491668) (@lem1491667 x)). Qed.
Lemma lem1491670 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1491662 x) (@lem1491669 x)). Qed.
Lemma lem1491671 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491672 : term12 = term13.
Proof. exact (@lem1491671 term14). Qed.
Lemma lem1491673 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1491674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491675 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1491674) (@lem1491673 x)). Qed.
Lemma lem1491676 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1491675 x) (@lem1491670 x)). Qed.
Lemma lem1491677 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1491676 x)). Qed.
Lemma lem1491678 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491679 : term13 = term20.
Proof. exact (MK_COMB (@lem1491678) (@lem1491677)). Qed.
Lemma lem1491681 : term12 = term20.
Proof. exact (TRANS (@lem1491672) (@lem1491679)). Qed.
Lemma lem1491684 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1491685 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1491684 x y)). Qed.
Lemma lem1491686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491687 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1491686) (@lem1491685 x)). Qed.
Lemma lem1491688 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1491687 x)). Qed.
Lemma lem1491689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491690 : term20 = term20.
Proof. exact (MK_COMB (@lem1491689) (@lem1491688)). Qed.
Lemma lem1491691 : term12 = term20.
Proof. exact (TRANS (@lem1491681) (@lem1491690)). Qed.
Lemma lem1491692 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 x y) (real_mul x y)). Qed.
Lemma lem1491699 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491706 (y : real) : (real_neg y) = (term22 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1491713 (x : real) : (real_neg x) = (term22 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1491714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491715 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1491714) (@lem1491713 x)). Qed.
Lemma lem1491716 (x : real) (y : real) : (term6 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1491715 x) (@lem1491706 y)). Qed.
Lemma lem1491717 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483464 term27 term27 x y). Qed.
Lemma lem1491719 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1491720 : term30 = term31.
Proof. exact (@lem1491719 term32 term32). Qed.
Lemma lem1491721 : (term33 = (BIT1 0)) = (term34 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1491722 : term34 = term32.
Proof. exact (EQ_MP (@lem1491721) (@lem940073)). Qed.
Lemma lem1491723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1491724 : term31 = term35.
Proof. exact (MK_COMB (@lem1491723) (@lem1491722)). Qed.
Lemma lem1491725 : term30 = term35.
Proof. exact (TRANS (@lem1491720) (@lem1491724)). Qed.
Lemma lem1491726 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491727 : term36 = term37.
Proof. exact (MK_COMB (@lem1491726) (@lem1491725)). Qed.
Lemma lem1491728 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491729 (x : real) (y : real) : (term26 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1491727) (@lem1491728 x y)). Qed.
Lemma lem1491734 (x : real) (y : real) : (term25 x y) = (term38 x y).
Proof. exact (TRANS (@lem1491717 x y) (@lem1491729 x y)). Qed.
Lemma lem1491735 (x : real) (y : real) : (term38 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1491736 (x : real) (y : real) : (term25 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1491734 x y) (@lem1491735 x y)). Qed.
Lemma lem1491737 (x : real) (y : real) : (term6 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1491716 x y) (@lem1491736 x y)). Qed.
Lemma lem1491738 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1491739 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1491738) (@lem1491737 x y)). Qed.
Lemma lem1491740 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1491739 x y) (@lem1491699 x y)). Qed.
Lemma lem1491741 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (@lem1483519 (real_mul x y) (real_mul x y)). Qed.
Lemma lem1491745 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483442 term27 (real_mul x y)). Qed.
Lemma lem1491747 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491748 : term47 = term46.
Proof. exact (@lem1491747 term32). Qed.
Lemma lem1491749 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491750 : term48 = term49.
Proof. exact (MK_COMB (@lem1491749) (@lem1491748)). Qed.
Lemma lem1491751 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491752 (x : real) (y : real) : (term44 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1491750) (@lem1491751 x y)). Qed.
Lemma lem1491753 (x : real) (y : real) : (term43 x y) = (term50 x y).
Proof. exact (TRANS (@lem1491745 x y) (@lem1491752 x y)). Qed.
Lemma lem1491754 (x : real) (y : real) : (term50 x y) = term46.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1491756 (x : real) (y : real) : (term43 x y) = term46.
Proof. exact (TRANS (@lem1491753 x y) (@lem1491754 x y)). Qed.
Lemma lem1491757 (x : real) (y : real) : (term42 x y) = term46.
Proof. exact (TRANS (@lem1491741 x y) (@lem1491756 x y)). Qed.
Lemma lem1491758 (x : real) (y : real) : (term41 x y) = term46.
Proof. exact (TRANS (@lem1491740 x y) (@lem1491757 x y)). Qed.
Lemma lem1491759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1491760 (x : real) (y : real) : (term51 x y) = term52.
Proof. exact (MK_COMB (@lem1491759) (@lem1491758 x y)). Qed.
Lemma lem1491761 : term52 = term53.
Proof. exact (@lem1483512 term46). Qed.
Lemma lem1491763 (x : nat) : (term54 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1491764 : term53 = term46.
Proof. exact (@lem1491763 term32). Qed.
Lemma lem1491765 : term52 = term46.
Proof. exact (TRANS (@lem1491761) (@lem1491764)). Qed.
Lemma lem1491766 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1491767 (x : real) (y : real) : ((term51 x y) = term52) = ((term51 x y) = term46).
Proof. exact (MK_COMB (@lem1491766 x y) (@lem1491765)). Qed.
Lemma lem1491768 (x : real) (y : real) : (term51 x y) = term46.
Proof. exact (EQ_MP (@lem1491767 x y) (@lem1491760 x y)). Qed.
Lemma lem1491769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491770 (x : real) (y : real) : (term56 x y) = term57.
Proof. exact (MK_COMB (@lem1491769) (@lem1491768 x y)). Qed.
Lemma lem1491771 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1491772 (x : real) (y : real) : (term58 x y) = term59.
Proof. exact (MK_COMB (@lem1491770 x y) (@lem1491771)). Qed.
Lemma lem1491773 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491774 (x : real) (y : real) : (term60 x y) = term57.
Proof. exact (MK_COMB (@lem1491773) (@lem1491758 x y)). Qed.
Lemma lem1491775 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1491776 (x : real) (y : real) : (term61 x y) = term59.
Proof. exact (MK_COMB (@lem1491774 x y) (@lem1491775)). Qed.
Lemma lem1491777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491778 (x : real) (y : real) : (term62 x y) = term63.
Proof. exact (MK_COMB (@lem1491777) (@lem1491776 x y)). Qed.
Lemma lem1491779 (x : real) (y : real) : (term21 x y) = term64.
Proof. exact (MK_COMB (@lem1491778 x y) (@lem1491772 x y)). Qed.
Lemma lem1491780 (x : real) (y : real) : (term8 x y) = term64.
Proof. exact (TRANS (@lem1491692 x y) (@lem1491779 x y)). Qed.
Lemma lem1491781 (x : real) : (term10 x) = term65.
Proof. exact (fun_ext (fun y : real => @lem1491780 x y)). Qed.
Lemma lem1491782 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491783 (x : real) : (term11 x) = term66.
Proof. exact (MK_COMB (@lem1491782) (@lem1491781 x)). Qed.
Lemma lem1491784 : term19 = term67.
Proof. exact (fun_ext (fun x : real => @lem1491783 x)). Qed.
Lemma lem1491785 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491786 : term20 = term68.
Proof. exact (MK_COMB (@lem1491785) (@lem1491784)). Qed.
Lemma lem1491787 : term12 = term68.
Proof. exact (TRANS (@lem1491691) (@lem1491786)). Qed.
Lemma lem1491789 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491790 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1491789 real t). Qed.
Lemma lem1491791 : term68 = term66.
Proof. exact (@lem1491790 term66). Qed.
Lemma lem1491793 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1491794 (P : real -> Prop) (Q : real -> Prop) : (term73 P Q) = (term74 P Q).
Proof. exact (@lem1491793 real P Q). Qed.
Lemma lem1491795 : term75 = term76.
Proof. exact (@lem1491794 term77 term77). Qed.
Lemma lem1491796 (y : real) : (term78 y) = term59.
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1491797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491798 (y : real) : (term79 y) = term63.
Proof. exact (MK_COMB (@lem1491797) (@lem1491796 y)). Qed.
Lemma lem1491799 (y : real) : (term78 y) = term59.
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1491800 (y : real) : (term80 y) = term64.
Proof. exact (MK_COMB (@lem1491798 y) (@lem1491799 y)). Qed.
Lemma lem1491801 : term81 = term65.
Proof. exact (fun_ext (fun y : real => @lem1491800 y)). Qed.
Lemma lem1491802 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491803 : term75 = term66.
Proof. exact (MK_COMB (@lem1491802) (@lem1491801)). Qed.
Lemma lem1491804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1491805 : term82 = term83.
Proof. exact (MK_COMB (@lem1491804) (@lem1491803)). Qed.
Lemma lem1491806 (y : real) : (term78 y) = term59.
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1491807 : term84 = term77.
Proof. exact (fun_ext (fun y : real => @lem1491806 y)). Qed.
Lemma lem1491808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491809 : term85 = term86.
Proof. exact (MK_COMB (@lem1491808) (@lem1491807)). Qed.
Lemma lem1491810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491811 : term87 = term88.
Proof. exact (MK_COMB (@lem1491810) (@lem1491809)). Qed.
Lemma lem1491812 (y : real) : (term78 y) = term59.
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1491813 : term84 = term77.
Proof. exact (fun_ext (fun y : real => @lem1491812 y)). Qed.
Lemma lem1491814 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491815 : term85 = term86.
Proof. exact (MK_COMB (@lem1491814) (@lem1491813)). Qed.
Lemma lem1491816 : term76 = term89.
Proof. exact (MK_COMB (@lem1491811) (@lem1491815)). Qed.
Lemma lem1491817 : (term75 = term76) = (term66 = term89).
Proof. exact (MK_COMB (@lem1491805) (@lem1491816)). Qed.
Lemma lem1491818 : term66 = term89.
Proof. exact (EQ_MP (@lem1491817) (@lem1491795)). Qed.
Lemma lem1491819 : term68 = term89.
Proof. exact (TRANS (@lem1491791) (@lem1491818)). Qed.
Lemma lem1491821 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491822 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1491821 real t). Qed.
Lemma lem1491823 : term86 = term59.
Proof. exact (@lem1491822 term59). Qed.
Lemma lem1491824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491825 : term88 = term63.
Proof. exact (MK_COMB (@lem1491824) (@lem1491823)). Qed.
Lemma lem1491827 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491828 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1491827 real t). Qed.
Lemma lem1491829 : term86 = term59.
Proof. exact (@lem1491828 term59). Qed.
Lemma lem1491830 : term89 = term64.
Proof. exact (MK_COMB (@lem1491825) (@lem1491829)). Qed.
Lemma lem1491833 : term68 = term64.
Proof. exact (TRANS (@lem1491819) (@lem1491830)). Qed.
Lemma lem1491842 : term12 = term64.
Proof. exact (TRANS (@lem1491787) (@lem1491833)). Qed.
Lemma lem1491852 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1491853 (h1 : term59) : term59.
Proof. exact (h1). Qed.
Lemma lem1491855 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491856 : term59 = term91.
Proof. exact (@lem1491855 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491857 : term91 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491858 : term59 = False.
Proof. exact (TRANS (@lem1491856) (@lem1491857)). Qed.
Lemma lem1491859 (h1 : term59) : False.
Proof. exact (EQ_MP (@lem1491858) (@lem1491853 h1)). Qed.
Lemma lem1491860 (h1 : term59) : term59.
Proof. exact (h1). Qed.
Lemma lem1491862 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491863 : term59 = term91.
Proof. exact (@lem1491862 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491864 : term91 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491865 : term59 = False.
Proof. exact (TRANS (@lem1491863) (@lem1491864)). Qed.
Lemma lem1491866 (h1 : term59) : False.
Proof. exact (EQ_MP (@lem1491865) (@lem1491860 h1)). Qed.
Lemma lem1491867 (h1 : term64) : False.
Proof. exact (or_elim (@lem1491852 h1) (fun h0 : term59 => @lem1491859 h0) (fun h0 : term59 => @lem1491866 h0)). Qed.
Lemma lem1491869 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1491870 (h1 : term64) : term64 = False.
Proof. exact (prop_ext (fun h2 : term64 => @lem1491867 h1) (fun h2 : False => @lem1491869 h1)). Qed.
Lemma lem1491871 (h1 : term64) : False.
Proof. exact (EQ_MP (@lem1491870 h1) (@lem1491869 h1)). Qed.
Lemma lem1491872 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1491873 (h1 : term12) : term64.
Proof. exact (EQ_MP (@lem1491842) (@lem1491872 h1)). Qed.
Lemma lem1491874 (h1 : term12) : term64 = False.
Proof. exact (prop_ext (fun h2 : term64 => @lem1491871 h2) (fun h2 : False => @lem1491873 h1)). Qed.
Lemma lem1491875 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1491874 h1) (@lem1491873 h1)). Qed.
Lemma lem1491876 : term92.
Proof. exact (fun h0 : term12 => @lem1491875 h0). Qed.
Lemma lem1491877 : term93.
Proof. exact (@lem1386578 term94). Qed.
Lemma lem1491878 : term94.
Proof. exact (@lem1491877 (@lem1491876)). Qed.
