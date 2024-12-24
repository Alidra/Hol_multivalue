Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_STILLNZ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482704_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483529_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1539603 (x : real) : (term0 x) = (x = term1).
Proof. exact (@lem16933 (x = term1)). Qed.
Lemma lem1539605 (x : real) (y : real) : (term2 x y) = (term2 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1539606 (y : real) (x : real) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1539605 x y) (@lem1539603 x)). Qed.
Lemma lem1539607 (y : real) (x : real) : (term5 y x) = (term3 y x).
Proof. exact (@lem17362 (term6 x y) (term7 x)). Qed.
Lemma lem1539608 (y : real) (x : real) : (term5 y x) = (term4 y x).
Proof. exact (TRANS (@lem1539607 y x) (@lem1539606 y x)). Qed.
Lemma lem1539609 (P : real -> Prop) : (term8 P) = (term9 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1539610 (x : real) : (term10 x) = (term11 x).
Proof. exact (@lem1539609 (term12 x)). Qed.
Lemma lem1539611 (y : real) (x : real) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1539612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1539613 (y : real) (x : real) : (term15 x y) = (term5 y x).
Proof. exact (MK_COMB (@lem1539612) (@lem1539611 y x)). Qed.
Lemma lem1539614 (y : real) (x : real) : (term15 x y) = (term4 y x).
Proof. exact (TRANS (@lem1539613 y x) (@lem1539608 y x)). Qed.
Lemma lem1539615 (x : real) : (term16 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1539614 y x)). Qed.
Lemma lem1539616 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539617 (x : real) : (term11 x) = (term18 x).
Proof. exact (MK_COMB (@lem1539616) (@lem1539615 x)). Qed.
Lemma lem1539618 (x : real) : (term10 x) = (term18 x).
Proof. exact (TRANS (@lem1539610 x) (@lem1539617 x)). Qed.
Lemma lem1539619 (P : real -> Prop) : (term8 P) = (term9 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1539620 : term19 = term20.
Proof. exact (@lem1539619 term21). Qed.
Lemma lem1539621 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1539622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1539623 (x : real) : (term24 x) = (term10 x).
Proof. exact (MK_COMB (@lem1539622) (@lem1539621 x)). Qed.
Lemma lem1539624 (x : real) : (term24 x) = (term18 x).
Proof. exact (TRANS (@lem1539623 x) (@lem1539618 x)). Qed.
Lemma lem1539625 : term25 = term26.
Proof. exact (fun_ext (fun x : real => @lem1539624 x)). Qed.
Lemma lem1539626 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539627 : term20 = term27.
Proof. exact (MK_COMB (@lem1539626) (@lem1539625)). Qed.
Lemma lem1539629 : term19 = term27.
Proof. exact (TRANS (@lem1539620) (@lem1539627)). Qed.
Lemma lem1539634 (y : real) (x : real) : (term4 y x) = (term4 y x).
Proof. exact (eq_refl (term4 y x)). Qed.
Lemma lem1539635 (x : real) : (term17 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1539634 y x)). Qed.
Lemma lem1539636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539637 (x : real) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem1539636) (@lem1539635 x)). Qed.
Lemma lem1539638 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1539637 x)). Qed.
Lemma lem1539639 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539640 : term27 = term27.
Proof. exact (MK_COMB (@lem1539639) (@lem1539638)). Qed.
Lemma lem1539641 : term19 = term27.
Proof. exact (TRANS (@lem1539629) (@lem1539640)). Qed.
Lemma lem1539642 (x : real) (y : real) : (term6 x y) = (term28 x y).
Proof. exact (@lem1483521 (real_abs y) (term29 x y)). Qed.
Lemma lem1539655 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483519 (real_abs y) (term29 x y)). Qed.
Lemma lem1539656 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539657 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1539656) (@lem1539655 x y)). Qed.
Lemma lem1539658 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539659 (x : real) (y : real) : (term28 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1539657 x y) (@lem1539658)). Qed.
Lemma lem1539660 (x : real) (y : real) : (term6 x y) = (term34 x y).
Proof. exact (TRANS (@lem1539642 x y) (@lem1539659 x y)). Qed.
Lemma lem1539661 (x : real) : (x = term1) = ((term35 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1539667 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1539669 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1539670 : term38 = term1.
Proof. exact (@lem1539669 term39). Qed.
Lemma lem1539671 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1539672 (x : real) : (term36 x) = (term40 x).
Proof. exact (MK_COMB (@lem1539671 x) (@lem1539670)). Qed.
Lemma lem1539673 (x : real) : (term40 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1539674 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1539672 x) (@lem1539673 x)). Qed.
Lemma lem1539676 (x : real) : (term35 x) = x.
Proof. exact (TRANS (@lem1539667 x) (@lem1539674 x)). Qed.
Lemma lem1539677 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1539678 (x : real) : (term41 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1539677) (@lem1539676 x)). Qed.
Lemma lem1539679 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539680 (x : real) : ((term35 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1539678 x) (@lem1539679)). Qed.
Lemma lem1539681 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1539661 x) (@lem1539680 x)). Qed.
Lemma lem1539682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539683 (x : real) (y : real) : (term2 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1539682) (@lem1539660 x y)). Qed.
Lemma lem1539684 (y : real) (x : real) : (term4 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem1539683 x y) (@lem1539681 x)). Qed.
Lemma lem1539685 (x : real) : (term17 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1539684 y x)). Qed.
Lemma lem1539686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539687 (x : real) : (term18 x) = (term45 x).
Proof. exact (MK_COMB (@lem1539686) (@lem1539685 x)). Qed.
Lemma lem1539688 : term26 = term46.
Proof. exact (fun_ext (fun x : real => @lem1539687 x)). Qed.
Lemma lem1539689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539690 : term27 = term47.
Proof. exact (MK_COMB (@lem1539689) (@lem1539688)). Qed.
Lemma lem1539691 : term19 = term47.
Proof. exact (TRANS (@lem1539641) (@lem1539690)). Qed.
Lemma lem1539717 {A : Type'} (P : A -> Prop) (Q : Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem1539718 (P : real -> Prop) (Q : Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem1539717 real P Q). Qed.
Lemma lem1539719 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1539718 (term54 x) (x = term1)). Qed.
Lemma lem1539720 (x : real) (y : real) : (term55 x y) = (term34 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1539721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539722 (x : real) (y : real) : (term56 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1539721) (@lem1539720 x y)). Qed.
Lemma lem1539723 (x : real) : (x = term1) = (x = term1).
Proof. exact (eq_refl (x = term1)). Qed.
Lemma lem1539724 (y : real) (x : real) : (term57 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem1539722 x y) (@lem1539723 x)). Qed.
Lemma lem1539725 (x : real) : (term58 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1539724 y x)). Qed.
Lemma lem1539726 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539727 (x : real) : (term52 x) = (term45 x).
Proof. exact (MK_COMB (@lem1539726) (@lem1539725 x)). Qed.
Lemma lem1539728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1539729 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1539728) (@lem1539727 x)). Qed.
Lemma lem1539730 (x : real) (y : real) : (term55 x y) = (term34 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1539731 (x : real) : (term61 x) = (term54 x).
Proof. exact (fun_ext (fun y : real => @lem1539730 x y)). Qed.
Lemma lem1539732 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539733 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1539732) (@lem1539731 x)). Qed.
Lemma lem1539734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539735 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1539734) (@lem1539733 x)). Qed.
Lemma lem1539736 (x : real) : (x = term1) = (x = term1).
Proof. exact (eq_refl (x = term1)). Qed.
Lemma lem1539737 (x : real) : (term53 x) = (term66 x).
Proof. exact (MK_COMB (@lem1539735 x) (@lem1539736 x)). Qed.
Lemma lem1539738 (x : real) : ((term52 x) = (term53 x)) = ((term45 x) = (term66 x)).
Proof. exact (MK_COMB (@lem1539729 x) (@lem1539737 x)). Qed.
Lemma lem1539739 (x : real) : (term45 x) = (term66 x).
Proof. exact (EQ_MP (@lem1539738 x) (@lem1539719 x)). Qed.
Lemma lem1539744 : term46 = term67.
Proof. exact (fun_ext (fun x : real => @lem1539739 x)). Qed.
Lemma lem1539745 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539746 : term47 = term68.
Proof. exact (MK_COMB (@lem1539745) (@lem1539744)). Qed.
Lemma lem1539796 {A : Type'} (P : A -> Prop) (Q : Prop) : (term49 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1539797 (P : real -> Prop) (Q : Prop) : (term51 P Q) = (term50 P Q).
Proof. exact (@lem1539796 real P Q). Qed.
Lemma lem1539798 (x : real) : (term53 x) = (term52 x).
Proof. exact (@lem1539797 (term54 x) (x = term1)). Qed.
Lemma lem1539799 (x : real) (y : real) : (term55 x y) = (term34 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1539800 (x : real) : (term61 x) = (term54 x).
Proof. exact (fun_ext (fun y : real => @lem1539799 x y)). Qed.
Lemma lem1539801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539802 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1539801) (@lem1539800 x)). Qed.
Lemma lem1539803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539804 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1539803) (@lem1539802 x)). Qed.
Lemma lem1539805 (x : real) : (x = term1) = (x = term1).
Proof. exact (eq_refl (x = term1)). Qed.
Lemma lem1539806 (x : real) : (term53 x) = (term66 x).
Proof. exact (MK_COMB (@lem1539804 x) (@lem1539805 x)). Qed.
Lemma lem1539807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1539808 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1539807) (@lem1539806 x)). Qed.
Lemma lem1539809 (x : real) (y : real) : (term55 x y) = (term34 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1539810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539811 (x : real) (y : real) : (term56 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1539810) (@lem1539809 x y)). Qed.
Lemma lem1539812 (x : real) : (x = term1) = (x = term1).
Proof. exact (eq_refl (x = term1)). Qed.
Lemma lem1539813 (y : real) (x : real) : (term57 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem1539811 x y) (@lem1539812 x)). Qed.
Lemma lem1539814 (x : real) : (term58 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1539813 y x)). Qed.
Lemma lem1539815 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539816 (x : real) : (term52 x) = (term45 x).
Proof. exact (MK_COMB (@lem1539815) (@lem1539814 x)). Qed.
Lemma lem1539817 (x : real) : ((term53 x) = (term52 x)) = ((term66 x) = (term45 x)).
Proof. exact (MK_COMB (@lem1539808 x) (@lem1539816 x)). Qed.
Lemma lem1539818 (x : real) : (term66 x) = (term45 x).
Proof. exact (EQ_MP (@lem1539817 x) (@lem1539798 x)). Qed.
Lemma lem1539819 : term67 = term46.
Proof. exact (fun_ext (fun x : real => @lem1539818 x)). Qed.
Lemma lem1539820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539821 : term68 = term47.
Proof. exact (MK_COMB (@lem1539820) (@lem1539819)). Qed.
Lemma lem1539822 : term47 = term47.
Proof. exact (TRANS (@lem1539746) (@lem1539821)). Qed.
Lemma lem1539825 : term19 = term47.
Proof. exact (TRANS (@lem1539691) (@lem1539822)). Qed.
Lemma lem1539832 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1539833 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1539832 y x)). Qed.
Lemma lem1539834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539835 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1539834) (@lem1539833 x)). Qed.
Lemma lem1539836 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1539835 x)). Qed.
Lemma lem1539837 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539838 : term47 = term47.
Proof. exact (MK_COMB (@lem1539837) (@lem1539836)). Qed.
Lemma lem1539839 : term19 = term47.
Proof. exact (TRANS (@lem1539825) (@lem1539838)). Qed.
Lemma lem1539841 (a : real) (x : real) (r : real) : (term71 a x r) = (term72 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1539842 (x : real) (y : real) : (term34 x y) = (term73 x y).
Proof. exact (@lem1539841 (real_abs y) (real_sub x y) term1). Qed.
Lemma lem1539855 (x : real) (y : real) : (real_sub x y) = (term74 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1539858 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1539859 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1539858) (@lem1539855 x y)). Qed.
Lemma lem1539860 (x : real) (y : real) : (term77 x y) = (term74 x y).
Proof. exact (@lem1483460 (term74 x y)). Qed.
Lemma lem1539861 (x : real) (y : real) : (term76 x y) = (term74 x y).
Proof. exact (TRANS (@lem1539859 x y) (@lem1539860 x y)). Qed.
Lemma lem1539864 (y : real) : (term78 y) = (term78 y).
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1539865 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1539864 y) (@lem1539861 x y)). Qed.
Lemma lem1539866 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483484 x (real_abs y) (term82 y)). Qed.
Lemma lem1539867 (y : real) : (term83 y) = (term84 y).
Proof. exact (@lem1483488 (term82 y) (real_abs y)). Qed.
Lemma lem1539868 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1539869 (x : real) (y : real) : (term81 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1539868 x) (@lem1539867 y)). Qed.
Lemma lem1539870 (x : real) (y : real) : (term80 x y) = (term85 x y).
Proof. exact (TRANS (@lem1539866 x y) (@lem1539869 x y)). Qed.
Lemma lem1539871 (x : real) (y : real) : (term79 x y) = (term85 x y).
Proof. exact (TRANS (@lem1539865 x y) (@lem1539870 x y)). Qed.
Lemma lem1539872 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539873 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1539872) (@lem1539871 x y)). Qed.
Lemma lem1539874 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539875 (x : real) (y : real) : (term88 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1539873 x y) (@lem1539874)). Qed.
Lemma lem1539888 (x : real) (y : real) : (real_sub x y) = (term74 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1539891 : term90 = term90.
Proof. exact (eq_refl term90). Qed.
Lemma lem1539892 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1539891) (@lem1539888 x y)). Qed.
Lemma lem1539893 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (@lem1483508 x term94 (term82 y)). Qed.
Lemma lem1539894 (y : real) : (term95 y) = (term96 y).
Proof. exact (@lem1483476 term94 term94 y). Qed.
Lemma lem1539896 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1539897 : term99 = term100.
Proof. exact (@lem1539896 term39 term39). Qed.
Lemma lem1539898 : (term101 = (BIT1 0)) = (term102 = term39).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1539899 : term102 = term39.
Proof. exact (EQ_MP (@lem1539898) (@lem940073)). Qed.
Lemma lem1539900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1539901 : term100 = term103.
Proof. exact (MK_COMB (@lem1539900) (@lem1539899)). Qed.
Lemma lem1539902 : term99 = term103.
Proof. exact (TRANS (@lem1539897) (@lem1539901)). Qed.
Lemma lem1539903 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539904 : term104 = term75.
Proof. exact (MK_COMB (@lem1539903) (@lem1539902)). Qed.
Lemma lem1539905 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1539906 (y : real) : (term96 y) = (term105 y).
Proof. exact (MK_COMB (@lem1539904) (@lem1539905 y)). Qed.
Lemma lem1539907 (y : real) : (term95 y) = (term105 y).
Proof. exact (TRANS (@lem1539894 y) (@lem1539906 y)). Qed.
Lemma lem1539908 (y : real) : (term105 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1539909 (y : real) : (term95 y) = y.
Proof. exact (TRANS (@lem1539907 y) (@lem1539908 y)). Qed.
Lemma lem1539912 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1539913 (x : real) (y : real) : (term93 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1539912 x) (@lem1539909 y)). Qed.
Lemma lem1539914 (x : real) (y : real) : (term92 x y) = (term107 x y).
Proof. exact (TRANS (@lem1539893 x y) (@lem1539913 x y)). Qed.
Lemma lem1539915 (x : real) (y : real) : (term91 x y) = (term107 x y).
Proof. exact (TRANS (@lem1539892 x y) (@lem1539914 x y)). Qed.
Lemma lem1539918 (y : real) : (term78 y) = (term78 y).
Proof. exact (eq_refl (term78 y)). Qed.
Lemma lem1539919 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1539918 y) (@lem1539915 x y)). Qed.
Lemma lem1539920 (x : real) (y : real) : (term109 x y) = (term110 x y).
Proof. exact (@lem1483484 (term82 x) (real_abs y) y). Qed.
Lemma lem1539921 (y : real) : (term111 y) = (term112 y).
Proof. exact (@lem1483488 y (real_abs y)). Qed.
Lemma lem1539922 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1539923 (x : real) (y : real) : (term110 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1539922 x) (@lem1539921 y)). Qed.
Lemma lem1539924 (x : real) (y : real) : (term109 x y) = (term113 x y).
Proof. exact (TRANS (@lem1539920 x y) (@lem1539923 x y)). Qed.
Lemma lem1539925 (x : real) (y : real) : (term108 x y) = (term113 x y).
Proof. exact (TRANS (@lem1539919 x y) (@lem1539924 x y)). Qed.
Lemma lem1539926 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539927 (x : real) (y : real) : (term114 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1539926) (@lem1539925 x y)). Qed.
Lemma lem1539928 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539929 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1539927 x y) (@lem1539928)). Qed.
Lemma lem1539930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539931 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1539930) (@lem1539929 x y)). Qed.
Lemma lem1539932 (x : real) (y : real) : (term73 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1539931 x y) (@lem1539875 x y)). Qed.
Lemma lem1539933 (x : real) (y : real) : (term34 x y) = (term120 x y).
Proof. exact (TRANS (@lem1539842 x y) (@lem1539932 x y)). Qed.
Lemma lem1539934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539935 (x : real) (y : real) : (term42 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1539934) (@lem1539933 x y)). Qed.
Lemma lem1539936 (x : real) : (x = term1) = (x = term1).
Proof. exact (eq_refl (x = term1)). Qed.
Lemma lem1539937 (y : real) (x : real) : (term43 y x) = (term122 y x).
Proof. exact (MK_COMB (@lem1539935 x y) (@lem1539936 x)). Qed.
Lemma lem1539938 (y : real) (x : real) : (term123 x y) = (term122 y x).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1539939 (x : real) (y : real) : (term122 y x) = (term123 x y).
Proof. exact (SYM (@lem1539938 y x)). Qed.
Lemma lem1539940 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (@lem1482981 (term125 y x) y). Qed.
Lemma lem1539941 (x : real) (y : real) : (term122 y x) = (term124 x y).
Proof. exact (TRANS (@lem1539939 x y) (@lem1539940 x y)). Qed.
Lemma lem1539942 (y : real) (x : real) : (term126 x y) = (term127 y x).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem1539943 (y : real) : (term128 y) = (term128 y).
Proof. exact (eq_refl (term128 y)). Qed.
Lemma lem1539944 (y : real) (x : real) : (term129 x y) = (term130 y x).
Proof. exact (MK_COMB (@lem1539943 y) (@lem1539942 y x)). Qed.
Lemma lem1539945 (y : real) (x : real) : (term131 x y) = (term132 y x).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1539946 (y : real) : (term133 y) = (term133 y).
Proof. exact (eq_refl (term133 y)). Qed.
Lemma lem1539947 (y : real) (x : real) : (term134 x y) = (term135 y x).
Proof. exact (MK_COMB (@lem1539946 y) (@lem1539945 y x)). Qed.
Lemma lem1539948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1539949 (y : real) (x : real) : (term136 x y) = (term137 y x).
Proof. exact (MK_COMB (@lem1539948) (@lem1539947 y x)). Qed.
Lemma lem1539950 (y : real) (x : real) : (term124 x y) = (term138 y x).
Proof. exact (MK_COMB (@lem1539949 y x) (@lem1539944 y x)). Qed.
Lemma lem1539951 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1539952 (y : real) (x : real) : ((term122 y x) = (term124 x y)) = ((term122 y x) = (term138 y x)).
Proof. exact (MK_COMB (@lem1539951 y x) (@lem1539950 y x)). Qed.
Lemma lem1539953 (y : real) (x : real) : (term122 y x) = (term138 y x).
Proof. exact (EQ_MP (@lem1539952 y x) (@lem1539941 x y)). Qed.
Lemma lem1539954 (y : real) : (term140 y) = (term141 y).
Proof. exact (@lem1483527 y term1). Qed.
Lemma lem1539960 (y : real) : (term35 y) = (term36 y).
Proof. exact (@lem1483519 y term1). Qed.
Lemma lem1539962 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1539963 : term38 = term1.
Proof. exact (@lem1539962 term39). Qed.
Lemma lem1539964 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1539965 (y : real) : (term36 y) = (term40 y).
Proof. exact (MK_COMB (@lem1539964 y) (@lem1539963)). Qed.
Lemma lem1539966 (y : real) : (term40 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1539967 (y : real) : (term36 y) = y.
Proof. exact (TRANS (@lem1539965 y) (@lem1539966 y)). Qed.
Lemma lem1539969 (y : real) : (term35 y) = y.
Proof. exact (TRANS (@lem1539960 y) (@lem1539967 y)). Qed.
Lemma lem1539970 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1539971 (y : real) : (term142 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1539970) (@lem1539969 y)). Qed.
Lemma lem1539972 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539973 (y : real) : (term141 y) = (term140 y).
Proof. exact (MK_COMB (@lem1539971 y) (@lem1539972)). Qed.
Lemma lem1539974 (y : real) : (term140 y) = (term140 y).
Proof. exact (TRANS (@lem1539954 y) (@lem1539973 y)). Qed.
Lemma lem1539975 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (@lem1483525 (term145 x y) term1). Qed.
Lemma lem1539976 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1539982 (y : real) : (real_add y y) = (term146 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1539983 : term147 = term148.
Proof. exact (@lem1367770 term39 term39). Qed.
Lemma lem1539984 : term149 = term150.
Proof. exact (@lem706885). Qed.
Lemma lem1539985 : (term149 = term150) = (term151 = term152).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term150). Qed.
Lemma lem1539986 : term151 = term152.
Proof. exact (EQ_MP (@lem1539985) (@lem1539984)). Qed.
Lemma lem1539987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1539988 : term148 = term153.
Proof. exact (MK_COMB (@lem1539987) (@lem1539986)). Qed.
Lemma lem1539989 : term147 = term153.
Proof. exact (TRANS (@lem1539983) (@lem1539988)). Qed.
Lemma lem1539990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539991 : term154 = term155.
Proof. exact (MK_COMB (@lem1539990) (@lem1539989)). Qed.
Lemma lem1539992 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1539993 (y : real) : (term146 y) = (term156 y).
Proof. exact (MK_COMB (@lem1539991) (@lem1539992 y)). Qed.
Lemma lem1539995 (y : real) : (real_add y y) = (term156 y).
Proof. exact (TRANS (@lem1539982 y) (@lem1539993 y)). Qed.
Lemma lem1540004 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1540007 (x : real) (y : real) : (term145 x y) = (term157 x y).
Proof. exact (MK_COMB (@lem1540004 x) (@lem1539995 y)). Qed.
Lemma lem1540008 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1540009 (x : real) (y : real) : (term158 x y) = (term159 x y).
Proof. exact (MK_COMB (@lem1540008) (@lem1540007 x y)). Qed.
Lemma lem1540010 (x : real) (y : real) : (term160 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1540009 x y) (@lem1539976)). Qed.
Lemma lem1540011 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem1483519 (term157 x y) term1). Qed.
Lemma lem1540013 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540014 : term38 = term1.
Proof. exact (@lem1540013 term39). Qed.
Lemma lem1540015 (x : real) (y : real) : (term163 x y) = (term163 x y).
Proof. exact (eq_refl (term163 x y)). Qed.
Lemma lem1540016 (x : real) (y : real) : (term162 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1540015 x y) (@lem1540014)). Qed.
Lemma lem1540017 (x : real) (y : real) : (term164 x y) = (term157 x y).
Proof. exact (@lem1483450 (term157 x y)). Qed.
Lemma lem1540018 (x : real) (y : real) : (term162 x y) = (term157 x y).
Proof. exact (TRANS (@lem1540016 x y) (@lem1540017 x y)). Qed.
Lemma lem1540019 (x : real) (y : real) : (term161 x y) = (term157 x y).
Proof. exact (TRANS (@lem1540011 x y) (@lem1540018 x y)). Qed.
Lemma lem1540020 (x : real) (y : real) : (term160 x y) = (term157 x y).
Proof. exact (TRANS (@lem1540010 x y) (@lem1540019 x y)). Qed.
Lemma lem1540021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540022 (x : real) (y : real) : (term165 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1540021) (@lem1540020 x y)). Qed.
Lemma lem1540023 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540024 (x : real) (y : real) : (term144 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem1540022 x y) (@lem1540023)). Qed.
Lemma lem1540025 (x : real) (y : real) : (term143 x y) = (term167 x y).
Proof. exact (TRANS (@lem1539975 x y) (@lem1540024 x y)). Qed.
Lemma lem1540026 (x : real) (y : real) : (term168 x y) = (term169 x y).
Proof. exact (@lem1483525 (term170 x y) term1). Qed.
Lemma lem1540027 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540039 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term94 y). Qed.
Lemma lem1540041 (m : nat) : (term173 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540042 : term174 = term1.
Proof. exact (@lem1540041 term39). Qed.
Lemma lem1540043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540044 : term175 = term176.
Proof. exact (MK_COMB (@lem1540043) (@lem1540042)). Qed.
Lemma lem1540045 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1540046 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1540044) (@lem1540045 y)). Qed.
Lemma lem1540047 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1540039 y) (@lem1540046 y)). Qed.
Lemma lem1540048 (y : real) : (term177 y) = term1.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1540050 (y : real) : (term171 y) = term1.
Proof. exact (TRANS (@lem1540047 y) (@lem1540048 y)). Qed.
Lemma lem1540053 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1540054 (y : real) (x : real) : (term170 x y) = (term40 x).
Proof. exact (MK_COMB (@lem1540053 x) (@lem1540050 y)). Qed.
Lemma lem1540055 (x : real) : (term40 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1540056 (y : real) (x : real) : (term170 x y) = x.
Proof. exact (TRANS (@lem1540054 y x) (@lem1540055 x)). Qed.
Lemma lem1540057 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1540058 (y : real) (x : real) : (term178 x y) = (real_sub x).
Proof. exact (MK_COMB (@lem1540057) (@lem1540056 y x)). Qed.
Lemma lem1540059 (y : real) (x : real) : (term179 x y) = (term35 x).
Proof. exact (MK_COMB (@lem1540058 y x) (@lem1540027)). Qed.
Lemma lem1540060 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1540062 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540063 : term38 = term1.
Proof. exact (@lem1540062 term39). Qed.
Lemma lem1540064 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1540065 (x : real) : (term36 x) = (term40 x).
Proof. exact (MK_COMB (@lem1540064 x) (@lem1540063)). Qed.
Lemma lem1540066 (x : real) : (term40 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1540067 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1540065 x) (@lem1540066 x)). Qed.
Lemma lem1540068 (x : real) : (term35 x) = x.
Proof. exact (TRANS (@lem1540060 x) (@lem1540067 x)). Qed.
Lemma lem1540069 (y : real) (x : real) : (term179 x y) = x.
Proof. exact (TRANS (@lem1540059 y x) (@lem1540068 x)). Qed.
Lemma lem1540070 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540071 (y : real) (x : real) : (term180 x y) = (real_gt x).
Proof. exact (MK_COMB (@lem1540070) (@lem1540069 y x)). Qed.
Lemma lem1540072 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540073 (y : real) (x : real) : (term169 x y) = (term181 x).
Proof. exact (MK_COMB (@lem1540071 y x) (@lem1540072)). Qed.
Lemma lem1540074 (y : real) (x : real) : (term168 x y) = (term181 x).
Proof. exact (TRANS (@lem1540026 x y) (@lem1540073 y x)). Qed.
Lemma lem1540075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540076 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1540075) (@lem1540025 x y)). Qed.
Lemma lem1540077 (y : real) (x : real) : (term184 x y) = (term185 y x).
Proof. exact (MK_COMB (@lem1540076 x y) (@lem1540074 y x)). Qed.
Lemma lem1540078 (x : real) : (x = term1) = ((term35 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1540084 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1540086 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540087 : term38 = term1.
Proof. exact (@lem1540086 term39). Qed.
Lemma lem1540088 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1540089 (x : real) : (term36 x) = (term40 x).
Proof. exact (MK_COMB (@lem1540088 x) (@lem1540087)). Qed.
Lemma lem1540090 (x : real) : (term40 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1540091 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1540089 x) (@lem1540090 x)). Qed.
Lemma lem1540093 (x : real) : (term35 x) = x.
Proof. exact (TRANS (@lem1540084 x) (@lem1540091 x)). Qed.
Lemma lem1540094 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1540095 (x : real) : (term41 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1540094) (@lem1540093 x)). Qed.
Lemma lem1540096 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540097 (x : real) : ((term35 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1540095 x) (@lem1540096)). Qed.
Lemma lem1540098 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1540078 x) (@lem1540097 x)). Qed.
Lemma lem1540099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540100 (y : real) (x : real) : (term186 x y) = (term187 y x).
Proof. exact (MK_COMB (@lem1540099) (@lem1540077 y x)). Qed.
Lemma lem1540101 (y : real) (x : real) : (term132 y x) = (term188 y x).
Proof. exact (MK_COMB (@lem1540100 y x) (@lem1540098 x)). Qed.
Lemma lem1540102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540103 (y : real) : (term133 y) = (term133 y).
Proof. exact (MK_COMB (@lem1540102) (@lem1539974 y)). Qed.
Lemma lem1540104 (y : real) (x : real) : (term135 y x) = (term189 y x).
Proof. exact (MK_COMB (@lem1540103 y) (@lem1540101 y x)). Qed.
Lemma lem1540105 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1483525 term1 y). Qed.
Lemma lem1540111 (y : real) : (term192 y) = (term193 y).
Proof. exact (@lem1483519 term1 y). Qed.
Lemma lem1540116 (y : real) : (term193 y) = (term82 y).
Proof. exact (@lem1483448 (term82 y)). Qed.
Lemma lem1540118 (y : real) : (term192 y) = (term82 y).
Proof. exact (TRANS (@lem1540111 y) (@lem1540116 y)). Qed.
Lemma lem1540119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540120 (y : real) : (term194 y) = (term195 y).
Proof. exact (MK_COMB (@lem1540119) (@lem1540118 y)). Qed.
Lemma lem1540121 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540122 (y : real) : (term191 y) = (term196 y).
Proof. exact (MK_COMB (@lem1540120 y) (@lem1540121)). Qed.
Lemma lem1540123 (y : real) : (term190 y) = (term196 y).
Proof. exact (TRANS (@lem1540105 y) (@lem1540122 y)). Qed.
Lemma lem1540124 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (@lem1483525 (term199 x y) term1). Qed.
Lemma lem1540125 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540132 (y : real) : (real_neg y) = (term82 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1540135 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1540136 (y : real) : (term200 y) = (term201 y).
Proof. exact (MK_COMB (@lem1540135 y) (@lem1540132 y)). Qed.
Lemma lem1540137 (y : real) : (term201 y) = (term172 y).
Proof. exact (@lem1483442 term94 y). Qed.
Lemma lem1540139 (m : nat) : (term173 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540140 : term174 = term1.
Proof. exact (@lem1540139 term39). Qed.
Lemma lem1540141 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540142 : term175 = term176.
Proof. exact (MK_COMB (@lem1540141) (@lem1540140)). Qed.
Lemma lem1540143 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1540144 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1540142) (@lem1540143 y)). Qed.
Lemma lem1540145 (y : real) : (term201 y) = (term177 y).
Proof. exact (TRANS (@lem1540137 y) (@lem1540144 y)). Qed.
Lemma lem1540146 (y : real) : (term177 y) = term1.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1540147 (y : real) : (term201 y) = term1.
Proof. exact (TRANS (@lem1540145 y) (@lem1540146 y)). Qed.
Lemma lem1540148 (y : real) : (term200 y) = term1.
Proof. exact (TRANS (@lem1540136 y) (@lem1540147 y)). Qed.
Lemma lem1540157 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1540158 (y : real) (x : real) : (term199 x y) = (term202 x).
Proof. exact (MK_COMB (@lem1540157 x) (@lem1540148 y)). Qed.
Lemma lem1540159 (x : real) : (term202 x) = (term82 x).
Proof. exact (@lem1483450 (term82 x)). Qed.
Lemma lem1540160 (y : real) (x : real) : (term199 x y) = (term82 x).
Proof. exact (TRANS (@lem1540158 y x) (@lem1540159 x)). Qed.
Lemma lem1540161 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1540162 (y : real) (x : real) : (term203 x y) = (term204 x).
Proof. exact (MK_COMB (@lem1540161) (@lem1540160 y x)). Qed.
Lemma lem1540163 (y : real) (x : real) : (term205 x y) = (term206 x).
Proof. exact (MK_COMB (@lem1540162 y x) (@lem1540125)). Qed.
Lemma lem1540164 (x : real) : (term206 x) = (term207 x).
Proof. exact (@lem1483519 (term82 x) term1). Qed.
Lemma lem1540166 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540167 : term38 = term1.
Proof. exact (@lem1540166 term39). Qed.
Lemma lem1540168 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1540169 (x : real) : (term207 x) = (term202 x).
Proof. exact (MK_COMB (@lem1540168 x) (@lem1540167)). Qed.
Lemma lem1540170 (x : real) : (term202 x) = (term82 x).
Proof. exact (@lem1483450 (term82 x)). Qed.
Lemma lem1540171 (x : real) : (term207 x) = (term82 x).
Proof. exact (TRANS (@lem1540169 x) (@lem1540170 x)). Qed.
Lemma lem1540172 (x : real) : (term206 x) = (term82 x).
Proof. exact (TRANS (@lem1540164 x) (@lem1540171 x)). Qed.
Lemma lem1540173 (y : real) (x : real) : (term205 x y) = (term82 x).
Proof. exact (TRANS (@lem1540163 y x) (@lem1540172 x)). Qed.
Lemma lem1540174 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540175 (y : real) (x : real) : (term208 x y) = (term195 x).
Proof. exact (MK_COMB (@lem1540174) (@lem1540173 y x)). Qed.
Lemma lem1540176 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540177 (y : real) (x : real) : (term198 x y) = (term196 x).
Proof. exact (MK_COMB (@lem1540175 y x) (@lem1540176)). Qed.
Lemma lem1540178 (y : real) (x : real) : (term197 x y) = (term196 x).
Proof. exact (TRANS (@lem1540124 x y) (@lem1540177 y x)). Qed.
Lemma lem1540179 (x : real) (y : real) : (term209 x y) = (term210 x y).
Proof. exact (@lem1483525 (term211 x y) term1). Qed.
Lemma lem1540180 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540187 (y : real) : (real_neg y) = (term82 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1540196 (y : real) : (term106 y) = (term106 y).
Proof. exact (eq_refl (term106 y)). Qed.
Lemma lem1540197 (y : real) : (term212 y) = (term213 y).
Proof. exact (MK_COMB (@lem1540196 y) (@lem1540187 y)). Qed.
Lemma lem1540198 (y : real) : (term213 y) = (term214 y).
Proof. exact (@lem1483438 term94 term94 y). Qed.
Lemma lem1540199 : term215 = term216.
Proof. exact (@lem1367763 term39 term39). Qed.
Lemma lem1540200 : term149 = term150.
Proof. exact (@lem706885). Qed.
Lemma lem1540201 : (term149 = term150) = (term151 = term152).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term150). Qed.
Lemma lem1540202 : term151 = term152.
Proof. exact (EQ_MP (@lem1540201) (@lem1540200)). Qed.
Lemma lem1540203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1540204 : term148 = term153.
Proof. exact (MK_COMB (@lem1540203) (@lem1540202)). Qed.
Lemma lem1540205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1540206 : term216 = term217.
Proof. exact (MK_COMB (@lem1540205) (@lem1540204)). Qed.
Lemma lem1540207 : term215 = term217.
Proof. exact (TRANS (@lem1540199) (@lem1540206)). Qed.
Lemma lem1540208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540209 : term218 = term219.
Proof. exact (MK_COMB (@lem1540208) (@lem1540207)). Qed.
Lemma lem1540210 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1540211 (y : real) : (term214 y) = (term220 y).
Proof. exact (MK_COMB (@lem1540209) (@lem1540210 y)). Qed.
Lemma lem1540212 (y : real) : (term213 y) = (term220 y).
Proof. exact (TRANS (@lem1540198 y) (@lem1540211 y)). Qed.
Lemma lem1540213 (y : real) : (term212 y) = (term220 y).
Proof. exact (TRANS (@lem1540197 y) (@lem1540212 y)). Qed.
Lemma lem1540216 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1540219 (x : real) (y : real) : (term211 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1540216 x) (@lem1540213 y)). Qed.
Lemma lem1540220 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1540221 (x : real) (y : real) : (term222 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1540220) (@lem1540219 x y)). Qed.
Lemma lem1540222 (x : real) (y : real) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem1540221 x y) (@lem1540180)). Qed.
Lemma lem1540223 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (@lem1483519 (term221 x y) term1). Qed.
Lemma lem1540225 (x : nat) : (term37 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540226 : term38 = term1.
Proof. exact (@lem1540225 term39). Qed.
Lemma lem1540227 (x : real) (y : real) : (term227 x y) = (term227 x y).
Proof. exact (eq_refl (term227 x y)). Qed.
Lemma lem1540228 (x : real) (y : real) : (term226 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1540227 x y) (@lem1540226)). Qed.
Lemma lem1540229 (x : real) (y : real) : (term228 x y) = (term221 x y).
Proof. exact (@lem1483450 (term221 x y)). Qed.
Lemma lem1540230 (x : real) (y : real) : (term226 x y) = (term221 x y).
Proof. exact (TRANS (@lem1540228 x y) (@lem1540229 x y)). Qed.
Lemma lem1540231 (x : real) (y : real) : (term225 x y) = (term221 x y).
Proof. exact (TRANS (@lem1540223 x y) (@lem1540230 x y)). Qed.
Lemma lem1540232 (x : real) (y : real) : (term224 x y) = (term221 x y).
Proof. exact (TRANS (@lem1540222 x y) (@lem1540231 x y)). Qed.
Lemma lem1540233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540234 (x : real) (y : real) : (term229 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem1540233) (@lem1540232 x y)). Qed.
Lemma lem1540235 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540236 (x : real) (y : real) : (term210 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem1540234 x y) (@lem1540235)). Qed.
Lemma lem1540237 (x : real) (y : real) : (term209 x y) = (term231 x y).
Proof. exact (TRANS (@lem1540179 x y) (@lem1540236 x y)). Qed.
Lemma lem1540238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540239 (y : real) (x : real) : (term232 x y) = (term233 x).
Proof. exact (MK_COMB (@lem1540238) (@lem1540178 y x)). Qed.
Lemma lem1540240 (x : real) (y : real) : (term234 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1540239 y x) (@lem1540237 x y)). Qed.
Lemma lem1540241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540242 (x : real) (y : real) : (term236 x y) = (term237 x y).
Proof. exact (MK_COMB (@lem1540241) (@lem1540240 x y)). Qed.
Lemma lem1540243 (y : real) (x : real) : (term127 y x) = (term238 y x).
Proof. exact (MK_COMB (@lem1540242 x y) (@lem1540098 x)). Qed.
Lemma lem1540244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540245 (y : real) : (term128 y) = (term233 y).
Proof. exact (MK_COMB (@lem1540244) (@lem1540123 y)). Qed.
Lemma lem1540246 (y : real) (x : real) : (term130 y x) = (term239 y x).
Proof. exact (MK_COMB (@lem1540245 y) (@lem1540243 y x)). Qed.
Lemma lem1540247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1540248 (y : real) (x : real) : (term137 y x) = (term240 y x).
Proof. exact (MK_COMB (@lem1540247) (@lem1540104 y x)). Qed.
Lemma lem1540249 (y : real) (x : real) : (term138 y x) = (term241 y x).
Proof. exact (MK_COMB (@lem1540248 y x) (@lem1540246 y x)). Qed.
Lemma lem1540260 (y : real) (x : real) : (term122 y x) = (term241 y x).
Proof. exact (TRANS (@lem1539953 y x) (@lem1540249 y x)). Qed.
Lemma lem1540261 (y : real) (x : real) : (term43 y x) = (term241 y x).
Proof. exact (TRANS (@lem1539937 y x) (@lem1540260 y x)). Qed.
Lemma lem1540262 (y : real) (x : real) (h1 : term241 y x) : term241 y x.
Proof. exact (h1). Qed.
Lemma lem1540263 (y : real) (x : real) (h1 : term189 y x) : term189 y x.
Proof. exact (h1). Qed.
Lemma lem1540264 (y : real) (x : real) (h1 : term189 y x) : term188 y x.
Proof. exact (proj2 (@lem1540263 y x h1)). Qed.
Lemma lem1540266 (y : real) (x : real) (h1 : term189 y x) : x = term1.
Proof. exact (proj2 (@lem1540264 y x h1)). Qed.
Lemma lem1540267 (y : real) (x : real) (h1 : term189 y x) : term185 y x.
Proof. exact (proj1 (@lem1540264 y x h1)). Qed.
Lemma lem1540268 (y : real) (x : real) (h1 : term189 y x) : term181 x.
Proof. exact (proj2 (@lem1540267 y x h1)). Qed.
Lemma lem1540271 (n : nat) (m : nat) : (term242 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540272 : term243 = term244.
Proof. exact (@lem1540271 (NUMERAL 0) term39). Qed.
Lemma lem1540273 : term245 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540274 (h1 : term245 = (BIT1 0)) : term244 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540275 : (term245 = (BIT1 0)) = (term244 = True).
Proof. exact (prop_ext (fun h1 : term245 = (BIT1 0) => @lem1540274 h1) (fun h1 : term244 = True => @lem1540273)). Qed.
Lemma lem1540276 : term244 = True.
Proof. exact (EQ_MP (@lem1540275) (@lem1540273)). Qed.
Lemma lem1540277 : term243 = True.
Proof. exact (TRANS (@lem1540272) (@lem1540276)). Qed.
Lemma lem1540278 : True = term243.
Proof. exact (SYM (@lem1540277)). Qed.
Lemma lem1540279 : term243.
Proof. exact (EQ_MP (@lem1540278) (@lem0)). Qed.
Lemma lem1540280 (y : real) (x : real) (h1 : term189 y x) : term246 x.
Proof. exact (conj (@lem1540279) (@lem1540268 y x h1)). Qed.
Lemma lem1540282 (x : real) (y : real) : term247 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1540283 (x : real) : term248 x.
Proof. exact (@lem1540282 term103 x). Qed.
Lemma lem1540284 (y : real) (x : real) (h1 : term189 y x) : term249 x.
Proof. exact (@lem1540283 x (@lem1540280 y x h1)). Qed.
Lemma lem1540285 (x : real) : (term105 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540286 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540287 (x : real) : (term250 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1540286) (@lem1540285 x)). Qed.
Lemma lem1540288 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540289 (x : real) : (term249 x) = (term181 x).
Proof. exact (MK_COMB (@lem1540287 x) (@lem1540288)). Qed.
Lemma lem1540290 (y : real) (x : real) (h1 : term189 y x) : term181 x.
Proof. exact (EQ_MP (@lem1540289 x) (@lem1540284 y x h1)). Qed.
Lemma lem1540292 (y : real) : term251 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1540293 (x : real) : term251 x.
Proof. exact (@lem1540292 x). Qed.
Lemma lem1540294 (y : real) (x : real) (h1 : term189 y x) : term252 x.
Proof. exact (@lem1540293 x (@lem1540266 y x h1)). Qed.
Lemma lem1540295 (y : real) (x : real) (h1 : term189 y x) : term253 x.
Proof. exact (@lem1540294 y x h1 term94). Qed.
Lemma lem1540296 (x : real) : (term253 x) = ((term82 x) = term1).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem1540303 (y : real) (x : real) (h1 : term189 y x) : (term82 x) = term1.
Proof. exact (EQ_MP (@lem1540296 x) (@lem1540295 y x h1)). Qed.
Lemma lem1540304 (y : real) (x : real) (h1 : term189 y x) : term254 x.
Proof. exact (conj (@lem1540303 y x h1) (@lem1540290 y x h1)). Qed.
Lemma lem1540306 (x : real) (y : real) : term255 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1540307 (x : real) : term256 x.
Proof. exact (@lem1540306 (term82 x) x). Qed.
Lemma lem1540308 (y : real) (x : real) (h1 : term189 y x) : term257 x.
Proof. exact (@lem1540307 x (@lem1540304 y x h1)). Qed.
Lemma lem1540309 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term94 x). Qed.
Lemma lem1540311 (m : nat) : (term173 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540312 : term174 = term1.
Proof. exact (@lem1540311 term39). Qed.
Lemma lem1540313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540314 : term175 = term176.
Proof. exact (MK_COMB (@lem1540313) (@lem1540312)). Qed.
Lemma lem1540315 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1540316 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1540314) (@lem1540315 x)). Qed.
Lemma lem1540317 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1540309 x) (@lem1540316 x)). Qed.
Lemma lem1540318 (x : real) : (term177 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1540319 (x : real) : (term171 x) = term1.
Proof. exact (TRANS (@lem1540317 x) (@lem1540318 x)). Qed.
Lemma lem1540320 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540321 (x : real) : (term258 x) = term259.
Proof. exact (MK_COMB (@lem1540320) (@lem1540319 x)). Qed.
Lemma lem1540322 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540323 (x : real) : (term257 x) = term260.
Proof. exact (MK_COMB (@lem1540321 x) (@lem1540322)). Qed.
Lemma lem1540324 (y : real) (x : real) (h1 : term189 y x) : term260.
Proof. exact (EQ_MP (@lem1540323 x) (@lem1540308 y x h1)). Qed.
Lemma lem1540326 (n : nat) (m : nat) : (term242 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540327 : term260 = term261.
Proof. exact (@lem1540326 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1540328 : term261 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1540329 : term260 = False.
Proof. exact (TRANS (@lem1540327) (@lem1540328)). Qed.
Lemma lem1540330 (y : real) (x : real) (h1 : term189 y x) : False.
Proof. exact (EQ_MP (@lem1540329) (@lem1540324 y x h1)). Qed.
Lemma lem1540331 (y : real) (x : real) (h1 : term239 y x) : term239 y x.
Proof. exact (h1). Qed.
Lemma lem1540332 (y : real) (x : real) (h1 : term239 y x) : term238 y x.
Proof. exact (proj2 (@lem1540331 y x h1)). Qed.
Lemma lem1540334 (y : real) (x : real) (h1 : term239 y x) : x = term1.
Proof. exact (proj2 (@lem1540332 y x h1)). Qed.
Lemma lem1540335 (y : real) (x : real) (h1 : term239 y x) : term235 x y.
Proof. exact (proj1 (@lem1540332 y x h1)). Qed.
Lemma lem1540337 (y : real) (x : real) (h1 : term239 y x) : term196 x.
Proof. exact (proj1 (@lem1540335 y x h1)). Qed.
Lemma lem1540339 (n : nat) (m : nat) : (term242 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540340 : term243 = term244.
Proof. exact (@lem1540339 (NUMERAL 0) term39). Qed.
Lemma lem1540341 : term245 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540342 (h1 : term245 = (BIT1 0)) : term244 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540343 : (term245 = (BIT1 0)) = (term244 = True).
Proof. exact (prop_ext (fun h1 : term245 = (BIT1 0) => @lem1540342 h1) (fun h1 : term244 = True => @lem1540341)). Qed.
Lemma lem1540344 : term244 = True.
Proof. exact (EQ_MP (@lem1540343) (@lem1540341)). Qed.
Lemma lem1540345 : term243 = True.
Proof. exact (TRANS (@lem1540340) (@lem1540344)). Qed.
Lemma lem1540346 : True = term243.
Proof. exact (SYM (@lem1540345)). Qed.
Lemma lem1540347 : term243.
Proof. exact (EQ_MP (@lem1540346) (@lem0)). Qed.
Lemma lem1540348 (y : real) (x : real) (h1 : term239 y x) : term262 x.
Proof. exact (conj (@lem1540347) (@lem1540337 y x h1)). Qed.
Lemma lem1540350 (x : real) (y : real) : term247 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1540351 (x : real) : term263 x.
Proof. exact (@lem1540350 term103 (term82 x)). Qed.
Lemma lem1540352 (y : real) (x : real) (h1 : term239 y x) : term264 x.
Proof. exact (@lem1540351 x (@lem1540348 y x h1)). Qed.
Lemma lem1540353 (x : real) : (term265 x) = (term82 x).
Proof. exact (@lem1483460 (term82 x)). Qed.
Lemma lem1540354 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540355 (x : real) : (term266 x) = (term195 x).
Proof. exact (MK_COMB (@lem1540354) (@lem1540353 x)). Qed.
Lemma lem1540356 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540357 (x : real) : (term264 x) = (term196 x).
Proof. exact (MK_COMB (@lem1540355 x) (@lem1540356)). Qed.
Lemma lem1540358 (y : real) (x : real) (h1 : term239 y x) : term196 x.
Proof. exact (EQ_MP (@lem1540357 x) (@lem1540352 y x h1)). Qed.
Lemma lem1540360 (y : real) : term251 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1540361 (x : real) : term251 x.
Proof. exact (@lem1540360 x). Qed.
Lemma lem1540362 (y : real) (x : real) (h1 : term239 y x) : term252 x.
Proof. exact (@lem1540361 x (@lem1540334 y x h1)). Qed.
Lemma lem1540363 (y : real) (x : real) (h1 : term239 y x) : term267 x.
Proof. exact (@lem1540362 y x h1 term103). Qed.
Lemma lem1540364 (x : real) : (term267 x) = ((term105 x) = term1).
Proof. exact (eq_refl (term267 x)). Qed.
Lemma lem1540365 (y : real) (x : real) (h1 : term239 y x) : (term105 x) = term1.
Proof. exact (EQ_MP (@lem1540364 x) (@lem1540363 y x h1)). Qed.
Lemma lem1540366 (x : real) : (term105 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540367 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1540368 (x : real) : (term268 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1540367) (@lem1540366 x)). Qed.
Lemma lem1540369 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540370 (x : real) : ((term105 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1540368 x) (@lem1540369)). Qed.
Lemma lem1540371 (y : real) (x : real) (h1 : term239 y x) : x = term1.
Proof. exact (EQ_MP (@lem1540370 x) (@lem1540365 y x h1)). Qed.
Lemma lem1540372 (y : real) (x : real) (h1 : term239 y x) : term269 x.
Proof. exact (conj (@lem1540371 y x h1) (@lem1540358 y x h1)). Qed.
Lemma lem1540374 (x : real) (y : real) : term255 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1540375 (x : real) : term270 x.
Proof. exact (@lem1540374 x (term82 x)). Qed.
Lemma lem1540376 (y : real) (x : real) (h1 : term239 y x) : term271 x.
Proof. exact (@lem1540375 x (@lem1540372 y x h1)). Qed.
Lemma lem1540377 (x : real) : (term201 x) = (term172 x).
Proof. exact (@lem1483442 term94 x). Qed.
Lemma lem1540379 (m : nat) : (term173 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540380 : term174 = term1.
Proof. exact (@lem1540379 term39). Qed.
Lemma lem1540381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540382 : term175 = term176.
Proof. exact (MK_COMB (@lem1540381) (@lem1540380)). Qed.
Lemma lem1540383 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1540384 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1540382) (@lem1540383 x)). Qed.
Lemma lem1540385 (x : real) : (term201 x) = (term177 x).
Proof. exact (TRANS (@lem1540377 x) (@lem1540384 x)). Qed.
Lemma lem1540386 (x : real) : (term177 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1540387 (x : real) : (term201 x) = term1.
Proof. exact (TRANS (@lem1540385 x) (@lem1540386 x)). Qed.
Lemma lem1540388 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540389 (x : real) : (term272 x) = term259.
Proof. exact (MK_COMB (@lem1540388) (@lem1540387 x)). Qed.
Lemma lem1540390 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1540391 (x : real) : (term271 x) = term260.
Proof. exact (MK_COMB (@lem1540389 x) (@lem1540390)). Qed.
Lemma lem1540392 (y : real) (x : real) (h1 : term239 y x) : term260.
Proof. exact (EQ_MP (@lem1540391 x) (@lem1540376 y x h1)). Qed.
Lemma lem1540394 (n : nat) (m : nat) : (term242 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540395 : term260 = term261.
Proof. exact (@lem1540394 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1540396 : term261 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1540397 : term260 = False.
Proof. exact (TRANS (@lem1540395) (@lem1540396)). Qed.
Lemma lem1540398 (y : real) (x : real) (h1 : term239 y x) : False.
Proof. exact (EQ_MP (@lem1540397) (@lem1540392 y x h1)). Qed.
Lemma lem1540399 (y : real) (x : real) (h1 : term241 y x) : False.
Proof. exact (or_elim (@lem1540262 y x h1) (fun h0 : term189 y x => @lem1540330 y x h0) (fun h0 : term239 y x => @lem1540398 y x h0)). Qed.
Lemma lem1540400 (y : real) (x : real) (h1 : term43 y x) : term43 y x.
Proof. exact (h1). Qed.
Lemma lem1540401 (y : real) (x : real) (h1 : term43 y x) : term241 y x.
Proof. exact (EQ_MP (@lem1540261 y x) (@lem1540400 y x h1)). Qed.
Lemma lem1540402 (y : real) (x : real) (h1 : term43 y x) : (term241 y x) = False.
Proof. exact (prop_ext (fun h2 : term241 y x => @lem1540399 y x h2) (fun h2 : False => @lem1540401 y x h1)). Qed.
Lemma lem1540403 (y : real) (x : real) (h1 : term43 y x) : False.
Proof. exact (EQ_MP (@lem1540402 y x h1) (@lem1540401 y x h1)). Qed.
Lemma lem1540404 (x : real) (h1 : term45 x) : term45 x.
Proof. exact (h1). Qed.
Lemma lem1540405 (x : real) (h1 : term45 x) : False.
Proof. exact (ex_elim (@lem1540404 x h1) (fun y : real => fun h0 : term44 x y => @lem1540403 y x h0)). Qed.
Lemma lem1540406 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1540407 (h1 : term47) : False.
Proof. exact (ex_elim (@lem1540406 h1) (fun x : real => fun h0 : term46 x => @lem1540405 x h0)). Qed.
Lemma lem1540408 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1540409 (h1 : term19) : term47.
Proof. exact (EQ_MP (@lem1539839) (@lem1540408 h1)). Qed.
Lemma lem1540410 (h1 : term19) : term47 = False.
Proof. exact (prop_ext (fun h2 : term47 => @lem1540407 h2) (fun h2 : False => @lem1540409 h1)). Qed.
Lemma lem1540411 (h1 : term19) : False.
Proof. exact (EQ_MP (@lem1540410 h1) (@lem1540409 h1)). Qed.
Lemma lem1540412 : term273.
Proof. exact (fun h0 : term19 => @lem1540411 h0). Qed.
Lemma lem1540413 : term274.
Proof. exact (@lem1386578 term275). Qed.
Lemma lem1540414 : term275.
Proof. exact (@lem1540413 (@lem1540412)). Qed.
