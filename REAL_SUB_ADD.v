Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_ADD_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483482_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1504656 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504657 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1504656 (term4 x)). Qed.
Lemma lem1504658 (y : real) (x : real) : (term5 x y) = ((term6 x y) = x).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1504659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504661 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1504659) (@lem1504658 y x)). Qed.
Lemma lem1504662 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1504661 y x)). Qed.
Lemma lem1504663 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504664 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1504663) (@lem1504662 x)). Qed.
Lemma lem1504665 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1504657 x) (@lem1504664 x)). Qed.
Lemma lem1504666 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504667 : term12 = term13.
Proof. exact (@lem1504666 term14). Qed.
Lemma lem1504668 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1504669 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504670 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1504669) (@lem1504668 x)). Qed.
Lemma lem1504671 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1504670 x) (@lem1504665 x)). Qed.
Lemma lem1504672 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1504671 x)). Qed.
Lemma lem1504673 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504674 : term13 = term20.
Proof. exact (MK_COMB (@lem1504673) (@lem1504672)). Qed.
Lemma lem1504676 : term12 = term20.
Proof. exact (TRANS (@lem1504667) (@lem1504674)). Qed.
Lemma lem1504679 (y : real) (x : real) : (term8 y x) = (term8 y x).
Proof. exact (eq_refl (term8 y x)). Qed.
Lemma lem1504680 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1504679 y x)). Qed.
Lemma lem1504681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504682 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1504681) (@lem1504680 x)). Qed.
Lemma lem1504683 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1504682 x)). Qed.
Lemma lem1504684 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504685 : term20 = term20.
Proof. exact (MK_COMB (@lem1504684) (@lem1504683)). Qed.
Lemma lem1504686 : term12 = term20.
Proof. exact (TRANS (@lem1504676) (@lem1504685)). Qed.
Lemma lem1504687 (y : real) (x : real) : (term8 y x) = (term21 y x).
Proof. exact (@lem1483554 (term6 x y) x). Qed.
Lemma lem1504688 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504689 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504702 (x : real) (y : real) : (real_sub x y) = (term22 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1504703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504704 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1504703) (@lem1504702 x y)). Qed.
Lemma lem1504705 (x : real) (y : real) : (term6 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1504704 x y) (@lem1504689 y)). Qed.
Lemma lem1504706 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483482 x (term27 y) y). Qed.
Lemma lem1504707 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1504709 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504710 : term33 = term32.
Proof. exact (@lem1504709 term34). Qed.
Lemma lem1504711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504712 : term35 = term36.
Proof. exact (MK_COMB (@lem1504711) (@lem1504710)). Qed.
Lemma lem1504713 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504714 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1504712) (@lem1504713 y)). Qed.
Lemma lem1504715 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1504707 y) (@lem1504714 y)). Qed.
Lemma lem1504716 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1504717 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1504715 y) (@lem1504716 y)). Qed.
Lemma lem1504718 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1504719 (y : real) (x : real) : (term26 x y) = (term38 x).
Proof. exact (MK_COMB (@lem1504718 x) (@lem1504717 y)). Qed.
Lemma lem1504720 (y : real) (x : real) : (term25 x y) = (term38 x).
Proof. exact (TRANS (@lem1504706 x y) (@lem1504719 y x)). Qed.
Lemma lem1504721 (x : real) : (term38 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1504722 (y : real) (x : real) : (term25 x y) = x.
Proof. exact (TRANS (@lem1504720 y x) (@lem1504721 x)). Qed.
Lemma lem1504723 (y : real) (x : real) : (term6 x y) = x.
Proof. exact (TRANS (@lem1504705 x y) (@lem1504722 y x)). Qed.
Lemma lem1504724 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1504725 (y : real) (x : real) : (term39 x y) = (real_sub x).
Proof. exact (MK_COMB (@lem1504724) (@lem1504723 y x)). Qed.
Lemma lem1504726 (y : real) (x : real) : (term40 y x) = (real_sub x x).
Proof. exact (MK_COMB (@lem1504725 y x) (@lem1504688 x)). Qed.
Lemma lem1504727 (x : real) : (real_sub x x) = (term41 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1504731 (x : real) : (term41 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1504733 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504734 : term33 = term32.
Proof. exact (@lem1504733 term34). Qed.
Lemma lem1504735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504736 : term35 = term36.
Proof. exact (MK_COMB (@lem1504735) (@lem1504734)). Qed.
Lemma lem1504737 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504738 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1504736) (@lem1504737 x)). Qed.
Lemma lem1504739 (x : real) : (term41 x) = (term37 x).
Proof. exact (TRANS (@lem1504731 x) (@lem1504738 x)). Qed.
Lemma lem1504740 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1504742 (x : real) : (term41 x) = term32.
Proof. exact (TRANS (@lem1504739 x) (@lem1504740 x)). Qed.
Lemma lem1504743 (x : real) : (real_sub x x) = term32.
Proof. exact (TRANS (@lem1504727 x) (@lem1504742 x)). Qed.
Lemma lem1504744 (y : real) (x : real) : (term40 y x) = term32.
Proof. exact (TRANS (@lem1504726 y x) (@lem1504743 x)). Qed.
Lemma lem1504745 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1504746 (y : real) (x : real) : (term42 y x) = term43.
Proof. exact (MK_COMB (@lem1504745) (@lem1504744 y x)). Qed.
Lemma lem1504747 : term43 = term44.
Proof. exact (@lem1483512 term32). Qed.
Lemma lem1504749 (x : nat) : (term45 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1504750 : term44 = term32.
Proof. exact (@lem1504749 term34). Qed.
Lemma lem1504751 : term43 = term32.
Proof. exact (TRANS (@lem1504747) (@lem1504750)). Qed.
Lemma lem1504752 (y : real) (x : real) : (term46 y x) = (term46 y x).
Proof. exact (eq_refl (term46 y x)). Qed.
Lemma lem1504753 (y : real) (x : real) : ((term42 y x) = term43) = ((term42 y x) = term32).
Proof. exact (MK_COMB (@lem1504752 y x) (@lem1504751)). Qed.
Lemma lem1504754 (y : real) (x : real) : (term42 y x) = term32.
Proof. exact (EQ_MP (@lem1504753 y x) (@lem1504746 y x)). Qed.
Lemma lem1504755 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504756 (y : real) (x : real) : (term47 y x) = term48.
Proof. exact (MK_COMB (@lem1504755) (@lem1504754 y x)). Qed.
Lemma lem1504757 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1504758 (y : real) (x : real) : (term49 y x) = term50.
Proof. exact (MK_COMB (@lem1504756 y x) (@lem1504757)). Qed.
Lemma lem1504759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504760 (y : real) (x : real) : (term51 y x) = term48.
Proof. exact (MK_COMB (@lem1504759) (@lem1504744 y x)). Qed.
Lemma lem1504761 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1504762 (y : real) (x : real) : (term52 y x) = term50.
Proof. exact (MK_COMB (@lem1504760 y x) (@lem1504761)). Qed.
Lemma lem1504763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504764 (y : real) (x : real) : (term53 y x) = term54.
Proof. exact (MK_COMB (@lem1504763) (@lem1504762 y x)). Qed.
Lemma lem1504765 (y : real) (x : real) : (term21 y x) = term55.
Proof. exact (MK_COMB (@lem1504764 y x) (@lem1504758 y x)). Qed.
Lemma lem1504766 (y : real) (x : real) : (term8 y x) = term55.
Proof. exact (TRANS (@lem1504687 y x) (@lem1504765 y x)). Qed.
Lemma lem1504767 (x : real) : (term10 x) = term56.
Proof. exact (fun_ext (fun y : real => @lem1504766 y x)). Qed.
Lemma lem1504768 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504769 (x : real) : (term11 x) = term57.
Proof. exact (MK_COMB (@lem1504768) (@lem1504767 x)). Qed.
Lemma lem1504770 : term19 = term58.
Proof. exact (fun_ext (fun x : real => @lem1504769 x)). Qed.
Lemma lem1504771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504772 : term20 = term59.
Proof. exact (MK_COMB (@lem1504771) (@lem1504770)). Qed.
Lemma lem1504773 : term12 = term59.
Proof. exact (TRANS (@lem1504686) (@lem1504772)). Qed.
Lemma lem1504775 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1504776 (t : Prop) : (term61 t) = t.
Proof. exact (@lem1504775 real t). Qed.
Lemma lem1504777 : term59 = term57.
Proof. exact (@lem1504776 term57). Qed.
Lemma lem1504779 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1504780 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term65 P Q).
Proof. exact (@lem1504779 real P Q). Qed.
Lemma lem1504781 : term66 = term67.
Proof. exact (@lem1504780 term68 term68). Qed.
Lemma lem1504782 (y : real) : (term69 y) = term50.
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1504783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504784 (y : real) : (term70 y) = term54.
Proof. exact (MK_COMB (@lem1504783) (@lem1504782 y)). Qed.
Lemma lem1504785 (y : real) : (term69 y) = term50.
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1504786 (y : real) : (term71 y) = term55.
Proof. exact (MK_COMB (@lem1504784 y) (@lem1504785 y)). Qed.
Lemma lem1504787 : term72 = term56.
Proof. exact (fun_ext (fun y : real => @lem1504786 y)). Qed.
Lemma lem1504788 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504789 : term66 = term57.
Proof. exact (MK_COMB (@lem1504788) (@lem1504787)). Qed.
Lemma lem1504790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1504791 : term73 = term74.
Proof. exact (MK_COMB (@lem1504790) (@lem1504789)). Qed.
Lemma lem1504792 (y : real) : (term69 y) = term50.
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1504793 : term75 = term68.
Proof. exact (fun_ext (fun y : real => @lem1504792 y)). Qed.
Lemma lem1504794 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504795 : term76 = term77.
Proof. exact (MK_COMB (@lem1504794) (@lem1504793)). Qed.
Lemma lem1504796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504797 : term78 = term79.
Proof. exact (MK_COMB (@lem1504796) (@lem1504795)). Qed.
Lemma lem1504798 (y : real) : (term69 y) = term50.
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1504799 : term75 = term68.
Proof. exact (fun_ext (fun y : real => @lem1504798 y)). Qed.
Lemma lem1504800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504801 : term76 = term77.
Proof. exact (MK_COMB (@lem1504800) (@lem1504799)). Qed.
Lemma lem1504802 : term67 = term80.
Proof. exact (MK_COMB (@lem1504797) (@lem1504801)). Qed.
Lemma lem1504803 : (term66 = term67) = (term57 = term80).
Proof. exact (MK_COMB (@lem1504791) (@lem1504802)). Qed.
Lemma lem1504804 : term57 = term80.
Proof. exact (EQ_MP (@lem1504803) (@lem1504781)). Qed.
Lemma lem1504805 : term59 = term80.
Proof. exact (TRANS (@lem1504777) (@lem1504804)). Qed.
Lemma lem1504807 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1504808 (t : Prop) : (term61 t) = t.
Proof. exact (@lem1504807 real t). Qed.
Lemma lem1504809 : term77 = term50.
Proof. exact (@lem1504808 term50). Qed.
Lemma lem1504810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504811 : term79 = term54.
Proof. exact (MK_COMB (@lem1504810) (@lem1504809)). Qed.
Lemma lem1504813 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1504814 (t : Prop) : (term61 t) = t.
Proof. exact (@lem1504813 real t). Qed.
Lemma lem1504815 : term77 = term50.
Proof. exact (@lem1504814 term50). Qed.
Lemma lem1504816 : term80 = term55.
Proof. exact (MK_COMB (@lem1504811) (@lem1504815)). Qed.
Lemma lem1504819 : term59 = term55.
Proof. exact (TRANS (@lem1504805) (@lem1504816)). Qed.
Lemma lem1504828 : term12 = term55.
Proof. exact (TRANS (@lem1504773) (@lem1504819)). Qed.
Lemma lem1504838 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem1504839 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1504841 (n : nat) (m : nat) : (term81 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504842 : term50 = term82.
Proof. exact (@lem1504841 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1504843 : term82 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1504844 : term50 = False.
Proof. exact (TRANS (@lem1504842) (@lem1504843)). Qed.
Lemma lem1504845 (h1 : term50) : False.
Proof. exact (EQ_MP (@lem1504844) (@lem1504839 h1)). Qed.
Lemma lem1504846 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1504848 (n : nat) (m : nat) : (term81 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504849 : term50 = term82.
Proof. exact (@lem1504848 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1504850 : term82 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1504851 : term50 = False.
Proof. exact (TRANS (@lem1504849) (@lem1504850)). Qed.
Lemma lem1504852 (h1 : term50) : False.
Proof. exact (EQ_MP (@lem1504851) (@lem1504846 h1)). Qed.
Lemma lem1504853 (h1 : term55) : False.
Proof. exact (or_elim (@lem1504838 h1) (fun h0 : term50 => @lem1504845 h0) (fun h0 : term50 => @lem1504852 h0)). Qed.
Lemma lem1504855 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem1504856 (h1 : term55) : term55 = False.
Proof. exact (prop_ext (fun h2 : term55 => @lem1504853 h1) (fun h2 : False => @lem1504855 h1)). Qed.
Lemma lem1504857 (h1 : term55) : False.
Proof. exact (EQ_MP (@lem1504856 h1) (@lem1504855 h1)). Qed.
Lemma lem1504858 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1504859 (h1 : term12) : term55.
Proof. exact (EQ_MP (@lem1504828) (@lem1504858 h1)). Qed.
Lemma lem1504860 (h1 : term12) : term55 = False.
Proof. exact (prop_ext (fun h2 : term55 => @lem1504857 h2) (fun h2 : False => @lem1504859 h1)). Qed.
Lemma lem1504861 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1504860 h1) (@lem1504859 h1)). Qed.
Lemma lem1504862 : term83.
Proof. exact (fun h0 : term12 => @lem1504861 h0). Qed.
Lemma lem1504863 : term84.
Proof. exact (@lem1386578 term85). Qed.
Lemma lem1504864 : term85.
Proof. exact (@lem1504863 (@lem1504862)). Qed.
