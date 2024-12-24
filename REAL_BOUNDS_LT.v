Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_BOUNDS_LT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1553674 (x : real) (k : real) : (term0 x k) = (term1 x k).
Proof. exact (@lem17045 (term2 k x) (real_lt x k)). Qed.
Lemma lem1553679 (x : real) (k : real) : (term3 x k) = (term3 x k).
Proof. exact (eq_refl (term3 x k)). Qed.
Lemma lem1553680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553681 (x : real) (k : real) : (term4 x k) = (term5 x k).
Proof. exact (MK_COMB (@lem1553680) (@lem1553674 x k)). Qed.
Lemma lem1553682 (x : real) (k : real) : (term6 x k) = (term7 x k).
Proof. exact (MK_COMB (@lem1553681 x k) (@lem1553679 x k)). Qed.
Lemma lem1553687 (x : real) (k : real) : (term8 x k) = (term8 x k).
Proof. exact (eq_refl (term8 x k)). Qed.
Lemma lem1553688 (x : real) (k : real) : (term9 x k) = (term10 x k).
Proof. exact (MK_COMB (@lem1553687 x k) (@lem1553682 x k)). Qed.
Lemma lem1553689 (x : real) (k : real) : (term11 x k) = (term9 x k).
Proof. exact (@lem17646 (term12 x k) (term3 x k)). Qed.
Lemma lem1553690 (x : real) (k : real) : (term11 x k) = (term10 x k).
Proof. exact (TRANS (@lem1553689 x k) (@lem1553688 x k)). Qed.
Lemma lem1553691 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1553692 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1553691 (term17 x)). Qed.
Lemma lem1553693 (x : real) (k : real) : (term18 x k) = ((term12 x k) = (term3 x k)).
Proof. exact (eq_refl (term18 x k)). Qed.
Lemma lem1553694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1553695 (x : real) (k : real) : (term19 x k) = (term11 x k).
Proof. exact (MK_COMB (@lem1553694) (@lem1553693 x k)). Qed.
Lemma lem1553696 (x : real) (k : real) : (term19 x k) = (term10 x k).
Proof. exact (TRANS (@lem1553695 x k) (@lem1553690 x k)). Qed.
Lemma lem1553697 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun k : real => @lem1553696 x k)). Qed.
Lemma lem1553698 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553699 (x : real) : (term16 x) = (term22 x).
Proof. exact (MK_COMB (@lem1553698) (@lem1553697 x)). Qed.
Lemma lem1553700 (x : real) : (term15 x) = (term22 x).
Proof. exact (TRANS (@lem1553692 x) (@lem1553699 x)). Qed.
Lemma lem1553701 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1553702 : term23 = term24.
Proof. exact (@lem1553701 term25). Qed.
Lemma lem1553703 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1553704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1553705 (x : real) : (term28 x) = (term15 x).
Proof. exact (MK_COMB (@lem1553704) (@lem1553703 x)). Qed.
Lemma lem1553706 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1553705 x) (@lem1553700 x)). Qed.
Lemma lem1553707 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1553706 x)). Qed.
Lemma lem1553708 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553709 : term24 = term31.
Proof. exact (MK_COMB (@lem1553708) (@lem1553707)). Qed.
Lemma lem1553711 : term23 = term31.
Proof. exact (TRANS (@lem1553702) (@lem1553709)). Qed.
Lemma lem1553738 (x : real) (k : real) : (term10 x k) = (term10 x k).
Proof. exact (eq_refl (term10 x k)). Qed.
Lemma lem1553739 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun k : real => @lem1553738 x k)). Qed.
Lemma lem1553740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553741 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1553740) (@lem1553739 x)). Qed.
Lemma lem1553742 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1553741 x)). Qed.
Lemma lem1553743 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553744 : term31 = term31.
Proof. exact (MK_COMB (@lem1553743) (@lem1553742)). Qed.
Lemma lem1553745 : term23 = term31.
Proof. exact (TRANS (@lem1553711) (@lem1553744)). Qed.
Lemma lem1553746 (x : real) (k : real) : (term2 k x) = (term32 x k).
Proof. exact (@lem1483521 x (real_neg k)). Qed.
Lemma lem1553753 (k : real) : (real_neg k) = (term33 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1553756 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1553757 (x : real) (k : real) : (term34 x k) = (term35 x k).
Proof. exact (MK_COMB (@lem1553756 x) (@lem1553753 k)). Qed.
Lemma lem1553758 (x : real) (k : real) : (term35 x k) = (term36 x k).
Proof. exact (@lem1483519 x (term33 k)). Qed.
Lemma lem1553759 (k : real) : (term37 k) = (term38 k).
Proof. exact (@lem1483476 term39 term39 k). Qed.
Lemma lem1553761 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1553762 : term42 = term43.
Proof. exact (@lem1553761 term44 term44). Qed.
Lemma lem1553763 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1553764 : term46 = term44.
Proof. exact (EQ_MP (@lem1553763) (@lem940073)). Qed.
Lemma lem1553765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1553766 : term43 = term47.
Proof. exact (MK_COMB (@lem1553765) (@lem1553764)). Qed.
Lemma lem1553767 : term42 = term47.
Proof. exact (TRANS (@lem1553762) (@lem1553766)). Qed.
Lemma lem1553768 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553769 : term48 = term49.
Proof. exact (MK_COMB (@lem1553768) (@lem1553767)). Qed.
Lemma lem1553770 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1553771 (k : real) : (term38 k) = (term50 k).
Proof. exact (MK_COMB (@lem1553769) (@lem1553770 k)). Qed.
Lemma lem1553772 (k : real) : (term37 k) = (term50 k).
Proof. exact (TRANS (@lem1553759 k) (@lem1553771 k)). Qed.
Lemma lem1553773 (k : real) : (term50 k) = k.
Proof. exact (@lem1483436 k). Qed.
Lemma lem1553774 (k : real) : (term37 k) = k.
Proof. exact (TRANS (@lem1553772 k) (@lem1553773 k)). Qed.
Lemma lem1553775 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1553776 (x : real) (k : real) : (term36 x k) = (real_add x k).
Proof. exact (MK_COMB (@lem1553775 x) (@lem1553774 k)). Qed.
Lemma lem1553777 (k : real) (x : real) : (real_add x k) = (real_add k x).
Proof. exact (@lem1483488 k x). Qed.
Lemma lem1553778 (k : real) (x : real) : (term36 x k) = (real_add k x).
Proof. exact (TRANS (@lem1553776 x k) (@lem1553777 k x)). Qed.
Lemma lem1553779 (k : real) (x : real) : (term35 x k) = (real_add k x).
Proof. exact (TRANS (@lem1553758 x k) (@lem1553778 k x)). Qed.
Lemma lem1553780 (k : real) (x : real) : (term34 x k) = (real_add k x).
Proof. exact (TRANS (@lem1553757 x k) (@lem1553779 k x)). Qed.
Lemma lem1553781 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553782 (k : real) (x : real) : (term51 x k) = (term52 k x).
Proof. exact (MK_COMB (@lem1553781) (@lem1553780 k x)). Qed.
Lemma lem1553783 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553784 (k : real) (x : real) : (term32 x k) = (term54 k x).
Proof. exact (MK_COMB (@lem1553782 k x) (@lem1553783)). Qed.
Lemma lem1553785 (k : real) (x : real) : (term2 k x) = (term54 k x).
Proof. exact (TRANS (@lem1553746 x k) (@lem1553784 k x)). Qed.
Lemma lem1553786 (k : real) (x : real) : (real_lt x k) = (term55 k x).
Proof. exact (@lem1483521 k x). Qed.
Lemma lem1553799 (k : real) (x : real) : (real_sub k x) = (term56 k x).
Proof. exact (@lem1483519 k x). Qed.
Lemma lem1553800 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553801 (k : real) (x : real) : (term57 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1553800) (@lem1553799 k x)). Qed.
Lemma lem1553802 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553803 (k : real) (x : real) : (term55 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1553801 k x) (@lem1553802)). Qed.
Lemma lem1553804 (k : real) (x : real) : (real_lt x k) = (term59 k x).
Proof. exact (TRANS (@lem1553786 k x) (@lem1553803 k x)). Qed.
Lemma lem1553805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553806 (k : real) (x : real) : (term60 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1553805) (@lem1553785 k x)). Qed.
Lemma lem1553807 (k : real) (x : real) : (term12 x k) = (term62 k x).
Proof. exact (MK_COMB (@lem1553806 k x) (@lem1553804 k x)). Qed.
Lemma lem1553808 (x : real) (k : real) : (term63 x k) = (term64 x k).
Proof. exact (@lem1483531 (real_abs x) k). Qed.
Lemma lem1553814 (x : real) (k : real) : (term65 x k) = (term66 x k).
Proof. exact (@lem1483519 (real_abs x) k). Qed.
Lemma lem1553819 (k : real) (x : real) : (term66 x k) = (term67 k x).
Proof. exact (@lem1483488 (term33 k) (real_abs x)). Qed.
Lemma lem1553821 (k : real) (x : real) : (term65 x k) = (term67 k x).
Proof. exact (TRANS (@lem1553814 x k) (@lem1553819 k x)). Qed.
Lemma lem1553822 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553823 (k : real) (x : real) : (term68 x k) = (term69 k x).
Proof. exact (MK_COMB (@lem1553822) (@lem1553821 k x)). Qed.
Lemma lem1553824 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553825 (k : real) (x : real) : (term64 x k) = (term70 k x).
Proof. exact (MK_COMB (@lem1553823 k x) (@lem1553824)). Qed.
Lemma lem1553826 (k : real) (x : real) : (term63 x k) = (term70 k x).
Proof. exact (TRANS (@lem1553808 x k) (@lem1553825 k x)). Qed.
Lemma lem1553827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553828 (k : real) (x : real) : (term71 x k) = (term72 k x).
Proof. exact (MK_COMB (@lem1553827) (@lem1553807 k x)). Qed.
Lemma lem1553829 (k : real) (x : real) : (term73 x k) = (term74 k x).
Proof. exact (MK_COMB (@lem1553828 k x) (@lem1553826 k x)). Qed.
Lemma lem1553830 (k : real) (x : real) : (term75 k x) = (term76 k x).
Proof. exact (@lem1483531 (real_neg k) x). Qed.
Lemma lem1553831 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1553838 (k : real) : (real_neg k) = (term33 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1553839 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1553840 (k : real) : (term77 k) = (term78 k).
Proof. exact (MK_COMB (@lem1553839) (@lem1553838 k)). Qed.
Lemma lem1553841 (k : real) (x : real) : (term79 k x) = (term80 k x).
Proof. exact (MK_COMB (@lem1553840 k) (@lem1553831 x)). Qed.
Lemma lem1553848 (k : real) (x : real) : (term80 k x) = (term81 k x).
Proof. exact (@lem1483519 (term33 k) x). Qed.
Lemma lem1553849 (k : real) (x : real) : (term79 k x) = (term81 k x).
Proof. exact (TRANS (@lem1553841 k x) (@lem1553848 k x)). Qed.
Lemma lem1553850 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553851 (k : real) (x : real) : (term82 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1553850) (@lem1553849 k x)). Qed.
Lemma lem1553852 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553853 (k : real) (x : real) : (term76 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1553851 k x) (@lem1553852)). Qed.
Lemma lem1553854 (k : real) (x : real) : (term75 k x) = (term84 k x).
Proof. exact (TRANS (@lem1553830 k x) (@lem1553853 k x)). Qed.
Lemma lem1553855 (x : real) (k : real) : (term85 x k) = (term86 x k).
Proof. exact (@lem1483531 x k). Qed.
Lemma lem1553861 (x : real) (k : real) : (real_sub x k) = (term56 x k).
Proof. exact (@lem1483519 x k). Qed.
Lemma lem1553866 (k : real) (x : real) : (term56 x k) = (term87 k x).
Proof. exact (@lem1483488 (term33 k) x). Qed.
Lemma lem1553868 (k : real) (x : real) : (real_sub x k) = (term87 k x).
Proof. exact (TRANS (@lem1553861 x k) (@lem1553866 k x)). Qed.
Lemma lem1553869 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553870 (k : real) (x : real) : (term88 x k) = (term89 k x).
Proof. exact (MK_COMB (@lem1553869) (@lem1553868 k x)). Qed.
Lemma lem1553871 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553872 (k : real) (x : real) : (term86 x k) = (term90 k x).
Proof. exact (MK_COMB (@lem1553870 k x) (@lem1553871)). Qed.
Lemma lem1553873 (k : real) (x : real) : (term85 x k) = (term90 k x).
Proof. exact (TRANS (@lem1553855 x k) (@lem1553872 k x)). Qed.
Lemma lem1553874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553875 (k : real) (x : real) : (term91 k x) = (term92 k x).
Proof. exact (MK_COMB (@lem1553874) (@lem1553854 k x)). Qed.
Lemma lem1553876 (k : real) (x : real) : (term1 x k) = (term93 k x).
Proof. exact (MK_COMB (@lem1553875 k x) (@lem1553873 k x)). Qed.
Lemma lem1553877 (k : real) (x : real) : (term3 x k) = (term94 k x).
Proof. exact (@lem1483521 k (real_abs x)). Qed.
Lemma lem1553890 (k : real) (x : real) : (term95 k x) = (term96 k x).
Proof. exact (@lem1483519 k (real_abs x)). Qed.
Lemma lem1553891 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553892 (k : real) (x : real) : (term97 k x) = (term98 k x).
Proof. exact (MK_COMB (@lem1553891) (@lem1553890 k x)). Qed.
Lemma lem1553893 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553894 (k : real) (x : real) : (term94 k x) = (term99 k x).
Proof. exact (MK_COMB (@lem1553892 k x) (@lem1553893)). Qed.
Lemma lem1553895 (k : real) (x : real) : (term3 x k) = (term99 k x).
Proof. exact (TRANS (@lem1553877 k x) (@lem1553894 k x)). Qed.
Lemma lem1553896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553897 (k : real) (x : real) : (term5 x k) = (term100 k x).
Proof. exact (MK_COMB (@lem1553896) (@lem1553876 k x)). Qed.
Lemma lem1553898 (k : real) (x : real) : (term7 x k) = (term101 k x).
Proof. exact (MK_COMB (@lem1553897 k x) (@lem1553895 k x)). Qed.
Lemma lem1553899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553900 (k : real) (x : real) : (term8 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1553899) (@lem1553829 k x)). Qed.
Lemma lem1553901 (k : real) (x : real) : (term10 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1553900 k x) (@lem1553898 k x)). Qed.
Lemma lem1553902 (x : real) : (term21 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1553901 k x)). Qed.
Lemma lem1553903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553904 (x : real) : (term22 x) = (term105 x).
Proof. exact (MK_COMB (@lem1553903) (@lem1553902 x)). Qed.
Lemma lem1553905 : term30 = term106.
Proof. exact (fun_ext (fun x : real => @lem1553904 x)). Qed.
Lemma lem1553906 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553907 : term31 = term107.
Proof. exact (MK_COMB (@lem1553906) (@lem1553905)). Qed.
Lemma lem1553908 : term23 = term107.
Proof. exact (TRANS (@lem1553745) (@lem1553907)). Qed.
Lemma lem1553914 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1553915 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1553914 real P Q). Qed.
Lemma lem1553916 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem1553915 (term114 x) (term115 x)). Qed.
Lemma lem1553917 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1553918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553919 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1553918) (@lem1553917 k x)). Qed.
Lemma lem1553920 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1553921 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1553919 k x) (@lem1553920 k x)). Qed.
Lemma lem1553922 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1553921 k x)). Qed.
Lemma lem1553923 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553924 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1553923) (@lem1553922 x)). Qed.
Lemma lem1553925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1553926 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1553925) (@lem1553924 x)). Qed.
Lemma lem1553927 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1553928 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1553927 k x)). Qed.
Lemma lem1553929 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553930 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1553929) (@lem1553928 x)). Qed.
Lemma lem1553931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553932 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1553931) (@lem1553930 x)). Qed.
Lemma lem1553933 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1553934 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1553933 k x)). Qed.
Lemma lem1553935 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1553936 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1553935) (@lem1553934 x)). Qed.
Lemma lem1553937 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1553932 x) (@lem1553936 x)). Qed.
Lemma lem1553938 (x : real) : ((term112 x) = (term113 x)) = ((term105 x) = (term131 x)).
Proof. exact (MK_COMB (@lem1553926 x) (@lem1553937 x)). Qed.
Lemma lem1553939 (x : real) : (term105 x) = (term131 x).
Proof. exact (EQ_MP (@lem1553938 x) (@lem1553916 x)). Qed.
Lemma lem1554036 : term106 = term132.
Proof. exact (fun_ext (fun x : real => @lem1553939 x)). Qed.
Lemma lem1554037 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554038 : term107 = term133.
Proof. exact (MK_COMB (@lem1554037) (@lem1554036)). Qed.
Lemma lem1554040 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1554041 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1554040 real P Q). Qed.
Lemma lem1554042 : term134 = term135.
Proof. exact (@lem1554041 term136 term137). Qed.
Lemma lem1554043 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1554044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554045 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1554044) (@lem1554043 x)). Qed.
Lemma lem1554046 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1554047 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1554045 x) (@lem1554046 x)). Qed.
Lemma lem1554048 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1554047 x)). Qed.
Lemma lem1554049 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554050 : term134 = term133.
Proof. exact (MK_COMB (@lem1554049) (@lem1554048)). Qed.
Lemma lem1554051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1554052 : term143 = term144.
Proof. exact (MK_COMB (@lem1554051) (@lem1554050)). Qed.
Lemma lem1554053 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1554054 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1554053 x)). Qed.
Lemma lem1554055 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554056 : term146 = term147.
Proof. exact (MK_COMB (@lem1554055) (@lem1554054)). Qed.
Lemma lem1554057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554058 : term148 = term149.
Proof. exact (MK_COMB (@lem1554057) (@lem1554056)). Qed.
Lemma lem1554059 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1554060 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1554059 x)). Qed.
Lemma lem1554061 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554062 : term151 = term152.
Proof. exact (MK_COMB (@lem1554061) (@lem1554060)). Qed.
Lemma lem1554063 : term135 = term153.
Proof. exact (MK_COMB (@lem1554058) (@lem1554062)). Qed.
Lemma lem1554064 : (term134 = term135) = (term133 = term153).
Proof. exact (MK_COMB (@lem1554052) (@lem1554063)). Qed.
Lemma lem1554065 : term133 = term153.
Proof. exact (EQ_MP (@lem1554064) (@lem1554042)). Qed.
Lemma lem1554170 : term107 = term153.
Proof. exact (TRANS (@lem1554038) (@lem1554065)). Qed.
Lemma lem1554172 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1554173 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1554172 real P Q). Qed.
Lemma lem1554174 : term135 = term134.
Proof. exact (@lem1554173 term136 term137). Qed.
Lemma lem1554175 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1554176 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1554175 x)). Qed.
Lemma lem1554177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554178 : term146 = term147.
Proof. exact (MK_COMB (@lem1554177) (@lem1554176)). Qed.
Lemma lem1554179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554180 : term148 = term149.
Proof. exact (MK_COMB (@lem1554179) (@lem1554178)). Qed.
Lemma lem1554181 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1554182 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1554181 x)). Qed.
Lemma lem1554183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554184 : term151 = term152.
Proof. exact (MK_COMB (@lem1554183) (@lem1554182)). Qed.
Lemma lem1554185 : term135 = term153.
Proof. exact (MK_COMB (@lem1554180) (@lem1554184)). Qed.
Lemma lem1554186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1554187 : term154 = term155.
Proof. exact (MK_COMB (@lem1554186) (@lem1554185)). Qed.
Lemma lem1554188 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1554189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554190 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1554189) (@lem1554188 x)). Qed.
Lemma lem1554191 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1554192 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1554190 x) (@lem1554191 x)). Qed.
Lemma lem1554193 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1554192 x)). Qed.
Lemma lem1554194 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554195 : term134 = term133.
Proof. exact (MK_COMB (@lem1554194) (@lem1554193)). Qed.
Lemma lem1554196 : (term135 = term134) = (term153 = term133).
Proof. exact (MK_COMB (@lem1554187) (@lem1554195)). Qed.
Lemma lem1554197 : term153 = term133.
Proof. exact (EQ_MP (@lem1554196) (@lem1554174)). Qed.
Lemma lem1554199 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1554200 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1554199 real P Q). Qed.
Lemma lem1554201 (x : real) : (term113 x) = (term112 x).
Proof. exact (@lem1554200 (term114 x) (term115 x)). Qed.
Lemma lem1554202 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1554203 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1554202 k x)). Qed.
Lemma lem1554204 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554205 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1554204) (@lem1554203 x)). Qed.
Lemma lem1554206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554207 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1554206) (@lem1554205 x)). Qed.
Lemma lem1554208 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1554209 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1554208 k x)). Qed.
Lemma lem1554210 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554211 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1554210) (@lem1554209 x)). Qed.
Lemma lem1554212 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1554207 x) (@lem1554211 x)). Qed.
Lemma lem1554213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1554214 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1554213) (@lem1554212 x)). Qed.
Lemma lem1554215 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1554216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554217 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1554216) (@lem1554215 k x)). Qed.
Lemma lem1554218 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1554219 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1554217 k x) (@lem1554218 k x)). Qed.
Lemma lem1554220 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1554219 k x)). Qed.
Lemma lem1554221 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554222 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1554221) (@lem1554220 x)). Qed.
Lemma lem1554223 (x : real) : ((term113 x) = (term112 x)) = ((term131 x) = (term105 x)).
Proof. exact (MK_COMB (@lem1554214 x) (@lem1554222 x)). Qed.
Lemma lem1554224 (x : real) : (term131 x) = (term105 x).
Proof. exact (EQ_MP (@lem1554223 x) (@lem1554201 x)). Qed.
Lemma lem1554225 : term132 = term106.
Proof. exact (fun_ext (fun x : real => @lem1554224 x)). Qed.
Lemma lem1554226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554227 : term133 = term107.
Proof. exact (MK_COMB (@lem1554226) (@lem1554225)). Qed.
Lemma lem1554228 : term153 = term107.
Proof. exact (TRANS (@lem1554197) (@lem1554227)). Qed.
Lemma lem1554229 : term107 = term107.
Proof. exact (TRANS (@lem1554170) (@lem1554228)). Qed.
Lemma lem1554232 : term23 = term107.
Proof. exact (TRANS (@lem1553908) (@lem1554229)). Qed.
Lemma lem1554249 (k : real) (x : real) : (term101 k x) = (term158 k x).
Proof. exact (@lem19367 (term84 k x) (term90 k x) (term99 k x)). Qed.
Lemma lem1554264 (k : real) (x : real) : (term102 k x) = (term102 k x).
Proof. exact (eq_refl (term102 k x)). Qed.
Lemma lem1554265 (k : real) (x : real) : (term103 k x) = (term159 k x).
Proof. exact (MK_COMB (@lem1554264 k x) (@lem1554249 k x)). Qed.
Lemma lem1554266 (x : real) : (term104 x) = (term160 x).
Proof. exact (fun_ext (fun k : real => @lem1554265 k x)). Qed.
Lemma lem1554267 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554268 (x : real) : (term105 x) = (term161 x).
Proof. exact (MK_COMB (@lem1554267) (@lem1554266 x)). Qed.
Lemma lem1554269 : term106 = term162.
Proof. exact (fun_ext (fun x : real => @lem1554268 x)). Qed.
Lemma lem1554270 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1554271 : term107 = term163.
Proof. exact (MK_COMB (@lem1554270) (@lem1554269)). Qed.
Lemma lem1554272 : term23 = term163.
Proof. exact (TRANS (@lem1554232) (@lem1554271)). Qed.
Lemma lem1554274 (k : real) (x : real) : (term164 k x) = (term74 k x).
Proof. exact (eq_refl (term164 k x)). Qed.
Lemma lem1554275 (k : real) (x : real) : (term74 k x) = (term164 k x).
Proof. exact (SYM (@lem1554274 k x)). Qed.
Lemma lem1554276 (k : real) (x : real) : (term164 k x) = (term165 k x).
Proof. exact (@lem1482981 (term166 x k) x). Qed.
Lemma lem1554277 (k : real) (x : real) : (term74 k x) = (term165 k x).
Proof. exact (TRANS (@lem1554275 k x) (@lem1554276 k x)). Qed.
Lemma lem1554278 (k : real) (x : real) : (term167 k x) = (term168 k x).
Proof. exact (eq_refl (term167 k x)). Qed.
Lemma lem1554279 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1554280 (k : real) (x : real) : (term170 k x) = (term171 k x).
Proof. exact (MK_COMB (@lem1554279 x) (@lem1554278 k x)). Qed.
Lemma lem1554281 (k : real) (x : real) : (term172 k x) = (term173 k x).
Proof. exact (eq_refl (term172 k x)). Qed.
Lemma lem1554282 (x : real) : (term174 x) = (term174 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1554283 (k : real) (x : real) : (term175 k x) = (term176 k x).
Proof. exact (MK_COMB (@lem1554282 x) (@lem1554281 k x)). Qed.
Lemma lem1554284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554285 (k : real) (x : real) : (term177 k x) = (term178 k x).
Proof. exact (MK_COMB (@lem1554284) (@lem1554283 k x)). Qed.
Lemma lem1554286 (k : real) (x : real) : (term165 k x) = (term179 k x).
Proof. exact (MK_COMB (@lem1554285 k x) (@lem1554280 k x)). Qed.
Lemma lem1554287 (k : real) (x : real) : (term180 k x) = (term180 k x).
Proof. exact (eq_refl (term180 k x)). Qed.
Lemma lem1554288 (k : real) (x : real) : ((term74 k x) = (term165 k x)) = ((term74 k x) = (term179 k x)).
Proof. exact (MK_COMB (@lem1554287 k x) (@lem1554286 k x)). Qed.
Lemma lem1554289 (k : real) (x : real) : (term74 k x) = (term179 k x).
Proof. exact (EQ_MP (@lem1554288 k x) (@lem1554277 k x)). Qed.
Lemma lem1554290 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483527 x term53). Qed.
Lemma lem1554296 (x : real) : (term183 x) = (term184 x).
Proof. exact (@lem1483519 x term53). Qed.
Lemma lem1554298 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1554299 : term186 = term53.
Proof. exact (@lem1554298 term44). Qed.
Lemma lem1554300 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1554301 (x : real) : (term184 x) = (term187 x).
Proof. exact (MK_COMB (@lem1554300 x) (@lem1554299)). Qed.
Lemma lem1554302 (x : real) : (term187 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1554303 (x : real) : (term184 x) = x.
Proof. exact (TRANS (@lem1554301 x) (@lem1554302 x)). Qed.
Lemma lem1554305 (x : real) : (term183 x) = x.
Proof. exact (TRANS (@lem1554296 x) (@lem1554303 x)). Qed.
Lemma lem1554306 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554307 (x : real) : (term188 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1554306) (@lem1554305 x)). Qed.
Lemma lem1554308 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554309 (x : real) : (term182 x) = (term181 x).
Proof. exact (MK_COMB (@lem1554307 x) (@lem1554308)). Qed.
Lemma lem1554310 (x : real) : (term181 x) = (term181 x).
Proof. exact (TRANS (@lem1554290 x) (@lem1554309 x)). Qed.
Lemma lem1554311 (k : real) (x : real) : (term54 k x) = (term189 k x).
Proof. exact (@lem1483525 (real_add k x) term53). Qed.
Lemma lem1554323 (k : real) (x : real) : (term190 k x) = (term191 k x).
Proof. exact (@lem1483519 (real_add k x) term53). Qed.
Lemma lem1554325 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1554326 : term186 = term53.
Proof. exact (@lem1554325 term44). Qed.
Lemma lem1554327 (k : real) (x : real) : (term192 k x) = (term192 k x).
Proof. exact (eq_refl (term192 k x)). Qed.
Lemma lem1554328 (k : real) (x : real) : (term191 k x) = (term193 k x).
Proof. exact (MK_COMB (@lem1554327 k x) (@lem1554326)). Qed.
Lemma lem1554329 (k : real) (x : real) : (term193 k x) = (real_add k x).
Proof. exact (@lem1483450 (real_add k x)). Qed.
Lemma lem1554330 (k : real) (x : real) : (term191 k x) = (real_add k x).
Proof. exact (TRANS (@lem1554328 k x) (@lem1554329 k x)). Qed.
Lemma lem1554332 (k : real) (x : real) : (term190 k x) = (real_add k x).
Proof. exact (TRANS (@lem1554323 k x) (@lem1554330 k x)). Qed.
Lemma lem1554333 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554334 (k : real) (x : real) : (term194 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1554333) (@lem1554332 k x)). Qed.
Lemma lem1554335 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554336 (k : real) (x : real) : (term189 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1554334 k x) (@lem1554335)). Qed.
Lemma lem1554337 (k : real) (x : real) : (term54 k x) = (term54 k x).
Proof. exact (TRANS (@lem1554311 k x) (@lem1554336 k x)). Qed.
Lemma lem1554338 (k : real) (x : real) : (term59 k x) = (term195 k x).
Proof. exact (@lem1483525 (term56 k x) term53). Qed.
Lemma lem1554356 (k : real) (x : real) : (term196 k x) = (term197 k x).
Proof. exact (@lem1483519 (term56 k x) term53). Qed.
Lemma lem1554358 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1554359 : term186 = term53.
Proof. exact (@lem1554358 term44). Qed.
Lemma lem1554360 (k : real) (x : real) : (term198 k x) = (term198 k x).
Proof. exact (eq_refl (term198 k x)). Qed.
Lemma lem1554361 (k : real) (x : real) : (term197 k x) = (term199 k x).
Proof. exact (MK_COMB (@lem1554360 k x) (@lem1554359)). Qed.
Lemma lem1554362 (k : real) (x : real) : (term199 k x) = (term56 k x).
Proof. exact (@lem1483450 (term56 k x)). Qed.
Lemma lem1554363 (k : real) (x : real) : (term197 k x) = (term56 k x).
Proof. exact (TRANS (@lem1554361 k x) (@lem1554362 k x)). Qed.
Lemma lem1554365 (k : real) (x : real) : (term196 k x) = (term56 k x).
Proof. exact (TRANS (@lem1554356 k x) (@lem1554363 k x)). Qed.
Lemma lem1554366 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554367 (k : real) (x : real) : (term200 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1554366) (@lem1554365 k x)). Qed.
Lemma lem1554368 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554369 (k : real) (x : real) : (term195 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1554367 k x) (@lem1554368)). Qed.
Lemma lem1554370 (k : real) (x : real) : (term59 k x) = (term59 k x).
Proof. exact (TRANS (@lem1554338 k x) (@lem1554369 k x)). Qed.
Lemma lem1554371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554372 (k : real) (x : real) : (term61 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1554371) (@lem1554337 k x)). Qed.
Lemma lem1554373 (k : real) (x : real) : (term62 k x) = (term62 k x).
Proof. exact (MK_COMB (@lem1554372 k x) (@lem1554370 k x)). Qed.
Lemma lem1554374 (k : real) (x : real) : (term90 k x) = (term201 k x).
Proof. exact (@lem1483527 (term87 k x) term53). Qed.
Lemma lem1554392 (k : real) (x : real) : (term202 k x) = (term203 k x).
Proof. exact (@lem1483519 (term87 k x) term53). Qed.
Lemma lem1554394 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1554395 : term186 = term53.
Proof. exact (@lem1554394 term44). Qed.
Lemma lem1554396 (k : real) (x : real) : (term204 k x) = (term204 k x).
Proof. exact (eq_refl (term204 k x)). Qed.
Lemma lem1554397 (k : real) (x : real) : (term203 k x) = (term205 k x).
Proof. exact (MK_COMB (@lem1554396 k x) (@lem1554395)). Qed.
Lemma lem1554398 (k : real) (x : real) : (term205 k x) = (term87 k x).
Proof. exact (@lem1483450 (term87 k x)). Qed.
Lemma lem1554399 (k : real) (x : real) : (term203 k x) = (term87 k x).
Proof. exact (TRANS (@lem1554397 k x) (@lem1554398 k x)). Qed.
Lemma lem1554401 (k : real) (x : real) : (term202 k x) = (term87 k x).
Proof. exact (TRANS (@lem1554392 k x) (@lem1554399 k x)). Qed.
Lemma lem1554402 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554403 (k : real) (x : real) : (term206 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1554402) (@lem1554401 k x)). Qed.
Lemma lem1554404 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554405 (k : real) (x : real) : (term201 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1554403 k x) (@lem1554404)). Qed.
Lemma lem1554406 (k : real) (x : real) : (term90 k x) = (term90 k x).
Proof. exact (TRANS (@lem1554374 k x) (@lem1554405 k x)). Qed.
Lemma lem1554407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554408 (k : real) (x : real) : (term72 k x) = (term72 k x).
Proof. exact (MK_COMB (@lem1554407) (@lem1554373 k x)). Qed.
Lemma lem1554409 (k : real) (x : real) : (term173 k x) = (term173 k x).
Proof. exact (MK_COMB (@lem1554408 k x) (@lem1554406 k x)). Qed.
Lemma lem1554410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554411 (x : real) : (term174 x) = (term174 x).
Proof. exact (MK_COMB (@lem1554410) (@lem1554310 x)). Qed.
Lemma lem1554412 (k : real) (x : real) : (term176 k x) = (term176 k x).
Proof. exact (MK_COMB (@lem1554411 x) (@lem1554409 k x)). Qed.
Lemma lem1554413 (x : real) : (term207 x) = (term208 x).
Proof. exact (@lem1483525 term53 x). Qed.
Lemma lem1554419 (x : real) : (term209 x) = (term210 x).
Proof. exact (@lem1483519 term53 x). Qed.
Lemma lem1554424 (x : real) : (term210 x) = (term33 x).
Proof. exact (@lem1483448 (term33 x)). Qed.
Lemma lem1554426 (x : real) : (term209 x) = (term33 x).
Proof. exact (TRANS (@lem1554419 x) (@lem1554424 x)). Qed.
Lemma lem1554427 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554428 (x : real) : (term211 x) = (term212 x).
Proof. exact (MK_COMB (@lem1554427) (@lem1554426 x)). Qed.
Lemma lem1554429 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554430 (x : real) : (term208 x) = (term213 x).
Proof. exact (MK_COMB (@lem1554428 x) (@lem1554429)). Qed.
Lemma lem1554431 (x : real) : (term207 x) = (term213 x).
Proof. exact (TRANS (@lem1554413 x) (@lem1554430 x)). Qed.
Lemma lem1554432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554433 (k : real) (x : real) : (term61 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1554432) (@lem1554337 k x)). Qed.
Lemma lem1554434 (k : real) (x : real) : (term62 k x) = (term62 k x).
Proof. exact (MK_COMB (@lem1554433 k x) (@lem1554370 k x)). Qed.
Lemma lem1554435 (k : real) (x : real) : (term214 k x) = (term215 k x).
Proof. exact (@lem1483527 (term216 k x) term53). Qed.
Lemma lem1554436 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554443 (x : real) : (real_neg x) = (term33 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1554452 (k : real) : (term217 k) = (term217 k).
Proof. exact (eq_refl (term217 k)). Qed.
Lemma lem1554455 (k : real) (x : real) : (term216 k x) = (term81 k x).
Proof. exact (MK_COMB (@lem1554452 k) (@lem1554443 x)). Qed.
Lemma lem1554456 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1554457 (k : real) (x : real) : (term218 k x) = (term219 k x).
Proof. exact (MK_COMB (@lem1554456) (@lem1554455 k x)). Qed.
Lemma lem1554458 (k : real) (x : real) : (term220 k x) = (term221 k x).
Proof. exact (MK_COMB (@lem1554457 k x) (@lem1554436)). Qed.
Lemma lem1554459 (k : real) (x : real) : (term221 k x) = (term222 k x).
Proof. exact (@lem1483519 (term81 k x) term53). Qed.
Lemma lem1554461 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1554462 : term186 = term53.
Proof. exact (@lem1554461 term44). Qed.
Lemma lem1554463 (k : real) (x : real) : (term223 k x) = (term223 k x).
Proof. exact (eq_refl (term223 k x)). Qed.
Lemma lem1554464 (k : real) (x : real) : (term222 k x) = (term224 k x).
Proof. exact (MK_COMB (@lem1554463 k x) (@lem1554462)). Qed.
Lemma lem1554465 (k : real) (x : real) : (term224 k x) = (term81 k x).
Proof. exact (@lem1483450 (term81 k x)). Qed.
Lemma lem1554466 (k : real) (x : real) : (term222 k x) = (term81 k x).
Proof. exact (TRANS (@lem1554464 k x) (@lem1554465 k x)). Qed.
Lemma lem1554467 (k : real) (x : real) : (term221 k x) = (term81 k x).
Proof. exact (TRANS (@lem1554459 k x) (@lem1554466 k x)). Qed.
Lemma lem1554468 (k : real) (x : real) : (term220 k x) = (term81 k x).
Proof. exact (TRANS (@lem1554458 k x) (@lem1554467 k x)). Qed.
Lemma lem1554469 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554470 (k : real) (x : real) : (term225 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1554469) (@lem1554468 k x)). Qed.
Lemma lem1554471 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554472 (k : real) (x : real) : (term215 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1554470 k x) (@lem1554471)). Qed.
Lemma lem1554473 (k : real) (x : real) : (term214 k x) = (term84 k x).
Proof. exact (TRANS (@lem1554435 k x) (@lem1554472 k x)). Qed.
Lemma lem1554474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554475 (k : real) (x : real) : (term72 k x) = (term72 k x).
Proof. exact (MK_COMB (@lem1554474) (@lem1554434 k x)). Qed.
Lemma lem1554476 (k : real) (x : real) : (term168 k x) = (term226 k x).
Proof. exact (MK_COMB (@lem1554475 k x) (@lem1554473 k x)). Qed.
Lemma lem1554477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1554478 (x : real) : (term169 x) = (term227 x).
Proof. exact (MK_COMB (@lem1554477) (@lem1554431 x)). Qed.
Lemma lem1554479 (k : real) (x : real) : (term171 k x) = (term228 k x).
Proof. exact (MK_COMB (@lem1554478 x) (@lem1554476 k x)). Qed.
Lemma lem1554480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554481 (k : real) (x : real) : (term178 k x) = (term178 k x).
Proof. exact (MK_COMB (@lem1554480) (@lem1554412 k x)). Qed.
Lemma lem1554482 (k : real) (x : real) : (term179 k x) = (term229 k x).
Proof. exact (MK_COMB (@lem1554481 k x) (@lem1554479 k x)). Qed.
Lemma lem1554494 (k : real) (x : real) : (term74 k x) = (term229 k x).
Proof. exact (TRANS (@lem1554289 k x) (@lem1554482 k x)). Qed.
Lemma lem1554496 (a : real) (x : real) (r : real) : (term230 a x r) = (term231 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1554497 (k : real) (x : real) : (term99 k x) = (term232 k x).
Proof. exact (@lem1554496 k x term53). Qed.
Lemma lem1554504 (x : real) : (term50 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1554507 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1554510 (k : real) (x : real) : (term233 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1554507 k) (@lem1554504 x)). Qed.
Lemma lem1554511 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554512 (k : real) (x : real) : (term234 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1554511) (@lem1554510 k x)). Qed.
Lemma lem1554513 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554514 (k : real) (x : real) : (term235 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1554512 k x) (@lem1554513)). Qed.
Lemma lem1554533 (k : real) (x : real) : (term236 k x) = (term236 k x).
Proof. exact (eq_refl (term236 k x)). Qed.
Lemma lem1554534 (k : real) (x : real) : (term232 k x) = (term237 k x).
Proof. exact (MK_COMB (@lem1554533 k x) (@lem1554514 k x)). Qed.
Lemma lem1554535 (k : real) (x : real) : (term99 k x) = (term237 k x).
Proof. exact (TRANS (@lem1554497 k x) (@lem1554534 k x)). Qed.
Lemma lem1554536 (k : real) (x : real) : (term238 k x) = (term238 k x).
Proof. exact (eq_refl (term238 k x)). Qed.
Lemma lem1554539 (k : real) (x : real) : (term239 k x) = (term240 k x).
Proof. exact (MK_COMB (@lem1554536 k x) (@lem1554535 k x)). Qed.
Lemma lem1554541 (a : real) (x : real) (r : real) : (term230 a x r) = (term231 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1554542 (k : real) (x : real) : (term99 k x) = (term232 k x).
Proof. exact (@lem1554541 k x term53). Qed.
Lemma lem1554549 (x : real) : (term50 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1554552 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1554555 (k : real) (x : real) : (term233 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1554552 k) (@lem1554549 x)). Qed.
Lemma lem1554556 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554557 (k : real) (x : real) : (term234 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1554556) (@lem1554555 k x)). Qed.
Lemma lem1554558 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554559 (k : real) (x : real) : (term235 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1554557 k x) (@lem1554558)). Qed.
Lemma lem1554578 (k : real) (x : real) : (term236 k x) = (term236 k x).
Proof. exact (eq_refl (term236 k x)). Qed.
Lemma lem1554579 (k : real) (x : real) : (term232 k x) = (term237 k x).
Proof. exact (MK_COMB (@lem1554578 k x) (@lem1554559 k x)). Qed.
Lemma lem1554580 (k : real) (x : real) : (term99 k x) = (term237 k x).
Proof. exact (TRANS (@lem1554542 k x) (@lem1554579 k x)). Qed.
Lemma lem1554581 (k : real) (x : real) : (term241 k x) = (term241 k x).
Proof. exact (eq_refl (term241 k x)). Qed.
Lemma lem1554584 (k : real) (x : real) : (term242 k x) = (term243 k x).
Proof. exact (MK_COMB (@lem1554581 k x) (@lem1554580 k x)). Qed.
Lemma lem1554585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554586 (k : real) (x : real) : (term244 k x) = (term245 k x).
Proof. exact (MK_COMB (@lem1554585) (@lem1554539 k x)). Qed.
Lemma lem1554587 (k : real) (x : real) : (term158 k x) = (term246 k x).
Proof. exact (MK_COMB (@lem1554586 k x) (@lem1554584 k x)). Qed.
Lemma lem1554588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1554589 (k : real) (x : real) : (term102 k x) = (term247 k x).
Proof. exact (MK_COMB (@lem1554588) (@lem1554494 k x)). Qed.
Lemma lem1554590 (k : real) (x : real) : (term159 k x) = (term248 k x).
Proof. exact (MK_COMB (@lem1554589 k x) (@lem1554587 k x)). Qed.
Lemma lem1554591 (k : real) (x : real) (h1 : term248 k x) : term248 k x.
Proof. exact (h1). Qed.
Lemma lem1554592 (k : real) (x : real) (h1 : term229 k x) : term229 k x.
Proof. exact (h1). Qed.
Lemma lem1554593 (k : real) (x : real) (h1 : term176 k x) : term176 k x.
Proof. exact (h1). Qed.
Lemma lem1554594 (k : real) (x : real) (h1 : term176 k x) : term173 k x.
Proof. exact (proj2 (@lem1554593 k x h1)). Qed.
Lemma lem1554596 (k : real) (x : real) (h1 : term176 k x) : term90 k x.
Proof. exact (proj2 (@lem1554594 k x h1)). Qed.
Lemma lem1554597 (k : real) (x : real) (h1 : term176 k x) : term62 k x.
Proof. exact (proj1 (@lem1554594 k x h1)). Qed.
Lemma lem1554598 (k : real) (x : real) (h1 : term176 k x) : term59 k x.
Proof. exact (proj2 (@lem1554597 k x h1)). Qed.
Lemma lem1554601 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554602 : term250 = term251.
Proof. exact (@lem1554601 (NUMERAL 0) term44). Qed.
Lemma lem1554603 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554604 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554605 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554604 h1) (fun h1 : term251 = True => @lem1554603)). Qed.
Lemma lem1554606 : term251 = True.
Proof. exact (EQ_MP (@lem1554605) (@lem1554603)). Qed.
Lemma lem1554607 : term250 = True.
Proof. exact (TRANS (@lem1554602) (@lem1554606)). Qed.
Lemma lem1554608 : True = term250.
Proof. exact (SYM (@lem1554607)). Qed.
Lemma lem1554609 : term250.
Proof. exact (EQ_MP (@lem1554608) (@lem0)). Qed.
Lemma lem1554610 (k : real) (x : real) (h1 : term176 k x) : term253 k x.
Proof. exact (conj (@lem1554609) (@lem1554596 k x h1)). Qed.
Lemma lem1554612 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1554613 (k : real) (x : real) : term255 k x.
Proof. exact (@lem1554612 term47 (term87 k x)). Qed.
Lemma lem1554614 (k : real) (x : real) (h1 : term176 k x) : term256 k x.
Proof. exact (@lem1554613 k x (@lem1554610 k x h1)). Qed.
Lemma lem1554615 (k : real) (x : real) : (term257 k x) = (term87 k x).
Proof. exact (@lem1483460 (term87 k x)). Qed.
Lemma lem1554616 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554617 (k : real) (x : real) : (term258 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1554616) (@lem1554615 k x)). Qed.
Lemma lem1554618 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554619 (k : real) (x : real) : (term256 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1554617 k x) (@lem1554618)). Qed.
Lemma lem1554620 (k : real) (x : real) (h1 : term176 k x) : term90 k x.
Proof. exact (EQ_MP (@lem1554619 k x) (@lem1554614 k x h1)). Qed.
Lemma lem1554622 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554623 : term250 = term251.
Proof. exact (@lem1554622 (NUMERAL 0) term44). Qed.
Lemma lem1554624 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554625 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554626 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554625 h1) (fun h1 : term251 = True => @lem1554624)). Qed.
Lemma lem1554627 : term251 = True.
Proof. exact (EQ_MP (@lem1554626) (@lem1554624)). Qed.
Lemma lem1554628 : term250 = True.
Proof. exact (TRANS (@lem1554623) (@lem1554627)). Qed.
Lemma lem1554629 : True = term250.
Proof. exact (SYM (@lem1554628)). Qed.
Lemma lem1554630 : term250.
Proof. exact (EQ_MP (@lem1554629) (@lem0)). Qed.
Lemma lem1554631 (k : real) (x : real) (h1 : term176 k x) : term259 k x.
Proof. exact (conj (@lem1554630) (@lem1554598 k x h1)). Qed.
Lemma lem1554633 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1554634 (k : real) (x : real) : term261 k x.
Proof. exact (@lem1554633 term47 (term56 k x)). Qed.
Lemma lem1554635 (k : real) (x : real) (h1 : term176 k x) : term262 k x.
Proof. exact (@lem1554634 k x (@lem1554631 k x h1)). Qed.
Lemma lem1554636 (k : real) (x : real) : (term263 k x) = (term56 k x).
Proof. exact (@lem1483460 (term56 k x)). Qed.
Lemma lem1554637 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554638 (k : real) (x : real) : (term264 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1554637) (@lem1554636 k x)). Qed.
Lemma lem1554639 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554640 (k : real) (x : real) : (term262 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1554638 k x) (@lem1554639)). Qed.
Lemma lem1554641 (k : real) (x : real) (h1 : term176 k x) : term59 k x.
Proof. exact (EQ_MP (@lem1554640 k x) (@lem1554635 k x h1)). Qed.
Lemma lem1554642 (k : real) (x : real) (h1 : term176 k x) : term265 k x.
Proof. exact (conj (@lem1554641 k x h1) (@lem1554620 k x h1)). Qed.
Lemma lem1554644 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1554645 (k : real) (x : real) : term267 k x.
Proof. exact (@lem1554644 (term56 k x) (term87 k x)). Qed.
Lemma lem1554646 (k : real) (x : real) (h1 : term176 k x) : term268 k x.
Proof. exact (@lem1554645 k x (@lem1554642 k x h1)). Qed.
Lemma lem1554647 (k : real) (x : real) : (term269 k x) = (term270 k x).
Proof. exact (@lem1483480 k (term33 k) (term33 x) x). Qed.
Lemma lem1554648 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483442 term39 k). Qed.
Lemma lem1554650 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554651 : term274 = term53.
Proof. exact (@lem1554650 term44). Qed.
Lemma lem1554652 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554653 : term275 = term276.
Proof. exact (MK_COMB (@lem1554652) (@lem1554651)). Qed.
Lemma lem1554654 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1554655 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1554653) (@lem1554654 k)). Qed.
Lemma lem1554656 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1554648 k) (@lem1554655 k)). Qed.
Lemma lem1554657 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1554658 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1554656 k) (@lem1554657 k)). Qed.
Lemma lem1554659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1554660 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1554659) (@lem1554658 k)). Qed.
Lemma lem1554661 (x : real) : (term280 x) = (term272 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1554663 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554664 : term274 = term53.
Proof. exact (@lem1554663 term44). Qed.
Lemma lem1554665 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554666 : term275 = term276.
Proof. exact (MK_COMB (@lem1554665) (@lem1554664)). Qed.
Lemma lem1554667 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1554668 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1554666) (@lem1554667 x)). Qed.
Lemma lem1554669 (x : real) : (term280 x) = (term277 x).
Proof. exact (TRANS (@lem1554661 x) (@lem1554668 x)). Qed.
Lemma lem1554670 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1554671 (x : real) : (term280 x) = term53.
Proof. exact (TRANS (@lem1554669 x) (@lem1554670 x)). Qed.
Lemma lem1554672 (k : real) (x : real) : (term270 k x) = term281.
Proof. exact (MK_COMB (@lem1554660 k) (@lem1554671 x)). Qed.
Lemma lem1554673 (k : real) (x : real) : (term269 k x) = term281.
Proof. exact (TRANS (@lem1554647 k x) (@lem1554672 k x)). Qed.
Lemma lem1554674 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1554675 (k : real) (x : real) : (term269 k x) = term53.
Proof. exact (TRANS (@lem1554673 k x) (@lem1554674)). Qed.
Lemma lem1554676 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554677 (k : real) (x : real) : (term282 k x) = term283.
Proof. exact (MK_COMB (@lem1554676) (@lem1554675 k x)). Qed.
Lemma lem1554678 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554679 (k : real) (x : real) : (term268 k x) = term284.
Proof. exact (MK_COMB (@lem1554677 k x) (@lem1554678)). Qed.
Lemma lem1554680 (k : real) (x : real) (h1 : term176 k x) : term284.
Proof. exact (EQ_MP (@lem1554679 k x) (@lem1554646 k x h1)). Qed.
Lemma lem1554682 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554683 : term284 = term285.
Proof. exact (@lem1554682 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1554684 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1554685 : term284 = False.
Proof. exact (TRANS (@lem1554683) (@lem1554684)). Qed.
Lemma lem1554686 (k : real) (x : real) (h1 : term176 k x) : False.
Proof. exact (EQ_MP (@lem1554685) (@lem1554680 k x h1)). Qed.
Lemma lem1554687 (k : real) (x : real) (h1 : term228 k x) : term228 k x.
Proof. exact (h1). Qed.
Lemma lem1554688 (k : real) (x : real) (h1 : term228 k x) : term226 k x.
Proof. exact (proj2 (@lem1554687 k x h1)). Qed.
Lemma lem1554690 (k : real) (x : real) (h1 : term228 k x) : term84 k x.
Proof. exact (proj2 (@lem1554688 k x h1)). Qed.
Lemma lem1554691 (k : real) (x : real) (h1 : term228 k x) : term62 k x.
Proof. exact (proj1 (@lem1554688 k x h1)). Qed.
Lemma lem1554693 (k : real) (x : real) (h1 : term228 k x) : term54 k x.
Proof. exact (proj1 (@lem1554691 k x h1)). Qed.
Lemma lem1554695 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554696 : term250 = term251.
Proof. exact (@lem1554695 (NUMERAL 0) term44). Qed.
Lemma lem1554697 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554698 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554699 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554698 h1) (fun h1 : term251 = True => @lem1554697)). Qed.
Lemma lem1554700 : term251 = True.
Proof. exact (EQ_MP (@lem1554699) (@lem1554697)). Qed.
Lemma lem1554701 : term250 = True.
Proof. exact (TRANS (@lem1554696) (@lem1554700)). Qed.
Lemma lem1554702 : True = term250.
Proof. exact (SYM (@lem1554701)). Qed.
Lemma lem1554703 : term250.
Proof. exact (EQ_MP (@lem1554702) (@lem0)). Qed.
Lemma lem1554704 (k : real) (x : real) (h1 : term228 k x) : term286 k x.
Proof. exact (conj (@lem1554703) (@lem1554690 k x h1)). Qed.
Lemma lem1554706 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1554707 (k : real) (x : real) : term287 k x.
Proof. exact (@lem1554706 term47 (term81 k x)). Qed.
Lemma lem1554708 (k : real) (x : real) (h1 : term228 k x) : term288 k x.
Proof. exact (@lem1554707 k x (@lem1554704 k x h1)). Qed.
Lemma lem1554709 (k : real) (x : real) : (term289 k x) = (term81 k x).
Proof. exact (@lem1483460 (term81 k x)). Qed.
Lemma lem1554710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554711 (k : real) (x : real) : (term290 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1554710) (@lem1554709 k x)). Qed.
Lemma lem1554712 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554713 (k : real) (x : real) : (term288 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1554711 k x) (@lem1554712)). Qed.
Lemma lem1554714 (k : real) (x : real) (h1 : term228 k x) : term84 k x.
Proof. exact (EQ_MP (@lem1554713 k x) (@lem1554708 k x h1)). Qed.
Lemma lem1554716 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554717 : term250 = term251.
Proof. exact (@lem1554716 (NUMERAL 0) term44). Qed.
Lemma lem1554718 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554719 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554720 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554719 h1) (fun h1 : term251 = True => @lem1554718)). Qed.
Lemma lem1554721 : term251 = True.
Proof. exact (EQ_MP (@lem1554720) (@lem1554718)). Qed.
Lemma lem1554722 : term250 = True.
Proof. exact (TRANS (@lem1554717) (@lem1554721)). Qed.
Lemma lem1554723 : True = term250.
Proof. exact (SYM (@lem1554722)). Qed.
Lemma lem1554724 : term250.
Proof. exact (EQ_MP (@lem1554723) (@lem0)). Qed.
Lemma lem1554725 (k : real) (x : real) (h1 : term228 k x) : term291 k x.
Proof. exact (conj (@lem1554724) (@lem1554693 k x h1)). Qed.
Lemma lem1554727 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1554728 (k : real) (x : real) : term292 k x.
Proof. exact (@lem1554727 term47 (real_add k x)). Qed.
Lemma lem1554729 (k : real) (x : real) (h1 : term228 k x) : term293 k x.
Proof. exact (@lem1554728 k x (@lem1554725 k x h1)). Qed.
Lemma lem1554730 (k : real) (x : real) : (term294 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1554731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554732 (k : real) (x : real) : (term295 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1554731) (@lem1554730 k x)). Qed.
Lemma lem1554733 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554734 (k : real) (x : real) : (term293 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1554732 k x) (@lem1554733)). Qed.
Lemma lem1554735 (k : real) (x : real) (h1 : term228 k x) : term54 k x.
Proof. exact (EQ_MP (@lem1554734 k x) (@lem1554729 k x h1)). Qed.
Lemma lem1554736 (k : real) (x : real) (h1 : term228 k x) : term296 k x.
Proof. exact (conj (@lem1554735 k x h1) (@lem1554714 k x h1)). Qed.
Lemma lem1554738 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1554739 (k : real) (x : real) : term297 k x.
Proof. exact (@lem1554738 (real_add k x) (term81 k x)). Qed.
Lemma lem1554740 (k : real) (x : real) (h1 : term228 k x) : term298 k x.
Proof. exact (@lem1554739 k x (@lem1554736 k x h1)). Qed.
Lemma lem1554741 (k : real) (x : real) : (term299 k x) = (term300 k x).
Proof. exact (@lem1483480 k (term33 k) x (term33 x)). Qed.
Lemma lem1554742 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483442 term39 k). Qed.
Lemma lem1554744 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554745 : term274 = term53.
Proof. exact (@lem1554744 term44). Qed.
Lemma lem1554746 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554747 : term275 = term276.
Proof. exact (MK_COMB (@lem1554746) (@lem1554745)). Qed.
Lemma lem1554748 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1554749 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1554747) (@lem1554748 k)). Qed.
Lemma lem1554750 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1554742 k) (@lem1554749 k)). Qed.
Lemma lem1554751 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1554752 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1554750 k) (@lem1554751 k)). Qed.
Lemma lem1554753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1554754 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1554753) (@lem1554752 k)). Qed.
Lemma lem1554755 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1554757 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554758 : term274 = term53.
Proof. exact (@lem1554757 term44). Qed.
Lemma lem1554759 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554760 : term275 = term276.
Proof. exact (MK_COMB (@lem1554759) (@lem1554758)). Qed.
Lemma lem1554761 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1554762 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1554760) (@lem1554761 x)). Qed.
Lemma lem1554763 (x : real) : (term271 x) = (term277 x).
Proof. exact (TRANS (@lem1554755 x) (@lem1554762 x)). Qed.
Lemma lem1554764 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1554765 (x : real) : (term271 x) = term53.
Proof. exact (TRANS (@lem1554763 x) (@lem1554764 x)). Qed.
Lemma lem1554766 (k : real) (x : real) : (term300 k x) = term281.
Proof. exact (MK_COMB (@lem1554754 k) (@lem1554765 x)). Qed.
Lemma lem1554767 (k : real) (x : real) : (term299 k x) = term281.
Proof. exact (TRANS (@lem1554741 k x) (@lem1554766 k x)). Qed.
Lemma lem1554768 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1554769 (k : real) (x : real) : (term299 k x) = term53.
Proof. exact (TRANS (@lem1554767 k x) (@lem1554768)). Qed.
Lemma lem1554770 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554771 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (MK_COMB (@lem1554770) (@lem1554769 k x)). Qed.
Lemma lem1554772 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554773 (k : real) (x : real) : (term298 k x) = term284.
Proof. exact (MK_COMB (@lem1554771 k x) (@lem1554772)). Qed.
Lemma lem1554774 (k : real) (x : real) (h1 : term228 k x) : term284.
Proof. exact (EQ_MP (@lem1554773 k x) (@lem1554740 k x h1)). Qed.
Lemma lem1554776 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554777 : term284 = term285.
Proof. exact (@lem1554776 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1554778 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1554779 : term284 = False.
Proof. exact (TRANS (@lem1554777) (@lem1554778)). Qed.
Lemma lem1554780 (k : real) (x : real) (h1 : term228 k x) : False.
Proof. exact (EQ_MP (@lem1554779) (@lem1554774 k x h1)). Qed.
Lemma lem1554781 (k : real) (x : real) (h1 : term229 k x) : False.
Proof. exact (or_elim (@lem1554592 k x h1) (fun h0 : term176 k x => @lem1554686 k x h0) (fun h0 : term228 k x => @lem1554780 k x h0)). Qed.
Lemma lem1554782 (k : real) (x : real) (h1 : term246 k x) : term246 k x.
Proof. exact (h1). Qed.
Lemma lem1554783 (k : real) (x : real) (h1 : term240 k x) : term240 k x.
Proof. exact (h1). Qed.
Lemma lem1554784 (k : real) (x : real) (h1 : term240 k x) : term237 k x.
Proof. exact (proj2 (@lem1554783 k x h1)). Qed.
Lemma lem1554785 (k : real) (x : real) (h1 : term240 k x) : term84 k x.
Proof. exact (proj1 (@lem1554783 k x h1)). Qed.
Lemma lem1554786 (k : real) (x : real) (h1 : term240 k x) : term54 k x.
Proof. exact (proj2 (@lem1554784 k x h1)). Qed.
Lemma lem1554789 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554790 : term250 = term251.
Proof. exact (@lem1554789 (NUMERAL 0) term44). Qed.
Lemma lem1554791 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554792 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554793 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554792 h1) (fun h1 : term251 = True => @lem1554791)). Qed.
Lemma lem1554794 : term251 = True.
Proof. exact (EQ_MP (@lem1554793) (@lem1554791)). Qed.
Lemma lem1554795 : term250 = True.
Proof. exact (TRANS (@lem1554790) (@lem1554794)). Qed.
Lemma lem1554796 : True = term250.
Proof. exact (SYM (@lem1554795)). Qed.
Lemma lem1554797 : term250.
Proof. exact (EQ_MP (@lem1554796) (@lem0)). Qed.
Lemma lem1554798 (k : real) (x : real) (h1 : term240 k x) : term286 k x.
Proof. exact (conj (@lem1554797) (@lem1554785 k x h1)). Qed.
Lemma lem1554800 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1554801 (k : real) (x : real) : term287 k x.
Proof. exact (@lem1554800 term47 (term81 k x)). Qed.
Lemma lem1554802 (k : real) (x : real) (h1 : term240 k x) : term288 k x.
Proof. exact (@lem1554801 k x (@lem1554798 k x h1)). Qed.
Lemma lem1554803 (k : real) (x : real) : (term289 k x) = (term81 k x).
Proof. exact (@lem1483460 (term81 k x)). Qed.
Lemma lem1554804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554805 (k : real) (x : real) : (term290 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1554804) (@lem1554803 k x)). Qed.
Lemma lem1554806 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554807 (k : real) (x : real) : (term288 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1554805 k x) (@lem1554806)). Qed.
Lemma lem1554808 (k : real) (x : real) (h1 : term240 k x) : term84 k x.
Proof. exact (EQ_MP (@lem1554807 k x) (@lem1554802 k x h1)). Qed.
Lemma lem1554810 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554811 : term250 = term251.
Proof. exact (@lem1554810 (NUMERAL 0) term44). Qed.
Lemma lem1554812 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554813 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554814 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554813 h1) (fun h1 : term251 = True => @lem1554812)). Qed.
Lemma lem1554815 : term251 = True.
Proof. exact (EQ_MP (@lem1554814) (@lem1554812)). Qed.
Lemma lem1554816 : term250 = True.
Proof. exact (TRANS (@lem1554811) (@lem1554815)). Qed.
Lemma lem1554817 : True = term250.
Proof. exact (SYM (@lem1554816)). Qed.
Lemma lem1554818 : term250.
Proof. exact (EQ_MP (@lem1554817) (@lem0)). Qed.
Lemma lem1554819 (k : real) (x : real) (h1 : term240 k x) : term291 k x.
Proof. exact (conj (@lem1554818) (@lem1554786 k x h1)). Qed.
Lemma lem1554821 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1554822 (k : real) (x : real) : term292 k x.
Proof. exact (@lem1554821 term47 (real_add k x)). Qed.
Lemma lem1554823 (k : real) (x : real) (h1 : term240 k x) : term293 k x.
Proof. exact (@lem1554822 k x (@lem1554819 k x h1)). Qed.
Lemma lem1554824 (k : real) (x : real) : (term294 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1554825 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554826 (k : real) (x : real) : (term295 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1554825) (@lem1554824 k x)). Qed.
Lemma lem1554827 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554828 (k : real) (x : real) : (term293 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1554826 k x) (@lem1554827)). Qed.
Lemma lem1554829 (k : real) (x : real) (h1 : term240 k x) : term54 k x.
Proof. exact (EQ_MP (@lem1554828 k x) (@lem1554823 k x h1)). Qed.
Lemma lem1554830 (k : real) (x : real) (h1 : term240 k x) : term296 k x.
Proof. exact (conj (@lem1554829 k x h1) (@lem1554808 k x h1)). Qed.
Lemma lem1554832 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1554833 (k : real) (x : real) : term297 k x.
Proof. exact (@lem1554832 (real_add k x) (term81 k x)). Qed.
Lemma lem1554834 (k : real) (x : real) (h1 : term240 k x) : term298 k x.
Proof. exact (@lem1554833 k x (@lem1554830 k x h1)). Qed.
Lemma lem1554835 (k : real) (x : real) : (term299 k x) = (term300 k x).
Proof. exact (@lem1483480 k (term33 k) x (term33 x)). Qed.
Lemma lem1554836 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483442 term39 k). Qed.
Lemma lem1554838 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554839 : term274 = term53.
Proof. exact (@lem1554838 term44). Qed.
Lemma lem1554840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554841 : term275 = term276.
Proof. exact (MK_COMB (@lem1554840) (@lem1554839)). Qed.
Lemma lem1554842 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1554843 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1554841) (@lem1554842 k)). Qed.
Lemma lem1554844 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1554836 k) (@lem1554843 k)). Qed.
Lemma lem1554845 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1554846 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1554844 k) (@lem1554845 k)). Qed.
Lemma lem1554847 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1554848 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1554847) (@lem1554846 k)). Qed.
Lemma lem1554849 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1554851 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554852 : term274 = term53.
Proof. exact (@lem1554851 term44). Qed.
Lemma lem1554853 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554854 : term275 = term276.
Proof. exact (MK_COMB (@lem1554853) (@lem1554852)). Qed.
Lemma lem1554855 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1554856 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1554854) (@lem1554855 x)). Qed.
Lemma lem1554857 (x : real) : (term271 x) = (term277 x).
Proof. exact (TRANS (@lem1554849 x) (@lem1554856 x)). Qed.
Lemma lem1554858 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1554859 (x : real) : (term271 x) = term53.
Proof. exact (TRANS (@lem1554857 x) (@lem1554858 x)). Qed.
Lemma lem1554860 (k : real) (x : real) : (term300 k x) = term281.
Proof. exact (MK_COMB (@lem1554848 k) (@lem1554859 x)). Qed.
Lemma lem1554861 (k : real) (x : real) : (term299 k x) = term281.
Proof. exact (TRANS (@lem1554835 k x) (@lem1554860 k x)). Qed.
Lemma lem1554862 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1554863 (k : real) (x : real) : (term299 k x) = term53.
Proof. exact (TRANS (@lem1554861 k x) (@lem1554862)). Qed.
Lemma lem1554864 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554865 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (MK_COMB (@lem1554864) (@lem1554863 k x)). Qed.
Lemma lem1554866 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554867 (k : real) (x : real) : (term298 k x) = term284.
Proof. exact (MK_COMB (@lem1554865 k x) (@lem1554866)). Qed.
Lemma lem1554868 (k : real) (x : real) (h1 : term240 k x) : term284.
Proof. exact (EQ_MP (@lem1554867 k x) (@lem1554834 k x h1)). Qed.
Lemma lem1554870 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554871 : term284 = term285.
Proof. exact (@lem1554870 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1554872 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1554873 : term284 = False.
Proof. exact (TRANS (@lem1554871) (@lem1554872)). Qed.
Lemma lem1554874 (k : real) (x : real) (h1 : term240 k x) : False.
Proof. exact (EQ_MP (@lem1554873) (@lem1554868 k x h1)). Qed.
Lemma lem1554875 (k : real) (x : real) (h1 : term243 k x) : term243 k x.
Proof. exact (h1). Qed.
Lemma lem1554876 (k : real) (x : real) (h1 : term243 k x) : term237 k x.
Proof. exact (proj2 (@lem1554875 k x h1)). Qed.
Lemma lem1554877 (k : real) (x : real) (h1 : term243 k x) : term90 k x.
Proof. exact (proj1 (@lem1554875 k x h1)). Qed.
Lemma lem1554879 (k : real) (x : real) (h1 : term243 k x) : term59 k x.
Proof. exact (proj1 (@lem1554876 k x h1)). Qed.
Lemma lem1554881 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554882 : term250 = term251.
Proof. exact (@lem1554881 (NUMERAL 0) term44). Qed.
Lemma lem1554883 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554884 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554885 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554884 h1) (fun h1 : term251 = True => @lem1554883)). Qed.
Lemma lem1554886 : term251 = True.
Proof. exact (EQ_MP (@lem1554885) (@lem1554883)). Qed.
Lemma lem1554887 : term250 = True.
Proof. exact (TRANS (@lem1554882) (@lem1554886)). Qed.
Lemma lem1554888 : True = term250.
Proof. exact (SYM (@lem1554887)). Qed.
Lemma lem1554889 : term250.
Proof. exact (EQ_MP (@lem1554888) (@lem0)). Qed.
Lemma lem1554890 (k : real) (x : real) (h1 : term243 k x) : term253 k x.
Proof. exact (conj (@lem1554889) (@lem1554877 k x h1)). Qed.
Lemma lem1554892 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1554893 (k : real) (x : real) : term255 k x.
Proof. exact (@lem1554892 term47 (term87 k x)). Qed.
Lemma lem1554894 (k : real) (x : real) (h1 : term243 k x) : term256 k x.
Proof. exact (@lem1554893 k x (@lem1554890 k x h1)). Qed.
Lemma lem1554895 (k : real) (x : real) : (term257 k x) = (term87 k x).
Proof. exact (@lem1483460 (term87 k x)). Qed.
Lemma lem1554896 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1554897 (k : real) (x : real) : (term258 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1554896) (@lem1554895 k x)). Qed.
Lemma lem1554898 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554899 (k : real) (x : real) : (term256 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1554897 k x) (@lem1554898)). Qed.
Lemma lem1554900 (k : real) (x : real) (h1 : term243 k x) : term90 k x.
Proof. exact (EQ_MP (@lem1554899 k x) (@lem1554894 k x h1)). Qed.
Lemma lem1554902 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554903 : term250 = term251.
Proof. exact (@lem1554902 (NUMERAL 0) term44). Qed.
Lemma lem1554904 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1554905 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1554906 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1554905 h1) (fun h1 : term251 = True => @lem1554904)). Qed.
Lemma lem1554907 : term251 = True.
Proof. exact (EQ_MP (@lem1554906) (@lem1554904)). Qed.
Lemma lem1554908 : term250 = True.
Proof. exact (TRANS (@lem1554903) (@lem1554907)). Qed.
Lemma lem1554909 : True = term250.
Proof. exact (SYM (@lem1554908)). Qed.
Lemma lem1554910 : term250.
Proof. exact (EQ_MP (@lem1554909) (@lem0)). Qed.
Lemma lem1554911 (k : real) (x : real) (h1 : term243 k x) : term259 k x.
Proof. exact (conj (@lem1554910) (@lem1554879 k x h1)). Qed.
Lemma lem1554913 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1554914 (k : real) (x : real) : term261 k x.
Proof. exact (@lem1554913 term47 (term56 k x)). Qed.
Lemma lem1554915 (k : real) (x : real) (h1 : term243 k x) : term262 k x.
Proof. exact (@lem1554914 k x (@lem1554911 k x h1)). Qed.
Lemma lem1554916 (k : real) (x : real) : (term263 k x) = (term56 k x).
Proof. exact (@lem1483460 (term56 k x)). Qed.
Lemma lem1554917 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554918 (k : real) (x : real) : (term264 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1554917) (@lem1554916 k x)). Qed.
Lemma lem1554919 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554920 (k : real) (x : real) : (term262 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1554918 k x) (@lem1554919)). Qed.
Lemma lem1554921 (k : real) (x : real) (h1 : term243 k x) : term59 k x.
Proof. exact (EQ_MP (@lem1554920 k x) (@lem1554915 k x h1)). Qed.
Lemma lem1554922 (k : real) (x : real) (h1 : term243 k x) : term265 k x.
Proof. exact (conj (@lem1554921 k x h1) (@lem1554900 k x h1)). Qed.
Lemma lem1554924 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1554925 (k : real) (x : real) : term267 k x.
Proof. exact (@lem1554924 (term56 k x) (term87 k x)). Qed.
Lemma lem1554926 (k : real) (x : real) (h1 : term243 k x) : term268 k x.
Proof. exact (@lem1554925 k x (@lem1554922 k x h1)). Qed.
Lemma lem1554927 (k : real) (x : real) : (term269 k x) = (term270 k x).
Proof. exact (@lem1483480 k (term33 k) (term33 x) x). Qed.
Lemma lem1554928 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483442 term39 k). Qed.
Lemma lem1554930 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554931 : term274 = term53.
Proof. exact (@lem1554930 term44). Qed.
Lemma lem1554932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554933 : term275 = term276.
Proof. exact (MK_COMB (@lem1554932) (@lem1554931)). Qed.
Lemma lem1554934 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1554935 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1554933) (@lem1554934 k)). Qed.
Lemma lem1554936 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1554928 k) (@lem1554935 k)). Qed.
Lemma lem1554937 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1554938 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1554936 k) (@lem1554937 k)). Qed.
Lemma lem1554939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1554940 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1554939) (@lem1554938 k)). Qed.
Lemma lem1554941 (x : real) : (term280 x) = (term272 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1554943 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1554944 : term274 = term53.
Proof. exact (@lem1554943 term44). Qed.
Lemma lem1554945 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1554946 : term275 = term276.
Proof. exact (MK_COMB (@lem1554945) (@lem1554944)). Qed.
Lemma lem1554947 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1554948 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1554946) (@lem1554947 x)). Qed.
Lemma lem1554949 (x : real) : (term280 x) = (term277 x).
Proof. exact (TRANS (@lem1554941 x) (@lem1554948 x)). Qed.
Lemma lem1554950 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1554951 (x : real) : (term280 x) = term53.
Proof. exact (TRANS (@lem1554949 x) (@lem1554950 x)). Qed.
Lemma lem1554952 (k : real) (x : real) : (term270 k x) = term281.
Proof. exact (MK_COMB (@lem1554940 k) (@lem1554951 x)). Qed.
Lemma lem1554953 (k : real) (x : real) : (term269 k x) = term281.
Proof. exact (TRANS (@lem1554927 k x) (@lem1554952 k x)). Qed.
Lemma lem1554954 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1554955 (k : real) (x : real) : (term269 k x) = term53.
Proof. exact (TRANS (@lem1554953 k x) (@lem1554954)). Qed.
Lemma lem1554956 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1554957 (k : real) (x : real) : (term282 k x) = term283.
Proof. exact (MK_COMB (@lem1554956) (@lem1554955 k x)). Qed.
Lemma lem1554958 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1554959 (k : real) (x : real) : (term268 k x) = term284.
Proof. exact (MK_COMB (@lem1554957 k x) (@lem1554958)). Qed.
Lemma lem1554960 (k : real) (x : real) (h1 : term243 k x) : term284.
Proof. exact (EQ_MP (@lem1554959 k x) (@lem1554926 k x h1)). Qed.
Lemma lem1554962 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1554963 : term284 = term285.
Proof. exact (@lem1554962 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1554964 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1554965 : term284 = False.
Proof. exact (TRANS (@lem1554963) (@lem1554964)). Qed.
Lemma lem1554966 (k : real) (x : real) (h1 : term243 k x) : False.
Proof. exact (EQ_MP (@lem1554965) (@lem1554960 k x h1)). Qed.
Lemma lem1554967 (k : real) (x : real) (h1 : term246 k x) : False.
Proof. exact (or_elim (@lem1554782 k x h1) (fun h0 : term240 k x => @lem1554874 k x h0) (fun h0 : term243 k x => @lem1554966 k x h0)). Qed.
Lemma lem1554968 (k : real) (x : real) (h1 : term248 k x) : False.
Proof. exact (or_elim (@lem1554591 k x h1) (fun h0 : term229 k x => @lem1554781 k x h0) (fun h0 : term246 k x => @lem1554967 k x h0)). Qed.
Lemma lem1554969 (k : real) (x : real) (h1 : term159 k x) : term159 k x.
Proof. exact (h1). Qed.
Lemma lem1554970 (k : real) (x : real) (h1 : term159 k x) : term248 k x.
Proof. exact (EQ_MP (@lem1554590 k x) (@lem1554969 k x h1)). Qed.
Lemma lem1554971 (k : real) (x : real) (h1 : term159 k x) : (term248 k x) = False.
Proof. exact (prop_ext (fun h2 : term248 k x => @lem1554968 k x h2) (fun h2 : False => @lem1554970 k x h1)). Qed.
Lemma lem1554972 (k : real) (x : real) (h1 : term159 k x) : False.
Proof. exact (EQ_MP (@lem1554971 k x h1) (@lem1554970 k x h1)). Qed.
Lemma lem1554973 (x : real) (h1 : term161 x) : term161 x.
Proof. exact (h1). Qed.
Lemma lem1554974 (x : real) (h1 : term161 x) : False.
Proof. exact (ex_elim (@lem1554973 x h1) (fun k : real => fun h0 : term160 x k => @lem1554972 k x h0)). Qed.
Lemma lem1554975 (h1 : term163) : term163.
Proof. exact (h1). Qed.
Lemma lem1554976 (h1 : term163) : False.
Proof. exact (ex_elim (@lem1554975 h1) (fun x : real => fun h0 : term162 x => @lem1554974 x h0)). Qed.
Lemma lem1554977 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1554978 (h1 : term23) : term163.
Proof. exact (EQ_MP (@lem1554272) (@lem1554977 h1)). Qed.
Lemma lem1554979 (h1 : term23) : term163 = False.
Proof. exact (prop_ext (fun h2 : term163 => @lem1554976 h2) (fun h2 : False => @lem1554978 h1)). Qed.
Lemma lem1554980 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1554979 h1) (@lem1554978 h1)). Qed.
Lemma lem1554981 : term302.
Proof. exact (fun h0 : term23 => @lem1554980 h0). Qed.
Lemma lem1554982 : term303.
Proof. exact (@lem1386578 term304). Qed.
Lemma lem1554983 : term304.
Proof. exact (@lem1554982 (@lem1554981)). Qed.
