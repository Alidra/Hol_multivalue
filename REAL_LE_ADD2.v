Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_ADD2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1501649 (w : real) (y : real) (x : real) (z : real) : (term0 w y x z) = (term1 w y x z).
Proof. exact (@lem17362 (term2 w x y z) (term3 w y x z)). Qed.
Lemma lem1501650 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501651 (w : real) (y : real) (x : real) : (term6 w y x) = (term7 w y x).
Proof. exact (@lem1501650 (term8 w y x)). Qed.
Lemma lem1501652 (w : real) (y : real) (x : real) (z : real) : (term9 w y x z) = (term10 w y x z).
Proof. exact (eq_refl (term9 w y x z)). Qed.
Lemma lem1501653 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501654 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term0 w y x z).
Proof. exact (MK_COMB (@lem1501653) (@lem1501652 w y x z)). Qed.
Lemma lem1501655 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term1 w y x z).
Proof. exact (TRANS (@lem1501654 w y x z) (@lem1501649 w y x z)). Qed.
Lemma lem1501656 (w : real) (y : real) (x : real) : (term12 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1501655 w y x z)). Qed.
Lemma lem1501657 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501658 (w : real) (y : real) (x : real) : (term7 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1501657) (@lem1501656 w y x)). Qed.
Lemma lem1501659 (w : real) (y : real) (x : real) : (term6 w y x) = (term14 w y x).
Proof. exact (TRANS (@lem1501651 w y x) (@lem1501658 w y x)). Qed.
Lemma lem1501660 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501661 (w : real) (x : real) : (term15 w x) = (term16 w x).
Proof. exact (@lem1501660 (term17 w x)). Qed.
Lemma lem1501662 (w : real) (y : real) (x : real) : (term18 w x y) = (term19 w y x).
Proof. exact (eq_refl (term18 w x y)). Qed.
Lemma lem1501663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501664 (w : real) (y : real) (x : real) : (term20 w x y) = (term6 w y x).
Proof. exact (MK_COMB (@lem1501663) (@lem1501662 w y x)). Qed.
Lemma lem1501665 (w : real) (y : real) (x : real) : (term20 w x y) = (term14 w y x).
Proof. exact (TRANS (@lem1501664 w y x) (@lem1501659 w y x)). Qed.
Lemma lem1501666 (w : real) (x : real) : (term21 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1501665 w y x)). Qed.
Lemma lem1501667 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501668 (w : real) (x : real) : (term16 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1501667) (@lem1501666 w x)). Qed.
Lemma lem1501669 (w : real) (x : real) : (term15 w x) = (term23 w x).
Proof. exact (TRANS (@lem1501661 w x) (@lem1501668 w x)). Qed.
Lemma lem1501670 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501671 (w : real) : (term24 w) = (term25 w).
Proof. exact (@lem1501670 (term26 w)). Qed.
Lemma lem1501672 (w : real) (x : real) : (term27 w x) = (term28 w x).
Proof. exact (eq_refl (term27 w x)). Qed.
Lemma lem1501673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501674 (w : real) (x : real) : (term29 w x) = (term15 w x).
Proof. exact (MK_COMB (@lem1501673) (@lem1501672 w x)). Qed.
Lemma lem1501675 (w : real) (x : real) : (term29 w x) = (term23 w x).
Proof. exact (TRANS (@lem1501674 w x) (@lem1501669 w x)). Qed.
Lemma lem1501676 (w : real) : (term30 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1501675 w x)). Qed.
Lemma lem1501677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501678 (w : real) : (term25 w) = (term32 w).
Proof. exact (MK_COMB (@lem1501677) (@lem1501676 w)). Qed.
Lemma lem1501679 (w : real) : (term24 w) = (term32 w).
Proof. exact (TRANS (@lem1501671 w) (@lem1501678 w)). Qed.
Lemma lem1501680 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501681 : term33 = term34.
Proof. exact (@lem1501680 term35). Qed.
Lemma lem1501682 (w : real) : (term36 w) = (term37 w).
Proof. exact (eq_refl (term36 w)). Qed.
Lemma lem1501683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501684 (w : real) : (term38 w) = (term24 w).
Proof. exact (MK_COMB (@lem1501683) (@lem1501682 w)). Qed.
Lemma lem1501685 (w : real) : (term38 w) = (term32 w).
Proof. exact (TRANS (@lem1501684 w) (@lem1501679 w)). Qed.
Lemma lem1501686 : term39 = term40.
Proof. exact (fun_ext (fun w : real => @lem1501685 w)). Qed.
Lemma lem1501687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501688 : term34 = term41.
Proof. exact (MK_COMB (@lem1501687) (@lem1501686)). Qed.
Lemma lem1501690 : term33 = term41.
Proof. exact (TRANS (@lem1501681) (@lem1501688)). Qed.
Lemma lem1501701 (w : real) (y : real) (x : real) (z : real) : (term1 w y x z) = (term1 w y x z).
Proof. exact (eq_refl (term1 w y x z)). Qed.
Lemma lem1501702 (w : real) (y : real) (x : real) : (term13 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1501701 w y x z)). Qed.
Lemma lem1501703 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501704 (w : real) (y : real) (x : real) : (term14 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1501703) (@lem1501702 w y x)). Qed.
Lemma lem1501705 (w : real) (x : real) : (term22 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1501704 w y x)). Qed.
Lemma lem1501706 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501707 (w : real) (x : real) : (term23 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1501706) (@lem1501705 w x)). Qed.
Lemma lem1501708 (w : real) : (term31 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1501707 w x)). Qed.
Lemma lem1501709 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501710 (w : real) : (term32 w) = (term32 w).
Proof. exact (MK_COMB (@lem1501709) (@lem1501708 w)). Qed.
Lemma lem1501711 : term40 = term40.
Proof. exact (fun_ext (fun w : real => @lem1501710 w)). Qed.
Lemma lem1501712 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501713 : term41 = term41.
Proof. exact (MK_COMB (@lem1501712) (@lem1501711)). Qed.
Lemma lem1501714 : term33 = term41.
Proof. exact (TRANS (@lem1501690) (@lem1501713)). Qed.
Lemma lem1501715 (x : real) (w : real) : (real_le w x) = (term42 x w).
Proof. exact (@lem1483523 x w). Qed.
Lemma lem1501721 (x : real) (w : real) : (real_sub x w) = (term43 x w).
Proof. exact (@lem1483519 x w). Qed.
Lemma lem1501726 (w : real) (x : real) : (term43 x w) = (term44 w x).
Proof. exact (@lem1483488 (term45 w) x). Qed.
Lemma lem1501728 (w : real) (x : real) : (real_sub x w) = (term44 w x).
Proof. exact (TRANS (@lem1501721 x w) (@lem1501726 w x)). Qed.
Lemma lem1501729 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501730 (w : real) (x : real) : (term46 x w) = (term47 w x).
Proof. exact (MK_COMB (@lem1501729) (@lem1501728 w x)). Qed.
Lemma lem1501731 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501732 (w : real) (x : real) : (term42 x w) = (term49 w x).
Proof. exact (MK_COMB (@lem1501730 w x) (@lem1501731)). Qed.
Lemma lem1501733 (w : real) (x : real) : (real_le w x) = (term49 w x).
Proof. exact (TRANS (@lem1501715 x w) (@lem1501732 w x)). Qed.
Lemma lem1501734 (z : real) (y : real) : (real_le y z) = (term42 z y).
Proof. exact (@lem1483523 z y). Qed.
Lemma lem1501740 (z : real) (y : real) : (real_sub z y) = (term43 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1501745 (y : real) (z : real) : (term43 z y) = (term44 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1501747 (y : real) (z : real) : (real_sub z y) = (term44 y z).
Proof. exact (TRANS (@lem1501740 z y) (@lem1501745 y z)). Qed.
Lemma lem1501748 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501749 (y : real) (z : real) : (term46 z y) = (term47 y z).
Proof. exact (MK_COMB (@lem1501748) (@lem1501747 y z)). Qed.
Lemma lem1501750 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501751 (y : real) (z : real) : (term42 z y) = (term49 y z).
Proof. exact (MK_COMB (@lem1501749 y z) (@lem1501750)). Qed.
Lemma lem1501752 (y : real) (z : real) : (real_le y z) = (term49 y z).
Proof. exact (TRANS (@lem1501734 z y) (@lem1501751 y z)). Qed.
Lemma lem1501753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1501754 (w : real) (x : real) : (term50 w x) = (term51 w x).
Proof. exact (MK_COMB (@lem1501753) (@lem1501733 w x)). Qed.
Lemma lem1501755 (w : real) (x : real) (y : real) (z : real) : (term2 w x y z) = (term52 w x y z).
Proof. exact (MK_COMB (@lem1501754 w x) (@lem1501752 y z)). Qed.
Lemma lem1501756 (w : real) (y : real) (x : real) (z : real) : (term53 w y x z) = (term54 w y x z).
Proof. exact (@lem1483533 (real_add w y) (real_add x z)). Qed.
Lemma lem1501774 (w : real) (y : real) (x : real) (z : real) : (term55 w y x z) = (term56 w y x z).
Proof. exact (@lem1483519 (real_add w y) (real_add x z)). Qed.
Lemma lem1501781 (x : real) (z : real) : (term57 x z) = (term58 x z).
Proof. exact (@lem1483508 x term59 z). Qed.
Lemma lem1501782 (w : real) (y : real) : (term60 w y) = (term60 w y).
Proof. exact (eq_refl (term60 w y)). Qed.
Lemma lem1501783 (w : real) (y : real) (x : real) (z : real) : (term56 w y x z) = (term61 w y x z).
Proof. exact (MK_COMB (@lem1501782 w y) (@lem1501781 x z)). Qed.
Lemma lem1501784 (w : real) (y : real) (x : real) (z : real) : (term61 w y x z) = (term62 w y x z).
Proof. exact (@lem1483482 w y (term58 x z)). Qed.
Lemma lem1501789 (x : real) (y : real) (z : real) : (term63 y x z) = (term64 x y z).
Proof. exact (@lem1483484 (term45 x) y (term45 z)). Qed.
Lemma lem1501790 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1501791 (w : real) (x : real) (y : real) (z : real) : (term62 w y x z) = (term65 w x y z).
Proof. exact (MK_COMB (@lem1501790 w) (@lem1501789 x y z)). Qed.
Lemma lem1501792 (w : real) (x : real) (y : real) (z : real) : (term61 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501784 w y x z) (@lem1501791 w x y z)). Qed.
Lemma lem1501793 (w : real) (x : real) (y : real) (z : real) : (term56 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501783 w y x z) (@lem1501792 w x y z)). Qed.
Lemma lem1501795 (w : real) (x : real) (y : real) (z : real) : (term55 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501774 w y x z) (@lem1501793 w x y z)). Qed.
Lemma lem1501796 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501797 (w : real) (x : real) (y : real) (z : real) : (term66 w y x z) = (term67 w x y z).
Proof. exact (MK_COMB (@lem1501796) (@lem1501795 w x y z)). Qed.
Lemma lem1501798 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501799 (w : real) (x : real) (y : real) (z : real) : (term54 w y x z) = (term68 w x y z).
Proof. exact (MK_COMB (@lem1501797 w x y z) (@lem1501798)). Qed.
Lemma lem1501800 (w : real) (x : real) (y : real) (z : real) : (term53 w y x z) = (term68 w x y z).
Proof. exact (TRANS (@lem1501756 w y x z) (@lem1501799 w x y z)). Qed.
Lemma lem1501801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1501802 (w : real) (x : real) (y : real) (z : real) : (term69 w x y z) = (term70 w x y z).
Proof. exact (MK_COMB (@lem1501801) (@lem1501755 w x y z)). Qed.
Lemma lem1501803 (w : real) (x : real) (y : real) (z : real) : (term1 w y x z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1501802 w x y z) (@lem1501800 w x y z)). Qed.
Lemma lem1501804 (w : real) (x : real) (y : real) : (term13 w y x) = (term72 w x y).
Proof. exact (fun_ext (fun z : real => @lem1501803 w x y z)). Qed.
Lemma lem1501805 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501806 (w : real) (x : real) (y : real) : (term14 w y x) = (term73 w x y).
Proof. exact (MK_COMB (@lem1501805) (@lem1501804 w x y)). Qed.
Lemma lem1501807 (w : real) (x : real) : (term22 w x) = (term74 w x).
Proof. exact (fun_ext (fun y : real => @lem1501806 w x y)). Qed.
Lemma lem1501808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501809 (w : real) (x : real) : (term23 w x) = (term75 w x).
Proof. exact (MK_COMB (@lem1501808) (@lem1501807 w x)). Qed.
Lemma lem1501810 (w : real) : (term31 w) = (term76 w).
Proof. exact (fun_ext (fun x : real => @lem1501809 w x)). Qed.
Lemma lem1501811 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501812 (w : real) : (term32 w) = (term77 w).
Proof. exact (MK_COMB (@lem1501811) (@lem1501810 w)). Qed.
Lemma lem1501813 : term40 = term78.
Proof. exact (fun_ext (fun w : real => @lem1501812 w)). Qed.
Lemma lem1501814 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501815 : term41 = term79.
Proof. exact (MK_COMB (@lem1501814) (@lem1501813)). Qed.
Lemma lem1501882 : term33 = term79.
Proof. exact (TRANS (@lem1501714) (@lem1501815)). Qed.
Lemma lem1501895 (w : real) (x : real) (y : real) (z : real) : (term71 w x y z) = (term71 w x y z).
Proof. exact (eq_refl (term71 w x y z)). Qed.
Lemma lem1501896 (w : real) (x : real) (y : real) : (term72 w x y) = (term72 w x y).
Proof. exact (fun_ext (fun z : real => @lem1501895 w x y z)). Qed.
Lemma lem1501897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501898 (w : real) (x : real) (y : real) : (term73 w x y) = (term73 w x y).
Proof. exact (MK_COMB (@lem1501897) (@lem1501896 w x y)). Qed.
Lemma lem1501899 (w : real) (x : real) : (term74 w x) = (term74 w x).
Proof. exact (fun_ext (fun y : real => @lem1501898 w x y)). Qed.
Lemma lem1501900 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501901 (w : real) (x : real) : (term75 w x) = (term75 w x).
Proof. exact (MK_COMB (@lem1501900) (@lem1501899 w x)). Qed.
Lemma lem1501902 (w : real) : (term76 w) = (term76 w).
Proof. exact (fun_ext (fun x : real => @lem1501901 w x)). Qed.
Lemma lem1501903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501904 (w : real) : (term77 w) = (term77 w).
Proof. exact (MK_COMB (@lem1501903) (@lem1501902 w)). Qed.
Lemma lem1501905 : term78 = term78.
Proof. exact (fun_ext (fun w : real => @lem1501904 w)). Qed.
Lemma lem1501906 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501907 : term79 = term79.
Proof. exact (MK_COMB (@lem1501906) (@lem1501905)). Qed.
Lemma lem1501908 : term33 = term79.
Proof. exact (TRANS (@lem1501882) (@lem1501907)). Qed.
Lemma lem1501912 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term71 w x y z.
Proof. exact (h1). Qed.
Lemma lem1501913 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term68 w x y z.
Proof. exact (proj2 (@lem1501912 w x y z h1)). Qed.
Lemma lem1501914 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term52 w x y z.
Proof. exact (proj1 (@lem1501912 w x y z h1)). Qed.
Lemma lem1501915 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 y z.
Proof. exact (proj2 (@lem1501914 w x y z h1)). Qed.
Lemma lem1501916 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 w x.
Proof. exact (proj1 (@lem1501914 w x y z h1)). Qed.
Lemma lem1501918 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501919 : term81 = term82.
Proof. exact (@lem1501918 (NUMERAL 0) term83). Qed.
Lemma lem1501920 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501921 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501922 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501921 h1) (fun h1 : term82 = True => @lem1501920)). Qed.
Lemma lem1501923 : term82 = True.
Proof. exact (EQ_MP (@lem1501922) (@lem1501920)). Qed.
Lemma lem1501924 : term81 = True.
Proof. exact (TRANS (@lem1501919) (@lem1501923)). Qed.
Lemma lem1501925 : True = term81.
Proof. exact (SYM (@lem1501924)). Qed.
Lemma lem1501926 : term81.
Proof. exact (EQ_MP (@lem1501925) (@lem0)). Qed.
Lemma lem1501927 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term85 w x.
Proof. exact (conj (@lem1501926) (@lem1501916 w x y z h1)). Qed.
Lemma lem1501929 (x : real) (y : real) : term86 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1501930 (w : real) (x : real) : term87 w x.
Proof. exact (@lem1501929 term88 (term44 w x)). Qed.
Lemma lem1501931 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term89 w x.
Proof. exact (@lem1501930 w x (@lem1501927 w x y z h1)). Qed.
Lemma lem1501932 (w : real) (x : real) : (term90 w x) = (term44 w x).
Proof. exact (@lem1483460 (term44 w x)). Qed.
Lemma lem1501933 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501934 (w : real) (x : real) : (term91 w x) = (term47 w x).
Proof. exact (MK_COMB (@lem1501933) (@lem1501932 w x)). Qed.
Lemma lem1501935 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501936 (w : real) (x : real) : (term89 w x) = (term49 w x).
Proof. exact (MK_COMB (@lem1501934 w x) (@lem1501935)). Qed.
Lemma lem1501937 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 w x.
Proof. exact (EQ_MP (@lem1501936 w x) (@lem1501931 w x y z h1)). Qed.
Lemma lem1501939 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501940 : term81 = term82.
Proof. exact (@lem1501939 (NUMERAL 0) term83). Qed.
Lemma lem1501941 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501942 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501943 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501942 h1) (fun h1 : term82 = True => @lem1501941)). Qed.
Lemma lem1501944 : term82 = True.
Proof. exact (EQ_MP (@lem1501943) (@lem1501941)). Qed.
Lemma lem1501945 : term81 = True.
Proof. exact (TRANS (@lem1501940) (@lem1501944)). Qed.
Lemma lem1501946 : True = term81.
Proof. exact (SYM (@lem1501945)). Qed.
Lemma lem1501947 : term81.
Proof. exact (EQ_MP (@lem1501946) (@lem0)). Qed.
Lemma lem1501948 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term85 y z.
Proof. exact (conj (@lem1501947) (@lem1501915 w x y z h1)). Qed.
Lemma lem1501950 (x : real) (y : real) : term86 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1501951 (y : real) (z : real) : term87 y z.
Proof. exact (@lem1501950 term88 (term44 y z)). Qed.
Lemma lem1501952 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term89 y z.
Proof. exact (@lem1501951 y z (@lem1501948 w x y z h1)). Qed.
Lemma lem1501953 (y : real) (z : real) : (term90 y z) = (term44 y z).
Proof. exact (@lem1483460 (term44 y z)). Qed.
Lemma lem1501954 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501955 (y : real) (z : real) : (term91 y z) = (term47 y z).
Proof. exact (MK_COMB (@lem1501954) (@lem1501953 y z)). Qed.
Lemma lem1501956 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501957 (y : real) (z : real) : (term89 y z) = (term49 y z).
Proof. exact (MK_COMB (@lem1501955 y z) (@lem1501956)). Qed.
Lemma lem1501958 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 y z.
Proof. exact (EQ_MP (@lem1501957 y z) (@lem1501952 w x y z h1)). Qed.
Lemma lem1501960 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501961 : term81 = term82.
Proof. exact (@lem1501960 (NUMERAL 0) term83). Qed.
Lemma lem1501962 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501963 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501964 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501963 h1) (fun h1 : term82 = True => @lem1501962)). Qed.
Lemma lem1501965 : term82 = True.
Proof. exact (EQ_MP (@lem1501964) (@lem1501962)). Qed.
Lemma lem1501966 : term81 = True.
Proof. exact (TRANS (@lem1501961) (@lem1501965)). Qed.
Lemma lem1501967 : True = term81.
Proof. exact (SYM (@lem1501966)). Qed.
Lemma lem1501968 : term81.
Proof. exact (EQ_MP (@lem1501967) (@lem0)). Qed.
Lemma lem1501969 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term92 w x y z.
Proof. exact (conj (@lem1501968) (@lem1501913 w x y z h1)). Qed.
Lemma lem1501971 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1501972 (w : real) (x : real) (y : real) (z : real) : term94 w x y z.
Proof. exact (@lem1501971 term88 (term65 w x y z)). Qed.
Lemma lem1501973 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term95 w x y z.
Proof. exact (@lem1501972 w x y z (@lem1501969 w x y z h1)). Qed.
Lemma lem1501974 (w : real) (x : real) (y : real) (z : real) : (term96 w x y z) = (term65 w x y z).
Proof. exact (@lem1483460 (term65 w x y z)). Qed.
Lemma lem1501975 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501976 (w : real) (x : real) (y : real) (z : real) : (term97 w x y z) = (term67 w x y z).
Proof. exact (MK_COMB (@lem1501975) (@lem1501974 w x y z)). Qed.
Lemma lem1501977 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501978 (w : real) (x : real) (y : real) (z : real) : (term95 w x y z) = (term68 w x y z).
Proof. exact (MK_COMB (@lem1501976 w x y z) (@lem1501977)). Qed.
Lemma lem1501979 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term68 w x y z.
Proof. exact (EQ_MP (@lem1501978 w x y z) (@lem1501973 w x y z h1)). Qed.
Lemma lem1501980 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term98 w x y z.
Proof. exact (conj (@lem1501979 w x y z h1) (@lem1501958 w x y z h1)). Qed.
Lemma lem1501982 (x : real) (y : real) : term99 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1501983 (w : real) (x : real) (y : real) (z : real) : term100 w x y z.
Proof. exact (@lem1501982 (term65 w x y z) (term44 y z)). Qed.
Lemma lem1501984 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term101 w x y z.
Proof. exact (@lem1501983 w x y z (@lem1501980 w x y z h1)). Qed.
Lemma lem1501985 (w : real) (x : real) (y : real) (z : real) : (term102 w x y z) = (term103 w x y z).
Proof. exact (@lem1483482 w (term64 x y z) (term44 y z)). Qed.
Lemma lem1501986 (x : real) (y : real) (z : real) : (term104 x y z) = (term105 x y z).
Proof. exact (@lem1483482 (term45 x) (term43 y z) (term44 y z)). Qed.
Lemma lem1501987 (y : real) (z : real) : (term106 y z) = (term107 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1501988 (y : real) : (term108 y) = (term109 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1501990 (m : nat) : (term110 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501991 : term111 = term48.
Proof. exact (@lem1501990 term83). Qed.
Lemma lem1501992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501993 : term112 = term113.
Proof. exact (MK_COMB (@lem1501992) (@lem1501991)). Qed.
Lemma lem1501994 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1501995 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1501993) (@lem1501994 y)). Qed.
Lemma lem1501996 (y : real) : (term108 y) = (term114 y).
Proof. exact (TRANS (@lem1501988 y) (@lem1501995 y)). Qed.
Lemma lem1501997 (y : real) : (term114 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1501998 (y : real) : (term108 y) = term48.
Proof. exact (TRANS (@lem1501996 y) (@lem1501997 y)). Qed.
Lemma lem1501999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1502000 (y : real) : (term115 y) = term116.
Proof. exact (MK_COMB (@lem1501999) (@lem1501998 y)). Qed.
Lemma lem1502001 (z : real) : (term117 z) = (term109 z).
Proof. exact (@lem1483440 term59 z). Qed.
Lemma lem1502003 (m : nat) : (term110 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1502004 : term111 = term48.
Proof. exact (@lem1502003 term83). Qed.
Lemma lem1502005 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1502006 : term112 = term113.
Proof. exact (MK_COMB (@lem1502005) (@lem1502004)). Qed.
Lemma lem1502007 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1502008 (z : real) : (term109 z) = (term114 z).
Proof. exact (MK_COMB (@lem1502006) (@lem1502007 z)). Qed.
Lemma lem1502009 (z : real) : (term117 z) = (term114 z).
Proof. exact (TRANS (@lem1502001 z) (@lem1502008 z)). Qed.
Lemma lem1502010 (z : real) : (term114 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1502011 (z : real) : (term117 z) = term48.
Proof. exact (TRANS (@lem1502009 z) (@lem1502010 z)). Qed.
Lemma lem1502012 (y : real) (z : real) : (term107 y z) = term118.
Proof. exact (MK_COMB (@lem1502000 y) (@lem1502011 z)). Qed.
Lemma lem1502013 (y : real) (z : real) : (term106 y z) = term118.
Proof. exact (TRANS (@lem1501987 y z) (@lem1502012 y z)). Qed.
Lemma lem1502014 : term118 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1502015 (y : real) (z : real) : (term106 y z) = term48.
Proof. exact (TRANS (@lem1502013 y z) (@lem1502014)). Qed.
Lemma lem1502016 (x : real) : (term119 x) = (term119 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1502017 (y : real) (z : real) (x : real) : (term105 x y z) = (term120 x).
Proof. exact (MK_COMB (@lem1502016 x) (@lem1502015 y z)). Qed.
Lemma lem1502018 (y : real) (z : real) (x : real) : (term104 x y z) = (term120 x).
Proof. exact (TRANS (@lem1501986 x y z) (@lem1502017 y z x)). Qed.
Lemma lem1502019 (x : real) : (term120 x) = (term45 x).
Proof. exact (@lem1483450 (term45 x)). Qed.
Lemma lem1502020 (y : real) (z : real) (x : real) : (term104 x y z) = (term45 x).
Proof. exact (TRANS (@lem1502018 y z x) (@lem1502019 x)). Qed.
Lemma lem1502021 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1502022 (y : real) (z : real) (w : real) (x : real) : (term103 w x y z) = (term43 w x).
Proof. exact (MK_COMB (@lem1502021 w) (@lem1502020 y z x)). Qed.
Lemma lem1502023 (y : real) (z : real) (w : real) (x : real) : (term102 w x y z) = (term43 w x).
Proof. exact (TRANS (@lem1501985 w x y z) (@lem1502022 y z w x)). Qed.
Lemma lem1502024 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1502025 (y : real) (z : real) (w : real) (x : real) : (term121 w x y z) = (term122 w x).
Proof. exact (MK_COMB (@lem1502024) (@lem1502023 y z w x)). Qed.
Lemma lem1502026 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1502027 (y : real) (z : real) (w : real) (x : real) : (term101 w x y z) = (term123 w x).
Proof. exact (MK_COMB (@lem1502025 y z w x) (@lem1502026)). Qed.
Lemma lem1502028 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term123 w x.
Proof. exact (EQ_MP (@lem1502027 y z w x) (@lem1501984 w x y z h1)). Qed.
Lemma lem1502030 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1502031 : term81 = term82.
Proof. exact (@lem1502030 (NUMERAL 0) term83). Qed.
Lemma lem1502032 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1502033 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1502034 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1502033 h1) (fun h1 : term82 = True => @lem1502032)). Qed.
Lemma lem1502035 : term82 = True.
Proof. exact (EQ_MP (@lem1502034) (@lem1502032)). Qed.
Lemma lem1502036 : term81 = True.
Proof. exact (TRANS (@lem1502031) (@lem1502035)). Qed.
Lemma lem1502037 : True = term81.
Proof. exact (SYM (@lem1502036)). Qed.
Lemma lem1502038 : term81.
Proof. exact (EQ_MP (@lem1502037) (@lem0)). Qed.
Lemma lem1502039 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term124 w x.
Proof. exact (conj (@lem1502038) (@lem1502028 w x y z h1)). Qed.
Lemma lem1502041 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1502042 (w : real) (x : real) : term125 w x.
Proof. exact (@lem1502041 term88 (term43 w x)). Qed.
Lemma lem1502043 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term126 w x.
Proof. exact (@lem1502042 w x (@lem1502039 w x y z h1)). Qed.
Lemma lem1502044 (w : real) (x : real) : (term127 w x) = (term43 w x).
Proof. exact (@lem1483460 (term43 w x)). Qed.
Lemma lem1502045 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1502046 (w : real) (x : real) : (term128 w x) = (term122 w x).
Proof. exact (MK_COMB (@lem1502045) (@lem1502044 w x)). Qed.
Lemma lem1502047 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1502048 (w : real) (x : real) : (term126 w x) = (term123 w x).
Proof. exact (MK_COMB (@lem1502046 w x) (@lem1502047)). Qed.
Lemma lem1502049 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term123 w x.
Proof. exact (EQ_MP (@lem1502048 w x) (@lem1502043 w x y z h1)). Qed.
Lemma lem1502050 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term129 w x.
Proof. exact (conj (@lem1502049 w x y z h1) (@lem1501937 w x y z h1)). Qed.
Lemma lem1502052 (x : real) (y : real) : term99 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1502053 (w : real) (x : real) : term130 w x.
Proof. exact (@lem1502052 (term43 w x) (term44 w x)). Qed.
Lemma lem1502054 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term131 w x.
Proof. exact (@lem1502053 w x (@lem1502050 w x y z h1)). Qed.
Lemma lem1502055 (w : real) (x : real) : (term106 w x) = (term107 w x).
Proof. exact (@lem1483480 w (term45 w) (term45 x) x). Qed.
Lemma lem1502056 (w : real) : (term108 w) = (term109 w).
Proof. exact (@lem1483442 term59 w). Qed.
Lemma lem1502058 (m : nat) : (term110 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1502059 : term111 = term48.
Proof. exact (@lem1502058 term83). Qed.
Lemma lem1502060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1502061 : term112 = term113.
Proof. exact (MK_COMB (@lem1502060) (@lem1502059)). Qed.
Lemma lem1502062 (w : real) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem1502063 (w : real) : (term109 w) = (term114 w).
Proof. exact (MK_COMB (@lem1502061) (@lem1502062 w)). Qed.
Lemma lem1502064 (w : real) : (term108 w) = (term114 w).
Proof. exact (TRANS (@lem1502056 w) (@lem1502063 w)). Qed.
Lemma lem1502065 (w : real) : (term114 w) = term48.
Proof. exact (@lem1483446 w). Qed.
Lemma lem1502066 (w : real) : (term108 w) = term48.
Proof. exact (TRANS (@lem1502064 w) (@lem1502065 w)). Qed.
Lemma lem1502067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1502068 (w : real) : (term115 w) = term116.
Proof. exact (MK_COMB (@lem1502067) (@lem1502066 w)). Qed.
Lemma lem1502069 (x : real) : (term117 x) = (term109 x).
Proof. exact (@lem1483440 term59 x). Qed.
Lemma lem1502071 (m : nat) : (term110 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1502072 : term111 = term48.
Proof. exact (@lem1502071 term83). Qed.
Lemma lem1502073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1502074 : term112 = term113.
Proof. exact (MK_COMB (@lem1502073) (@lem1502072)). Qed.
Lemma lem1502075 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1502076 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1502074) (@lem1502075 x)). Qed.
Lemma lem1502077 (x : real) : (term117 x) = (term114 x).
Proof. exact (TRANS (@lem1502069 x) (@lem1502076 x)). Qed.
Lemma lem1502078 (x : real) : (term114 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1502079 (x : real) : (term117 x) = term48.
Proof. exact (TRANS (@lem1502077 x) (@lem1502078 x)). Qed.
Lemma lem1502080 (w : real) (x : real) : (term107 w x) = term118.
Proof. exact (MK_COMB (@lem1502068 w) (@lem1502079 x)). Qed.
Lemma lem1502081 (w : real) (x : real) : (term106 w x) = term118.
Proof. exact (TRANS (@lem1502055 w x) (@lem1502080 w x)). Qed.
Lemma lem1502082 : term118 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1502083 (w : real) (x : real) : (term106 w x) = term48.
Proof. exact (TRANS (@lem1502081 w x) (@lem1502082)). Qed.
Lemma lem1502084 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1502085 (w : real) (x : real) : (term132 w x) = term133.
Proof. exact (MK_COMB (@lem1502084) (@lem1502083 w x)). Qed.
Lemma lem1502086 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1502087 (w : real) (x : real) : (term131 w x) = term134.
Proof. exact (MK_COMB (@lem1502085 w x) (@lem1502086)). Qed.
Lemma lem1502088 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term134.
Proof. exact (EQ_MP (@lem1502087 w x) (@lem1502054 w x y z h1)). Qed.
Lemma lem1502090 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1502091 : term134 = term135.
Proof. exact (@lem1502090 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1502092 : term135 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1502093 : term134 = False.
Proof. exact (TRANS (@lem1502091) (@lem1502092)). Qed.
Lemma lem1502094 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : False.
Proof. exact (EQ_MP (@lem1502093) (@lem1502088 w x y z h1)). Qed.
Lemma lem1502096 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term71 w x y z.
Proof. exact (h1). Qed.
Lemma lem1502097 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : (term71 w x y z) = False.
Proof. exact (prop_ext (fun h2 : term71 w x y z => @lem1502094 w x y z h1) (fun h2 : False => @lem1502096 w x y z h1)). Qed.
Lemma lem1502098 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : False.
Proof. exact (EQ_MP (@lem1502097 w x y z h1) (@lem1502096 w x y z h1)). Qed.
Lemma lem1502099 (w : real) (x : real) (y : real) (h1 : term73 w x y) : term73 w x y.
Proof. exact (h1). Qed.
Lemma lem1502100 (w : real) (x : real) (y : real) (h1 : term73 w x y) : False.
Proof. exact (ex_elim (@lem1502099 w x y h1) (fun z : real => fun h0 : term72 w x y z => @lem1502098 w x y z h0)). Qed.
Lemma lem1502101 (w : real) (x : real) (h1 : term75 w x) : term75 w x.
Proof. exact (h1). Qed.
Lemma lem1502102 (w : real) (x : real) (h1 : term75 w x) : False.
Proof. exact (ex_elim (@lem1502101 w x h1) (fun y : real => fun h0 : term74 w x y => @lem1502100 w x y h0)). Qed.
Lemma lem1502103 (w : real) (h1 : term77 w) : term77 w.
Proof. exact (h1). Qed.
Lemma lem1502104 (w : real) (h1 : term77 w) : False.
Proof. exact (ex_elim (@lem1502103 w h1) (fun x : real => fun h0 : term76 w x => @lem1502102 w x h0)). Qed.
Lemma lem1502105 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem1502106 (h1 : term79) : False.
Proof. exact (ex_elim (@lem1502105 h1) (fun w : real => fun h0 : term78 w => @lem1502104 w h0)). Qed.
Lemma lem1502107 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1502108 (h1 : term33) : term79.
Proof. exact (EQ_MP (@lem1501908) (@lem1502107 h1)). Qed.
Lemma lem1502109 (h1 : term33) : term79 = False.
Proof. exact (prop_ext (fun h2 : term79 => @lem1502106 h2) (fun h2 : False => @lem1502108 h1)). Qed.
Lemma lem1502110 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem1502109 h1) (@lem1502108 h1)). Qed.
Lemma lem1502111 : term136.
Proof. exact (fun h0 : term33 => @lem1502110 h0). Qed.
Lemma lem1502112 : term137.
Proof. exact (@lem1386578 term138). Qed.
Lemma lem1502113 : term138.
Proof. exact (@lem1502112 (@lem1502111)). Qed.
