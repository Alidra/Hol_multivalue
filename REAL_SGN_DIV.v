Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_DIV_term_abbrevs.
Require Import REAL_ABS_DIV_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_SGN_spec.
Require Import real_div_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483466_spec.
Require Import thm1483474_spec.
Require Import thm1483478_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1734684 (x : real) : term0 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1734685 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1734687 (x : real) : term2 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1734688 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1734689 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1734688 x) (@lem1734687 x)). Qed.
Lemma lem1734690 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1734689 x y). Qed.
Lemma lem1734691 (x : real) (y : real) : (term4 x y) = ((term5 x y) = (term6 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1734693 (x : real) : term7 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1734694 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1734695 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1734694 x) (@lem1734693 x)). Qed.
Lemma lem1734696 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1734695 x y). Qed.
Lemma lem1734697 (x : real) (y : real) : (term9 x y) = ((real_div x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1734699 (x : real) : term11 x.
Proof. exact (@lem1594900 x). Qed.
Lemma lem1734700 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1734701 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1734700 x) (@lem1734699 x)). Qed.
Lemma lem1734702 (x : real) (y : real) : term13 x y.
Proof. exact (@lem1734701 x y). Qed.
Lemma lem1734703 (x : real) (y : real) : (term13 x y) = ((term14 x y) = (term15 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1734705 (x : real) : term16 x.
Proof. exact (@lem1733933 x). Qed.
Lemma lem1734706 (x : real) : (term16 x) = ((real_sgn x) = (term17 x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1734719 (x : real) : (real_sgn x) = (term17 x).
Proof. exact (EQ_MP (@lem1734706 x) (@lem1734705 x)). Qed.
Lemma lem1734720 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (@lem1734719 (real_div x y)). Qed.
Lemma lem1734722 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1734703 x y) (@lem1734702 x y)). Qed.
Lemma lem1734723 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1734724 (x : real) (y : real) : (term19 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1734723 x y) (@lem1734722 x y)). Qed.
Lemma lem1734725 (x : real) (y : real) : (term18 x y) = (term21 x y).
Proof. exact (TRANS (@lem1734720 x y) (@lem1734724 x y)). Qed.
Lemma lem1734726 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1734727 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1734726) (@lem1734725 x y)). Qed.
Lemma lem1734729 (x : real) : (real_sgn x) = (term17 x).
Proof. exact (EQ_MP (@lem1734706 x) (@lem1734705 x)). Qed.
Lemma lem1734730 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1734731 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1734730) (@lem1734729 x)). Qed.
Lemma lem1734733 (x : real) : (real_sgn x) = (term17 x).
Proof. exact (EQ_MP (@lem1734706 x) (@lem1734705 x)). Qed.
Lemma lem1734734 (y : real) : (real_sgn y) = (term17 y).
Proof. exact (@lem1734733 y). Qed.
Lemma lem1734735 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1734731 x) (@lem1734734 y)). Qed.
Lemma lem1734736 (x : real) (y : real) : ((term18 x y) = (term26 x y)) = ((term21 x y) = (term27 x y)).
Proof. exact (MK_COMB (@lem1734727 x y) (@lem1734735 x y)). Qed.
Lemma lem1734739 (x : real) : (term28 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1734736 x y)). Qed.
Lemma lem1734740 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734741 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1734740) (@lem1734739 x)). Qed.
Lemma lem1734746 : term32 = term33.
Proof. exact (fun_ext (fun x : real => @lem1734741 x)). Qed.
Lemma lem1734747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734748 : term34 = term35.
Proof. exact (MK_COMB (@lem1734747) (@lem1734746)). Qed.
Lemma lem1734753 : term35 = term34.
Proof. exact (SYM (@lem1734748)). Qed.
Lemma lem1734765 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734766 (x : real) (y : real) : (term21 x y) = (term36 x y).
Proof. exact (@lem1734765 (real_div x y) (term15 x y)). Qed.
Lemma lem1734768 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734770 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1734769) (@lem1734768 x y)). Qed.
Lemma lem1734772 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734773 (x : real) (y : real) : (term15 x y) = (term39 x y).
Proof. exact (@lem1734772 (real_abs x) (real_abs y)). Qed.
Lemma lem1734774 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1734775 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1734774) (@lem1734773 x y)). Qed.
Lemma lem1734777 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1734691 x y) (@lem1734690 x y)). Qed.
Lemma lem1734778 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (@lem1734777 (real_abs x) (term43 y)). Qed.
Lemma lem1734780 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1734685 x) (@lem1734684 x)). Qed.
Lemma lem1734781 (y : real) : (term44 y) = (real_abs y).
Proof. exact (@lem1734780 (real_abs y)). Qed.
Lemma lem1734782 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1734783 (x : real) (y : real) : (term42 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1734782 x) (@lem1734781 y)). Qed.
Lemma lem1734784 (x : real) (y : real) : (term41 x y) = (term46 x y).
Proof. exact (TRANS (@lem1734778 x y) (@lem1734783 x y)). Qed.
Lemma lem1734785 (x : real) (y : real) : (term40 x y) = (term46 x y).
Proof. exact (TRANS (@lem1734775 x y) (@lem1734784 x y)). Qed.
Lemma lem1734786 (x : real) (y : real) : (term36 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1734770 x y) (@lem1734785 x y)). Qed.
Lemma lem1734787 (x : real) (y : real) : (term21 x y) = (term47 x y).
Proof. exact (TRANS (@lem1734766 x y) (@lem1734786 x y)). Qed.
Lemma lem1734788 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1734789 (x : real) (y : real) : (term23 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1734788) (@lem1734787 x y)). Qed.
Lemma lem1734791 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734792 (x : real) (y : real) : (term27 x y) = (term49 x y).
Proof. exact (@lem1734791 (term17 x) (term17 y)). Qed.
Lemma lem1734794 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734795 (x : real) : (term17 x) = (term50 x).
Proof. exact (@lem1734794 x (real_abs x)). Qed.
Lemma lem1734796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734797 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1734796) (@lem1734795 x)). Qed.
Lemma lem1734799 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1734697 x y) (@lem1734696 x y)). Qed.
Lemma lem1734800 (y : real) : (term17 y) = (term50 y).
Proof. exact (@lem1734799 y (real_abs y)). Qed.
Lemma lem1734801 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1734802 (y : real) : (term53 y) = (term54 y).
Proof. exact (MK_COMB (@lem1734801) (@lem1734800 y)). Qed.
Lemma lem1734804 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1734691 x y) (@lem1734690 x y)). Qed.
Lemma lem1734805 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1734804 y (term43 y)). Qed.
Lemma lem1734807 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1734685 x) (@lem1734684 x)). Qed.
Lemma lem1734808 (y : real) : (term44 y) = (real_abs y).
Proof. exact (@lem1734807 (real_abs y)). Qed.
Lemma lem1734809 (y : real) : (term56 y) = (term56 y).
Proof. exact (eq_refl (term56 y)). Qed.
Lemma lem1734810 (y : real) : (term55 y) = (term57 y).
Proof. exact (MK_COMB (@lem1734809 y) (@lem1734808 y)). Qed.
Lemma lem1734811 (y : real) : (term54 y) = (term57 y).
Proof. exact (TRANS (@lem1734805 y) (@lem1734810 y)). Qed.
Lemma lem1734812 (y : real) : (term53 y) = (term57 y).
Proof. exact (TRANS (@lem1734802 y) (@lem1734811 y)). Qed.
Lemma lem1734813 (x : real) (y : real) : (term49 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1734797 x) (@lem1734812 y)). Qed.
Lemma lem1734814 (x : real) (y : real) : (term27 x y) = (term58 x y).
Proof. exact (TRANS (@lem1734792 x y) (@lem1734813 x y)). Qed.
Lemma lem1734815 (x : real) (y : real) : ((term21 x y) = (term27 x y)) = ((term47 x y) = (term58 x y)).
Proof. exact (MK_COMB (@lem1734789 x y) (@lem1734814 x y)). Qed.
Lemma lem1734818 (x : real) : (term29 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem1734815 x y)). Qed.
Lemma lem1734819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734820 (x : real) : (term31 x) = (term60 x).
Proof. exact (MK_COMB (@lem1734819) (@lem1734818 x)). Qed.
Lemma lem1734825 : term33 = term61.
Proof. exact (fun_ext (fun x : real => @lem1734820 x)). Qed.
Lemma lem1734826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734827 : term35 = term62.
Proof. exact (MK_COMB (@lem1734826) (@lem1734825)). Qed.
Lemma lem1734832 : term62 = term35.
Proof. exact (SYM (@lem1734827)). Qed.
Lemma lem1734845 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1734846 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1734845 (term59 x)). Qed.
Lemma lem1734847 (x : real) (y : real) : (term67 x y) = ((term47 x y) = (term58 x y)).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1734848 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1734850 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1734848) (@lem1734847 x y)). Qed.
Lemma lem1734851 (x : real) : (term70 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1734850 x y)). Qed.
Lemma lem1734852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734853 (x : real) : (term66 x) = (term72 x).
Proof. exact (MK_COMB (@lem1734852) (@lem1734851 x)). Qed.
Lemma lem1734854 (x : real) : (term65 x) = (term72 x).
Proof. exact (TRANS (@lem1734846 x) (@lem1734853 x)). Qed.
Lemma lem1734855 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1734856 : term73 = term74.
Proof. exact (@lem1734855 term61). Qed.
Lemma lem1734857 (x : real) : (term75 x) = (term60 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1734858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1734859 (x : real) : (term76 x) = (term65 x).
Proof. exact (MK_COMB (@lem1734858) (@lem1734857 x)). Qed.
Lemma lem1734860 (x : real) : (term76 x) = (term72 x).
Proof. exact (TRANS (@lem1734859 x) (@lem1734854 x)). Qed.
Lemma lem1734861 : term77 = term78.
Proof. exact (fun_ext (fun x : real => @lem1734860 x)). Qed.
Lemma lem1734862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734863 : term74 = term79.
Proof. exact (MK_COMB (@lem1734862) (@lem1734861)). Qed.
Lemma lem1734865 : term73 = term79.
Proof. exact (TRANS (@lem1734856) (@lem1734863)). Qed.
Lemma lem1734868 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1734869 (x : real) : (term71 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1734868 x y)). Qed.
Lemma lem1734870 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734871 (x : real) : (term72 x) = (term72 x).
Proof. exact (MK_COMB (@lem1734870) (@lem1734869 x)). Qed.
Lemma lem1734872 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1734871 x)). Qed.
Lemma lem1734873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734874 : term79 = term79.
Proof. exact (MK_COMB (@lem1734873) (@lem1734872)). Qed.
Lemma lem1734875 : term73 = term79.
Proof. exact (TRANS (@lem1734865) (@lem1734874)). Qed.
Lemma lem1734876 (x : real) (y : real) : (term69 x y) = (term80 x y).
Proof. exact (@lem1483554 (term47 x y) (term58 x y)). Qed.
Lemma lem1734883 (y : real) : (term57 y) = (term81 y).
Proof. exact (@lem1483474 (real_abs y) (real_inv y)). Qed.
Lemma lem1734892 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1734893 (x : real) (y : real) : (term58 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1734892 x) (@lem1734883 y)). Qed.
Lemma lem1734894 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (@lem1483466 x (term43 x) (real_abs y) (real_inv y)). Qed.
Lemma lem1734895 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (@lem1483478 (real_abs y) (term43 x) (real_inv y)). Qed.
Lemma lem1734896 (y : real) (x : real) : (term86 x y) = (term87 y x).
Proof. exact (@lem1483474 (real_inv y) (term43 x)). Qed.
Lemma lem1734897 (y : real) : (term88 y) = (term88 y).
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1734898 (y : real) (x : real) : (term85 x y) = (term89 y x).
Proof. exact (MK_COMB (@lem1734897 y) (@lem1734896 y x)). Qed.
Lemma lem1734899 (y : real) (x : real) : (term84 x y) = (term89 y x).
Proof. exact (TRANS (@lem1734895 x y) (@lem1734898 y x)). Qed.
Lemma lem1734900 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1734901 (y : real) (x : real) : (term83 x y) = (term90 y x).
Proof. exact (MK_COMB (@lem1734900 x) (@lem1734899 y x)). Qed.
Lemma lem1734902 (y : real) (x : real) : (term82 x y) = (term90 y x).
Proof. exact (TRANS (@lem1734894 x y) (@lem1734901 y x)). Qed.
Lemma lem1734903 (y : real) (x : real) : (term58 x y) = (term90 y x).
Proof. exact (TRANS (@lem1734893 x y) (@lem1734902 y x)). Qed.
Lemma lem1734910 (y : real) (x : real) : (term46 x y) = (term39 y x).
Proof. exact (@lem1483474 (real_abs y) (term43 x)). Qed.
Lemma lem1734919 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1734920 (y : real) (x : real) : (term47 x y) = (term91 y x).
Proof. exact (MK_COMB (@lem1734919 x y) (@lem1734910 y x)). Qed.
Lemma lem1734921 (y : real) (x : real) : (term91 y x) = (term92 y x).
Proof. exact (@lem1483466 x (real_inv y) (real_abs y) (term43 x)). Qed.
Lemma lem1734926 (y : real) (x : real) : (term93 y x) = (term89 y x).
Proof. exact (@lem1483478 (real_abs y) (real_inv y) (term43 x)). Qed.
Lemma lem1734927 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1734928 (y : real) (x : real) : (term92 y x) = (term90 y x).
Proof. exact (MK_COMB (@lem1734927 x) (@lem1734926 y x)). Qed.
Lemma lem1734929 (y : real) (x : real) : (term91 y x) = (term90 y x).
Proof. exact (TRANS (@lem1734921 y x) (@lem1734928 y x)). Qed.
Lemma lem1734930 (y : real) (x : real) : (term47 x y) = (term90 y x).
Proof. exact (TRANS (@lem1734920 y x) (@lem1734929 y x)). Qed.
Lemma lem1734931 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1734932 (y : real) (x : real) : (term94 x y) = (term95 y x).
Proof. exact (MK_COMB (@lem1734931) (@lem1734930 y x)). Qed.
Lemma lem1734933 (y : real) (x : real) : (term96 x y) = (term97 y x).
Proof. exact (MK_COMB (@lem1734932 y x) (@lem1734903 y x)). Qed.
Lemma lem1734934 (y : real) (x : real) : (term97 y x) = (term98 y x).
Proof. exact (@lem1483519 (term90 y x) (term90 y x)). Qed.
Lemma lem1734938 (y : real) (x : real) : (term98 y x) = (term99 y x).
Proof. exact (@lem1483442 term100 (term90 y x)). Qed.
Lemma lem1734940 (m : nat) : (term101 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1734941 : term103 = term102.
Proof. exact (@lem1734940 term104). Qed.
Lemma lem1734942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734943 : term105 = term106.
Proof. exact (MK_COMB (@lem1734942) (@lem1734941)). Qed.
Lemma lem1734944 (y : real) (x : real) : (term90 y x) = (term90 y x).
Proof. exact (eq_refl (term90 y x)). Qed.
Lemma lem1734945 (y : real) (x : real) : (term99 y x) = (term107 y x).
Proof. exact (MK_COMB (@lem1734943) (@lem1734944 y x)). Qed.
Lemma lem1734946 (y : real) (x : real) : (term98 y x) = (term107 y x).
Proof. exact (TRANS (@lem1734938 y x) (@lem1734945 y x)). Qed.
Lemma lem1734947 (y : real) (x : real) : (term107 y x) = term102.
Proof. exact (@lem1483446 (term90 y x)). Qed.
Lemma lem1734949 (y : real) (x : real) : (term98 y x) = term102.
Proof. exact (TRANS (@lem1734946 y x) (@lem1734947 y x)). Qed.
Lemma lem1734950 (y : real) (x : real) : (term97 y x) = term102.
Proof. exact (TRANS (@lem1734934 y x) (@lem1734949 y x)). Qed.
Lemma lem1734951 (x : real) (y : real) : (term96 x y) = term102.
Proof. exact (TRANS (@lem1734933 y x) (@lem1734950 y x)). Qed.
Lemma lem1734952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1734953 (x : real) (y : real) : (term108 x y) = term109.
Proof. exact (MK_COMB (@lem1734952) (@lem1734951 x y)). Qed.
Lemma lem1734954 : term109 = term110.
Proof. exact (@lem1483512 term102). Qed.
Lemma lem1734956 (x : nat) : (term111 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1734957 : term110 = term102.
Proof. exact (@lem1734956 term104). Qed.
Lemma lem1734958 : term109 = term102.
Proof. exact (TRANS (@lem1734954) (@lem1734957)). Qed.
Lemma lem1734959 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1734960 (x : real) (y : real) : ((term108 x y) = term109) = ((term108 x y) = term102).
Proof. exact (MK_COMB (@lem1734959 x y) (@lem1734958)). Qed.
Lemma lem1734961 (x : real) (y : real) : (term108 x y) = term102.
Proof. exact (EQ_MP (@lem1734960 x y) (@lem1734953 x y)). Qed.
Lemma lem1734962 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734963 (x : real) (y : real) : (term113 x y) = term114.
Proof. exact (MK_COMB (@lem1734962) (@lem1734961 x y)). Qed.
Lemma lem1734964 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem1734965 (x : real) (y : real) : (term115 x y) = term116.
Proof. exact (MK_COMB (@lem1734963 x y) (@lem1734964)). Qed.
Lemma lem1734966 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734967 (x : real) (y : real) : (term117 x y) = term114.
Proof. exact (MK_COMB (@lem1734966) (@lem1734951 x y)). Qed.
Lemma lem1734968 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem1734969 (x : real) (y : real) : (term118 x y) = term116.
Proof. exact (MK_COMB (@lem1734967 x y) (@lem1734968)). Qed.
Lemma lem1734970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734971 (x : real) (y : real) : (term119 x y) = term120.
Proof. exact (MK_COMB (@lem1734970) (@lem1734969 x y)). Qed.
Lemma lem1734972 (x : real) (y : real) : (term80 x y) = term121.
Proof. exact (MK_COMB (@lem1734971 x y) (@lem1734965 x y)). Qed.
Lemma lem1734973 (x : real) (y : real) : (term69 x y) = term121.
Proof. exact (TRANS (@lem1734876 x y) (@lem1734972 x y)). Qed.
Lemma lem1734974 (x : real) : (term71 x) = term122.
Proof. exact (fun_ext (fun y : real => @lem1734973 x y)). Qed.
Lemma lem1734975 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734976 (x : real) : (term72 x) = term123.
Proof. exact (MK_COMB (@lem1734975) (@lem1734974 x)). Qed.
Lemma lem1734977 : term78 = term124.
Proof. exact (fun_ext (fun x : real => @lem1734976 x)). Qed.
Lemma lem1734978 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734979 : term79 = term125.
Proof. exact (MK_COMB (@lem1734978) (@lem1734977)). Qed.
Lemma lem1734980 : term73 = term125.
Proof. exact (TRANS (@lem1734875) (@lem1734979)). Qed.
Lemma lem1734982 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1734983 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1734982 real t). Qed.
Lemma lem1734984 : term125 = term123.
Proof. exact (@lem1734983 term123). Qed.
Lemma lem1734986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1734987 (P : real -> Prop) (Q : real -> Prop) : (term130 P Q) = (term131 P Q).
Proof. exact (@lem1734986 real P Q). Qed.
Lemma lem1734988 : term132 = term133.
Proof. exact (@lem1734987 term134 term134). Qed.
Lemma lem1734989 (y : real) : (term135 y) = term116.
Proof. exact (eq_refl (term135 y)). Qed.
Lemma lem1734990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734991 (y : real) : (term136 y) = term120.
Proof. exact (MK_COMB (@lem1734990) (@lem1734989 y)). Qed.
Lemma lem1734992 (y : real) : (term135 y) = term116.
Proof. exact (eq_refl (term135 y)). Qed.
Lemma lem1734993 (y : real) : (term137 y) = term121.
Proof. exact (MK_COMB (@lem1734991 y) (@lem1734992 y)). Qed.
Lemma lem1734994 : term138 = term122.
Proof. exact (fun_ext (fun y : real => @lem1734993 y)). Qed.
Lemma lem1734995 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734996 : term132 = term123.
Proof. exact (MK_COMB (@lem1734995) (@lem1734994)). Qed.
Lemma lem1734997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1734998 : term139 = term140.
Proof. exact (MK_COMB (@lem1734997) (@lem1734996)). Qed.
Lemma lem1734999 (y : real) : (term135 y) = term116.
Proof. exact (eq_refl (term135 y)). Qed.
Lemma lem1735000 : term141 = term134.
Proof. exact (fun_ext (fun y : real => @lem1734999 y)). Qed.
Lemma lem1735001 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735002 : term142 = term143.
Proof. exact (MK_COMB (@lem1735001) (@lem1735000)). Qed.
Lemma lem1735003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735004 : term144 = term145.
Proof. exact (MK_COMB (@lem1735003) (@lem1735002)). Qed.
Lemma lem1735005 (y : real) : (term135 y) = term116.
Proof. exact (eq_refl (term135 y)). Qed.
Lemma lem1735006 : term141 = term134.
Proof. exact (fun_ext (fun y : real => @lem1735005 y)). Qed.
Lemma lem1735007 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735008 : term142 = term143.
Proof. exact (MK_COMB (@lem1735007) (@lem1735006)). Qed.
Lemma lem1735009 : term133 = term146.
Proof. exact (MK_COMB (@lem1735004) (@lem1735008)). Qed.
Lemma lem1735010 : (term132 = term133) = (term123 = term146).
Proof. exact (MK_COMB (@lem1734998) (@lem1735009)). Qed.
Lemma lem1735011 : term123 = term146.
Proof. exact (EQ_MP (@lem1735010) (@lem1734988)). Qed.
Lemma lem1735012 : term125 = term146.
Proof. exact (TRANS (@lem1734984) (@lem1735011)). Qed.
Lemma lem1735014 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1735015 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1735014 real t). Qed.
Lemma lem1735016 : term143 = term116.
Proof. exact (@lem1735015 term116). Qed.
Lemma lem1735017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735018 : term145 = term120.
Proof. exact (MK_COMB (@lem1735017) (@lem1735016)). Qed.
Lemma lem1735020 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1735021 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1735020 real t). Qed.
Lemma lem1735022 : term143 = term116.
Proof. exact (@lem1735021 term116). Qed.
Lemma lem1735023 : term146 = term121.
Proof. exact (MK_COMB (@lem1735018) (@lem1735022)). Qed.
Lemma lem1735026 : term125 = term121.
Proof. exact (TRANS (@lem1735012) (@lem1735023)). Qed.
Lemma lem1735035 : term73 = term121.
Proof. exact (TRANS (@lem1734980) (@lem1735026)). Qed.
Lemma lem1735045 (h1 : term121) : term121.
Proof. exact (h1). Qed.
Lemma lem1735046 (h1 : term116) : term116.
Proof. exact (h1). Qed.
Lemma lem1735048 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1735049 : term116 = term148.
Proof. exact (@lem1735048 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1735050 : term148 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1735051 : term116 = False.
Proof. exact (TRANS (@lem1735049) (@lem1735050)). Qed.
Lemma lem1735052 (h1 : term116) : False.
Proof. exact (EQ_MP (@lem1735051) (@lem1735046 h1)). Qed.
Lemma lem1735053 (h1 : term116) : term116.
Proof. exact (h1). Qed.
Lemma lem1735055 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1735056 : term116 = term148.
Proof. exact (@lem1735055 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1735057 : term148 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1735058 : term116 = False.
Proof. exact (TRANS (@lem1735056) (@lem1735057)). Qed.
Lemma lem1735059 (h1 : term116) : False.
Proof. exact (EQ_MP (@lem1735058) (@lem1735053 h1)). Qed.
Lemma lem1735060 (h1 : term121) : False.
Proof. exact (or_elim (@lem1735045 h1) (fun h0 : term116 => @lem1735052 h0) (fun h0 : term116 => @lem1735059 h0)). Qed.
Lemma lem1735062 (h1 : term121) : term121.
Proof. exact (h1). Qed.
Lemma lem1735063 (h1 : term121) : term121 = False.
Proof. exact (prop_ext (fun h2 : term121 => @lem1735060 h1) (fun h2 : False => @lem1735062 h1)). Qed.
Lemma lem1735064 (h1 : term121) : False.
Proof. exact (EQ_MP (@lem1735063 h1) (@lem1735062 h1)). Qed.
Lemma lem1735065 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1735066 (h1 : term73) : term121.
Proof. exact (EQ_MP (@lem1735035) (@lem1735065 h1)). Qed.
Lemma lem1735067 (h1 : term73) : term121 = False.
Proof. exact (prop_ext (fun h2 : term121 => @lem1735064 h2) (fun h2 : False => @lem1735066 h1)). Qed.
Lemma lem1735068 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1735067 h1) (@lem1735066 h1)). Qed.
Lemma lem1735069 : term149.
Proof. exact (fun h0 : term73 => @lem1735068 h0). Qed.
Lemma lem1735070 : term150.
Proof. exact (@lem1386578 term62). Qed.
Lemma lem1735071 : term62.
Proof. exact (@lem1735070 (@lem1735069)). Qed.
Lemma lem1735072 : term35.
Proof. exact (EQ_MP (@lem1734832) (@lem1735071)). Qed.
Lemma lem1735073 : term34.
Proof. exact (EQ_MP (@lem1734753) (@lem1735072)). Qed.
