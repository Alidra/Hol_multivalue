Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_GT0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1496753 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1496754 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1496755 : term6 = term7.
Proof. exact (@lem1496754 term8). Qed.
Lemma lem1496756 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1496757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1496758 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1496757) (@lem1496756 x)). Qed.
Lemma lem1496759 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1496758 x) (@lem1496753 x)). Qed.
Lemma lem1496760 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1496759 x)). Qed.
Lemma lem1496761 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496762 : term7 = term13.
Proof. exact (MK_COMB (@lem1496761) (@lem1496760)). Qed.
Lemma lem1496764 : term6 = term13.
Proof. exact (TRANS (@lem1496755) (@lem1496762)). Qed.
Lemma lem1496781 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1496782 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1496781 x)). Qed.
Lemma lem1496783 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496784 : term13 = term13.
Proof. exact (MK_COMB (@lem1496783) (@lem1496782)). Qed.
Lemma lem1496785 : term6 = term13.
Proof. exact (TRANS (@lem1496764) (@lem1496784)). Qed.
Lemma lem1496786 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483521 (real_neg x) term15). Qed.
Lemma lem1496787 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496794 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1496795 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1496796 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1496795) (@lem1496794 x)). Qed.
Lemma lem1496797 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1496796 x) (@lem1496787)). Qed.
Lemma lem1496798 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483519 (term16 x) term15). Qed.
Lemma lem1496800 (x : nat) : (term22 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1496801 : term23 = term15.
Proof. exact (@lem1496800 term24). Qed.
Lemma lem1496802 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1496803 (x : real) : (term21 x) = (term26 x).
Proof. exact (MK_COMB (@lem1496802 x) (@lem1496801)). Qed.
Lemma lem1496804 (x : real) : (term26 x) = (term16 x).
Proof. exact (@lem1483450 (term16 x)). Qed.
Lemma lem1496805 (x : real) : (term21 x) = (term16 x).
Proof. exact (TRANS (@lem1496803 x) (@lem1496804 x)). Qed.
Lemma lem1496806 (x : real) : (term20 x) = (term16 x).
Proof. exact (TRANS (@lem1496798 x) (@lem1496805 x)). Qed.
Lemma lem1496807 (x : real) : (term19 x) = (term16 x).
Proof. exact (TRANS (@lem1496797 x) (@lem1496806 x)). Qed.
Lemma lem1496808 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496809 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1496808) (@lem1496807 x)). Qed.
Lemma lem1496810 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496811 (x : real) : (term14 x) = (term29 x).
Proof. exact (MK_COMB (@lem1496809 x) (@lem1496810)). Qed.
Lemma lem1496812 (x : real) : (term2 x) = (term29 x).
Proof. exact (TRANS (@lem1496786 x) (@lem1496811 x)). Qed.
Lemma lem1496813 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1483531 x term15). Qed.
Lemma lem1496819 (x : real) : (term32 x) = (term33 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1496821 (x : nat) : (term22 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1496822 : term23 = term15.
Proof. exact (@lem1496821 term24). Qed.
Lemma lem1496823 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1496824 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1496823 x) (@lem1496822)). Qed.
Lemma lem1496825 (x : real) : (term34 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1496826 (x : real) : (term33 x) = x.
Proof. exact (TRANS (@lem1496824 x) (@lem1496825 x)). Qed.
Lemma lem1496828 (x : real) : (term32 x) = x.
Proof. exact (TRANS (@lem1496819 x) (@lem1496826 x)). Qed.
Lemma lem1496829 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496830 (x : real) : (term35 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1496829) (@lem1496828 x)). Qed.
Lemma lem1496831 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496832 (x : real) : (term31 x) = (term36 x).
Proof. exact (MK_COMB (@lem1496830 x) (@lem1496831)). Qed.
Lemma lem1496833 (x : real) : (term30 x) = (term36 x).
Proof. exact (TRANS (@lem1496813 x) (@lem1496832 x)). Qed.
Lemma lem1496834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1496835 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496834) (@lem1496812 x)). Qed.
Lemma lem1496836 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1496835 x) (@lem1496833 x)). Qed.
Lemma lem1496837 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483531 term15 (real_neg x)). Qed.
Lemma lem1496844 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1496847 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1496848 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1496847) (@lem1496844 x)). Qed.
Lemma lem1496849 (x : real) : (term45 x) = (term46 x).
Proof. exact (@lem1483519 term15 (term16 x)). Qed.
Lemma lem1496850 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1483476 term49 term49 x). Qed.
Lemma lem1496852 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1496853 : term52 = term53.
Proof. exact (@lem1496852 term24 term24). Qed.
Lemma lem1496854 : (term54 = (BIT1 0)) = (term55 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1496855 : term55 = term24.
Proof. exact (EQ_MP (@lem1496854) (@lem940073)). Qed.
Lemma lem1496856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1496857 : term53 = term56.
Proof. exact (MK_COMB (@lem1496856) (@lem1496855)). Qed.
Lemma lem1496858 : term52 = term56.
Proof. exact (TRANS (@lem1496853) (@lem1496857)). Qed.
Lemma lem1496859 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496860 : term57 = term58.
Proof. exact (MK_COMB (@lem1496859) (@lem1496858)). Qed.
Lemma lem1496861 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1496862 (x : real) : (term48 x) = (term59 x).
Proof. exact (MK_COMB (@lem1496860) (@lem1496861 x)). Qed.
Lemma lem1496863 (x : real) : (term47 x) = (term59 x).
Proof. exact (TRANS (@lem1496850 x) (@lem1496862 x)). Qed.
Lemma lem1496864 (x : real) : (term59 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1496865 (x : real) : (term47 x) = x.
Proof. exact (TRANS (@lem1496863 x) (@lem1496864 x)). Qed.
Lemma lem1496866 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1496867 (x : real) : (term46 x) = (term61 x).
Proof. exact (MK_COMB (@lem1496866) (@lem1496865 x)). Qed.
Lemma lem1496868 (x : real) : (term61 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1496869 (x : real) : (term46 x) = x.
Proof. exact (TRANS (@lem1496867 x) (@lem1496868 x)). Qed.
Lemma lem1496870 (x : real) : (term45 x) = x.
Proof. exact (TRANS (@lem1496849 x) (@lem1496869 x)). Qed.
Lemma lem1496871 (x : real) : (term44 x) = x.
Proof. exact (TRANS (@lem1496848 x) (@lem1496870 x)). Qed.
Lemma lem1496872 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496873 (x : real) : (term62 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1496872) (@lem1496871 x)). Qed.
Lemma lem1496874 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496875 (x : real) : (term42 x) = (term36 x).
Proof. exact (MK_COMB (@lem1496873 x) (@lem1496874)). Qed.
Lemma lem1496876 (x : real) : (term41 x) = (term36 x).
Proof. exact (TRANS (@lem1496837 x) (@lem1496875 x)). Qed.
Lemma lem1496877 (x : real) : (term3 x) = (term63 x).
Proof. exact (@lem1483521 term15 x). Qed.
Lemma lem1496883 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1496888 (x : real) : (term65 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1496890 (x : real) : (term64 x) = (term16 x).
Proof. exact (TRANS (@lem1496883 x) (@lem1496888 x)). Qed.
Lemma lem1496891 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496892 (x : real) : (term66 x) = (term28 x).
Proof. exact (MK_COMB (@lem1496891) (@lem1496890 x)). Qed.
Lemma lem1496893 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496894 (x : real) : (term63 x) = (term29 x).
Proof. exact (MK_COMB (@lem1496892 x) (@lem1496893)). Qed.
Lemma lem1496895 (x : real) : (term3 x) = (term29 x).
Proof. exact (TRANS (@lem1496877 x) (@lem1496894 x)). Qed.
Lemma lem1496896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1496897 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1496896) (@lem1496876 x)). Qed.
Lemma lem1496898 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1496897 x) (@lem1496895 x)). Qed.
Lemma lem1496899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496900 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496899) (@lem1496836 x)). Qed.
Lemma lem1496901 (x : real) : (term1 x) = (term73 x).
Proof. exact (MK_COMB (@lem1496900 x) (@lem1496898 x)). Qed.
Lemma lem1496902 : term12 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496901 x)). Qed.
Lemma lem1496903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496904 : term13 = term75.
Proof. exact (MK_COMB (@lem1496903) (@lem1496902)). Qed.
Lemma lem1496905 : term6 = term75.
Proof. exact (TRANS (@lem1496785) (@lem1496904)). Qed.
Lemma lem1496907 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1496908 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1496907 real P Q). Qed.
Lemma lem1496909 : term80 = term81.
Proof. exact (@lem1496908 term82 term83). Qed.
Lemma lem1496910 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496912 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496911) (@lem1496910 x)). Qed.
Lemma lem1496913 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496914 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1496912 x) (@lem1496913 x)). Qed.
Lemma lem1496915 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496914 x)). Qed.
Lemma lem1496916 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496917 : term80 = term75.
Proof. exact (MK_COMB (@lem1496916) (@lem1496915)). Qed.
Lemma lem1496918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1496919 : term89 = term90.
Proof. exact (MK_COMB (@lem1496918) (@lem1496917)). Qed.
Lemma lem1496920 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496921 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1496920 x)). Qed.
Lemma lem1496922 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496923 : term92 = term93.
Proof. exact (MK_COMB (@lem1496922) (@lem1496921)). Qed.
Lemma lem1496924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496925 : term94 = term95.
Proof. exact (MK_COMB (@lem1496924) (@lem1496923)). Qed.
Lemma lem1496926 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496927 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1496926 x)). Qed.
Lemma lem1496928 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496929 : term97 = term98.
Proof. exact (MK_COMB (@lem1496928) (@lem1496927)). Qed.
Lemma lem1496930 : term81 = term99.
Proof. exact (MK_COMB (@lem1496925) (@lem1496929)). Qed.
Lemma lem1496931 : (term80 = term81) = (term75 = term99).
Proof. exact (MK_COMB (@lem1496919) (@lem1496930)). Qed.
Lemma lem1496932 : term75 = term99.
Proof. exact (EQ_MP (@lem1496931) (@lem1496909)). Qed.
Lemma lem1497030 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1497031 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1497030 real P Q). Qed.
Lemma lem1497032 : term81 = term80.
Proof. exact (@lem1497031 term82 term83). Qed.
Lemma lem1497033 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497034 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1497033 x)). Qed.
Lemma lem1497035 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497036 : term92 = term93.
Proof. exact (MK_COMB (@lem1497035) (@lem1497034)). Qed.
Lemma lem1497037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497038 : term94 = term95.
Proof. exact (MK_COMB (@lem1497037) (@lem1497036)). Qed.
Lemma lem1497039 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497040 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1497039 x)). Qed.
Lemma lem1497041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497042 : term97 = term98.
Proof. exact (MK_COMB (@lem1497041) (@lem1497040)). Qed.
Lemma lem1497043 : term81 = term99.
Proof. exact (MK_COMB (@lem1497038) (@lem1497042)). Qed.
Lemma lem1497044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1497045 : term100 = term101.
Proof. exact (MK_COMB (@lem1497044) (@lem1497043)). Qed.
Lemma lem1497046 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497048 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497047) (@lem1497046 x)). Qed.
Lemma lem1497049 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497050 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497048 x) (@lem1497049 x)). Qed.
Lemma lem1497051 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497050 x)). Qed.
Lemma lem1497052 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497053 : term80 = term75.
Proof. exact (MK_COMB (@lem1497052) (@lem1497051)). Qed.
Lemma lem1497054 : (term81 = term80) = (term99 = term75).
Proof. exact (MK_COMB (@lem1497045) (@lem1497053)). Qed.
Lemma lem1497055 : term99 = term75.
Proof. exact (EQ_MP (@lem1497054) (@lem1497032)). Qed.
Lemma lem1497056 : term75 = term75.
Proof. exact (TRANS (@lem1496932) (@lem1497055)). Qed.
Lemma lem1497059 : term6 = term75.
Proof. exact (TRANS (@lem1496905) (@lem1497056)). Qed.
Lemma lem1497076 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1497077 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497076 x)). Qed.
Lemma lem1497078 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497079 : term75 = term75.
Proof. exact (MK_COMB (@lem1497078) (@lem1497077)). Qed.
Lemma lem1497080 : term6 = term75.
Proof. exact (TRANS (@lem1497059) (@lem1497079)). Qed.
Lemma lem1497090 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1497091 (x : real) (h1 : term40 x) : term40 x.
Proof. exact (h1). Qed.
Lemma lem1497092 (x : real) (h1 : term40 x) : term36 x.
Proof. exact (proj2 (@lem1497091 x h1)). Qed.
Lemma lem1497093 (x : real) (h1 : term40 x) : term29 x.
Proof. exact (proj1 (@lem1497091 x h1)). Qed.
Lemma lem1497095 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497096 : term103 = term104.
Proof. exact (@lem1497095 (NUMERAL 0) term24). Qed.
Lemma lem1497097 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497098 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497099 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497098 h1) (fun h1 : term104 = True => @lem1497097)). Qed.
Lemma lem1497100 : term104 = True.
Proof. exact (EQ_MP (@lem1497099) (@lem1497097)). Qed.
Lemma lem1497101 : term103 = True.
Proof. exact (TRANS (@lem1497096) (@lem1497100)). Qed.
Lemma lem1497102 : True = term103.
Proof. exact (SYM (@lem1497101)). Qed.
Lemma lem1497103 : term103.
Proof. exact (EQ_MP (@lem1497102) (@lem0)). Qed.
Lemma lem1497104 (x : real) (h1 : term40 x) : term106 x.
Proof. exact (conj (@lem1497103) (@lem1497092 x h1)). Qed.
Lemma lem1497106 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1497107 (x : real) : term108 x.
Proof. exact (@lem1497106 term56 x). Qed.
Lemma lem1497108 (x : real) (h1 : term40 x) : term109 x.
Proof. exact (@lem1497107 x (@lem1497104 x h1)). Qed.
Lemma lem1497109 (x : real) : (term59 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1497110 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497111 (x : real) : (term110 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497110) (@lem1497109 x)). Qed.
Lemma lem1497112 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497113 (x : real) : (term109 x) = (term36 x).
Proof. exact (MK_COMB (@lem1497111 x) (@lem1497112)). Qed.
Lemma lem1497114 (x : real) (h1 : term40 x) : term36 x.
Proof. exact (EQ_MP (@lem1497113 x) (@lem1497108 x h1)). Qed.
Lemma lem1497116 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497117 : term103 = term104.
Proof. exact (@lem1497116 (NUMERAL 0) term24). Qed.
Lemma lem1497118 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497119 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497120 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497119 h1) (fun h1 : term104 = True => @lem1497118)). Qed.
Lemma lem1497121 : term104 = True.
Proof. exact (EQ_MP (@lem1497120) (@lem1497118)). Qed.
Lemma lem1497122 : term103 = True.
Proof. exact (TRANS (@lem1497117) (@lem1497121)). Qed.
Lemma lem1497123 : True = term103.
Proof. exact (SYM (@lem1497122)). Qed.
Lemma lem1497124 : term103.
Proof. exact (EQ_MP (@lem1497123) (@lem0)). Qed.
Lemma lem1497125 (x : real) (h1 : term40 x) : term111 x.
Proof. exact (conj (@lem1497124) (@lem1497093 x h1)). Qed.
Lemma lem1497127 (x : real) (y : real) : term112 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1497128 (x : real) : term113 x.
Proof. exact (@lem1497127 term56 (term16 x)). Qed.
Lemma lem1497129 (x : real) (h1 : term40 x) : term114 x.
Proof. exact (@lem1497128 x (@lem1497125 x h1)). Qed.
Lemma lem1497130 (x : real) : (term115 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1497131 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497132 (x : real) : (term116 x) = (term28 x).
Proof. exact (MK_COMB (@lem1497131) (@lem1497130 x)). Qed.
Lemma lem1497133 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497134 (x : real) : (term114 x) = (term29 x).
Proof. exact (MK_COMB (@lem1497132 x) (@lem1497133)). Qed.
Lemma lem1497135 (x : real) (h1 : term40 x) : term29 x.
Proof. exact (EQ_MP (@lem1497134 x) (@lem1497129 x h1)). Qed.
Lemma lem1497136 (x : real) (h1 : term40 x) : term40 x.
Proof. exact (conj (@lem1497135 x h1) (@lem1497114 x h1)). Qed.
Lemma lem1497138 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1497139 (x : real) : term118 x.
Proof. exact (@lem1497138 (term16 x) x). Qed.
Lemma lem1497140 (x : real) (h1 : term40 x) : term119 x.
Proof. exact (@lem1497139 x (@lem1497136 x h1)). Qed.
Lemma lem1497141 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483440 term49 x). Qed.
Lemma lem1497143 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1497144 : term123 = term15.
Proof. exact (@lem1497143 term24). Qed.
Lemma lem1497145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497146 : term124 = term125.
Proof. exact (MK_COMB (@lem1497145) (@lem1497144)). Qed.
Lemma lem1497147 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497148 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1497146) (@lem1497147 x)). Qed.
Lemma lem1497149 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1497141 x) (@lem1497148 x)). Qed.
Lemma lem1497150 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1497151 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1497149 x) (@lem1497150 x)). Qed.
Lemma lem1497152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497153 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1497152) (@lem1497151 x)). Qed.
Lemma lem1497154 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497155 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1497153 x) (@lem1497154)). Qed.
Lemma lem1497156 (x : real) (h1 : term40 x) : term129.
Proof. exact (EQ_MP (@lem1497155 x) (@lem1497140 x h1)). Qed.
Lemma lem1497158 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497159 : term129 = term130.
Proof. exact (@lem1497158 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1497160 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1497161 : term129 = False.
Proof. exact (TRANS (@lem1497159) (@lem1497160)). Qed.
Lemma lem1497162 (x : real) (h1 : term40 x) : False.
Proof. exact (EQ_MP (@lem1497161) (@lem1497156 x h1)). Qed.
Lemma lem1497163 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1497164 (x : real) (h1 : term70 x) : term29 x.
Proof. exact (proj2 (@lem1497163 x h1)). Qed.
Lemma lem1497165 (x : real) (h1 : term70 x) : term36 x.
Proof. exact (proj1 (@lem1497163 x h1)). Qed.
Lemma lem1497167 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497168 : term103 = term104.
Proof. exact (@lem1497167 (NUMERAL 0) term24). Qed.
Lemma lem1497169 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497170 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497171 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497170 h1) (fun h1 : term104 = True => @lem1497169)). Qed.
Lemma lem1497172 : term104 = True.
Proof. exact (EQ_MP (@lem1497171) (@lem1497169)). Qed.
Lemma lem1497173 : term103 = True.
Proof. exact (TRANS (@lem1497168) (@lem1497172)). Qed.
Lemma lem1497174 : True = term103.
Proof. exact (SYM (@lem1497173)). Qed.
Lemma lem1497175 : term103.
Proof. exact (EQ_MP (@lem1497174) (@lem0)). Qed.
Lemma lem1497176 (x : real) (h1 : term70 x) : term106 x.
Proof. exact (conj (@lem1497175) (@lem1497165 x h1)). Qed.
Lemma lem1497178 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1497179 (x : real) : term108 x.
Proof. exact (@lem1497178 term56 x). Qed.
Lemma lem1497180 (x : real) (h1 : term70 x) : term109 x.
Proof. exact (@lem1497179 x (@lem1497176 x h1)). Qed.
Lemma lem1497181 (x : real) : (term59 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1497182 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497183 (x : real) : (term110 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497182) (@lem1497181 x)). Qed.
Lemma lem1497184 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497185 (x : real) : (term109 x) = (term36 x).
Proof. exact (MK_COMB (@lem1497183 x) (@lem1497184)). Qed.
Lemma lem1497186 (x : real) (h1 : term70 x) : term36 x.
Proof. exact (EQ_MP (@lem1497185 x) (@lem1497180 x h1)). Qed.
Lemma lem1497188 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497189 : term103 = term104.
Proof. exact (@lem1497188 (NUMERAL 0) term24). Qed.
Lemma lem1497190 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497191 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497192 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497191 h1) (fun h1 : term104 = True => @lem1497190)). Qed.
Lemma lem1497193 : term104 = True.
Proof. exact (EQ_MP (@lem1497192) (@lem1497190)). Qed.
Lemma lem1497194 : term103 = True.
Proof. exact (TRANS (@lem1497189) (@lem1497193)). Qed.
Lemma lem1497195 : True = term103.
Proof. exact (SYM (@lem1497194)). Qed.
Lemma lem1497196 : term103.
Proof. exact (EQ_MP (@lem1497195) (@lem0)). Qed.
Lemma lem1497197 (x : real) (h1 : term70 x) : term111 x.
Proof. exact (conj (@lem1497196) (@lem1497164 x h1)). Qed.
Lemma lem1497199 (x : real) (y : real) : term112 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1497200 (x : real) : term113 x.
Proof. exact (@lem1497199 term56 (term16 x)). Qed.
Lemma lem1497201 (x : real) (h1 : term70 x) : term114 x.
Proof. exact (@lem1497200 x (@lem1497197 x h1)). Qed.
Lemma lem1497202 (x : real) : (term115 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1497203 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497204 (x : real) : (term116 x) = (term28 x).
Proof. exact (MK_COMB (@lem1497203) (@lem1497202 x)). Qed.
Lemma lem1497205 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497206 (x : real) : (term114 x) = (term29 x).
Proof. exact (MK_COMB (@lem1497204 x) (@lem1497205)). Qed.
Lemma lem1497207 (x : real) (h1 : term70 x) : term29 x.
Proof. exact (EQ_MP (@lem1497206 x) (@lem1497201 x h1)). Qed.
Lemma lem1497208 (x : real) (h1 : term70 x) : term40 x.
Proof. exact (conj (@lem1497207 x h1) (@lem1497186 x h1)). Qed.
Lemma lem1497210 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1497211 (x : real) : term118 x.
Proof. exact (@lem1497210 (term16 x) x). Qed.
Lemma lem1497212 (x : real) (h1 : term70 x) : term119 x.
Proof. exact (@lem1497211 x (@lem1497208 x h1)). Qed.
Lemma lem1497213 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483440 term49 x). Qed.
Lemma lem1497215 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1497216 : term123 = term15.
Proof. exact (@lem1497215 term24). Qed.
Lemma lem1497217 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497218 : term124 = term125.
Proof. exact (MK_COMB (@lem1497217) (@lem1497216)). Qed.
Lemma lem1497219 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497220 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1497218) (@lem1497219 x)). Qed.
Lemma lem1497221 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1497213 x) (@lem1497220 x)). Qed.
Lemma lem1497222 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1497223 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1497221 x) (@lem1497222 x)). Qed.
Lemma lem1497224 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497225 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1497224) (@lem1497223 x)). Qed.
Lemma lem1497226 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497227 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1497225 x) (@lem1497226)). Qed.
Lemma lem1497228 (x : real) (h1 : term70 x) : term129.
Proof. exact (EQ_MP (@lem1497227 x) (@lem1497212 x h1)). Qed.
Lemma lem1497230 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497231 : term129 = term130.
Proof. exact (@lem1497230 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1497232 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1497233 : term129 = False.
Proof. exact (TRANS (@lem1497231) (@lem1497232)). Qed.
Lemma lem1497234 (x : real) (h1 : term70 x) : False.
Proof. exact (EQ_MP (@lem1497233) (@lem1497228 x h1)). Qed.
Lemma lem1497235 (x : real) (h1 : term73 x) : False.
Proof. exact (or_elim (@lem1497090 x h1) (fun h0 : term40 x => @lem1497162 x h0) (fun h0 : term70 x => @lem1497234 x h0)). Qed.
Lemma lem1497237 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1497238 (x : real) (h1 : term73 x) : (term73 x) = False.
Proof. exact (prop_ext (fun h2 : term73 x => @lem1497235 x h1) (fun h2 : False => @lem1497237 x h1)). Qed.
Lemma lem1497239 (x : real) (h1 : term73 x) : False.
Proof. exact (EQ_MP (@lem1497238 x h1) (@lem1497237 x h1)). Qed.
Lemma lem1497240 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1497241 (h1 : term75) : False.
Proof. exact (ex_elim (@lem1497240 h1) (fun x : real => fun h0 : term74 x => @lem1497239 x h0)). Qed.
Lemma lem1497242 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1497243 (h1 : term6) : term75.
Proof. exact (EQ_MP (@lem1497080) (@lem1497242 h1)). Qed.
Lemma lem1497244 (h1 : term6) : term75 = False.
Proof. exact (prop_ext (fun h2 : term75 => @lem1497241 h2) (fun h2 : False => @lem1497243 h1)). Qed.
Lemma lem1497245 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1497244 h1) (@lem1497243 h1)). Qed.
Lemma lem1497246 : term131.
Proof. exact (fun h0 : term6 => @lem1497245 h0). Qed.
Lemma lem1497247 : term132.
Proof. exact (@lem1386578 term133). Qed.
Lemma lem1497248 : term133.
Proof. exact (@lem1497247 (@lem1497246)). Qed.
