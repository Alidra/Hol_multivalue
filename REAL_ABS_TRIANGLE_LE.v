Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_TRIANGLE_LE_term_abbrevs.
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
Require Import thm1482681_spec.
Require Import thm1482682_spec.
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
Require Import thm1483480_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1529670 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17362 (term2 y x z) (term3 y z)). Qed.
Lemma lem1529671 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1529672 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1529671 (term8 x y)). Qed.
Lemma lem1529673 (x : real) (y : real) (z : real) : (term9 x y z) = (term10 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1529674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1529675 (x : real) (y : real) (z : real) : (term11 x y z) = (term0 x y z).
Proof. exact (MK_COMB (@lem1529674) (@lem1529673 x y z)). Qed.
Lemma lem1529676 (x : real) (y : real) (z : real) : (term11 x y z) = (term1 x y z).
Proof. exact (TRANS (@lem1529675 x y z) (@lem1529670 x y z)). Qed.
Lemma lem1529677 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (fun_ext (fun z : real => @lem1529676 x y z)). Qed.
Lemma lem1529678 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529679 (x : real) (y : real) : (term7 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1529678) (@lem1529677 x y)). Qed.
Lemma lem1529680 (x : real) (y : real) : (term6 x y) = (term14 x y).
Proof. exact (TRANS (@lem1529672 x y) (@lem1529679 x y)). Qed.
Lemma lem1529681 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1529682 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1529681 (term17 x)). Qed.
Lemma lem1529683 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1529684 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1529685 (x : real) (y : real) : (term20 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1529684) (@lem1529683 x y)). Qed.
Lemma lem1529686 (x : real) (y : real) : (term20 x y) = (term14 x y).
Proof. exact (TRANS (@lem1529685 x y) (@lem1529680 x y)). Qed.
Lemma lem1529687 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1529686 x y)). Qed.
Lemma lem1529688 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529689 (x : real) : (term16 x) = (term23 x).
Proof. exact (MK_COMB (@lem1529688) (@lem1529687 x)). Qed.
Lemma lem1529690 (x : real) : (term15 x) = (term23 x).
Proof. exact (TRANS (@lem1529682 x) (@lem1529689 x)). Qed.
Lemma lem1529691 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1529692 : term24 = term25.
Proof. exact (@lem1529691 term26). Qed.
Lemma lem1529693 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1529694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1529695 (x : real) : (term29 x) = (term15 x).
Proof. exact (MK_COMB (@lem1529694) (@lem1529693 x)). Qed.
Lemma lem1529696 (x : real) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem1529695 x) (@lem1529690 x)). Qed.
Lemma lem1529697 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1529696 x)). Qed.
Lemma lem1529698 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529699 : term25 = term32.
Proof. exact (MK_COMB (@lem1529698) (@lem1529697)). Qed.
Lemma lem1529701 : term24 = term32.
Proof. exact (TRANS (@lem1529692) (@lem1529699)). Qed.
Lemma lem1529708 (x : real) (y : real) (z : real) : (term1 x y z) = (term1 x y z).
Proof. exact (eq_refl (term1 x y z)). Qed.
Lemma lem1529709 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (fun_ext (fun z : real => @lem1529708 x y z)). Qed.
Lemma lem1529710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529711 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1529710) (@lem1529709 x y)). Qed.
Lemma lem1529712 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1529711 x y)). Qed.
Lemma lem1529713 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529714 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1529713) (@lem1529712 x)). Qed.
Lemma lem1529715 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1529714 x)). Qed.
Lemma lem1529716 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529717 : term32 = term32.
Proof. exact (MK_COMB (@lem1529716) (@lem1529715)). Qed.
Lemma lem1529718 : term24 = term32.
Proof. exact (TRANS (@lem1529701) (@lem1529717)). Qed.
Lemma lem1529719 (z : real) (y : real) (x : real) : (term2 y x z) = (term33 z y x).
Proof. exact (@lem1483523 z (term34 y x)). Qed.
Lemma lem1529731 (z : real) (y : real) (x : real) : (term35 z y x) = (term36 z y x).
Proof. exact (@lem1483519 z (term34 y x)). Qed.
Lemma lem1529738 (y : real) (x : real) : (term37 y x) = (term38 y x).
Proof. exact (@lem1483508 (real_abs x) term39 (term40 y x)). Qed.
Lemma lem1529739 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1529742 (z : real) (y : real) (x : real) : (term36 z y x) = (term41 z y x).
Proof. exact (MK_COMB (@lem1529739 z) (@lem1529738 y x)). Qed.
Lemma lem1529744 (z : real) (y : real) (x : real) : (term35 z y x) = (term41 z y x).
Proof. exact (TRANS (@lem1529731 z y x) (@lem1529742 z y x)). Qed.
Lemma lem1529745 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1529746 (z : real) (y : real) (x : real) : (term42 z y x) = (term43 z y x).
Proof. exact (MK_COMB (@lem1529745) (@lem1529744 z y x)). Qed.
Lemma lem1529747 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1529748 (z : real) (y : real) (x : real) : (term33 z y x) = (term45 z y x).
Proof. exact (MK_COMB (@lem1529746 z y x) (@lem1529747)). Qed.
Lemma lem1529749 (z : real) (y : real) (x : real) : (term2 y x z) = (term45 z y x).
Proof. exact (TRANS (@lem1529719 z y x) (@lem1529748 z y x)). Qed.
Lemma lem1529750 (y : real) (z : real) : (term46 y z) = (term47 y z).
Proof. exact (@lem1483533 (real_abs y) z). Qed.
Lemma lem1529756 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483519 (real_abs y) z). Qed.
Lemma lem1529761 (z : real) (y : real) : (term49 y z) = (term50 z y).
Proof. exact (@lem1483488 (term51 z) (real_abs y)). Qed.
Lemma lem1529763 (z : real) (y : real) : (term48 y z) = (term50 z y).
Proof. exact (TRANS (@lem1529756 y z) (@lem1529761 z y)). Qed.
Lemma lem1529764 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529765 (z : real) (y : real) : (term52 y z) = (term53 z y).
Proof. exact (MK_COMB (@lem1529764) (@lem1529763 z y)). Qed.
Lemma lem1529766 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1529767 (z : real) (y : real) : (term47 y z) = (term54 z y).
Proof. exact (MK_COMB (@lem1529765 z y) (@lem1529766)). Qed.
Lemma lem1529768 (z : real) (y : real) : (term46 y z) = (term54 z y).
Proof. exact (TRANS (@lem1529750 y z) (@lem1529767 z y)). Qed.
Lemma lem1529769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529770 (z : real) (y : real) (x : real) : (term55 y x z) = (term56 z y x).
Proof. exact (MK_COMB (@lem1529769) (@lem1529749 z y x)). Qed.
Lemma lem1529771 (x : real) (z : real) (y : real) : (term1 x y z) = (term57 x z y).
Proof. exact (MK_COMB (@lem1529770 z y x) (@lem1529768 z y)). Qed.
Lemma lem1529772 (x : real) (y : real) : (term13 x y) = (term58 x y).
Proof. exact (fun_ext (fun z : real => @lem1529771 x z y)). Qed.
Lemma lem1529773 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529774 (x : real) (y : real) : (term14 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1529773) (@lem1529772 x y)). Qed.
Lemma lem1529775 (x : real) : (term22 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1529774 x y)). Qed.
Lemma lem1529776 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529777 (x : real) : (term23 x) = (term61 x).
Proof. exact (MK_COMB (@lem1529776) (@lem1529775 x)). Qed.
Lemma lem1529778 : term31 = term62.
Proof. exact (fun_ext (fun x : real => @lem1529777 x)). Qed.
Lemma lem1529779 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529780 : term32 = term63.
Proof. exact (MK_COMB (@lem1529779) (@lem1529778)). Qed.
Lemma lem1529843 : term24 = term63.
Proof. exact (TRANS (@lem1529718) (@lem1529780)). Qed.
Lemma lem1529850 (x : real) (z : real) (y : real) : (term57 x z y) = (term57 x z y).
Proof. exact (eq_refl (term57 x z y)). Qed.
Lemma lem1529851 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (fun_ext (fun z : real => @lem1529850 x z y)). Qed.
Lemma lem1529852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529853 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1529852) (@lem1529851 x y)). Qed.
Lemma lem1529854 (x : real) : (term60 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1529853 x y)). Qed.
Lemma lem1529855 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529856 (x : real) : (term61 x) = (term61 x).
Proof. exact (MK_COMB (@lem1529855) (@lem1529854 x)). Qed.
Lemma lem1529857 : term62 = term62.
Proof. exact (fun_ext (fun x : real => @lem1529856 x)). Qed.
Lemma lem1529858 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1529859 : term63 = term63.
Proof. exact (MK_COMB (@lem1529858) (@lem1529857)). Qed.
Lemma lem1529860 : term24 = term63.
Proof. exact (TRANS (@lem1529843) (@lem1529859)). Qed.
Lemma lem1529862 (a : real) (x : real) (b : real) (r : real) : (term64 a x b r) = (term65 a x b r).
Proof. exact (proj1 (@lem1482681 x a b (@el real) (@el real) r)). Qed.
Lemma lem1529863 (z : real) (y : real) (x : real) : (term45 z y x) = (term66 z y x).
Proof. exact (@lem1529862 z x (term67 y x) term44). Qed.
Lemma lem1529870 (y : real) (x : real) : (term67 y x) = (term67 y x).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1529877 (x : real) : (term68 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1529878 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529879 (x : real) : (term69 x) = (real_add x).
Proof. exact (MK_COMB (@lem1529878) (@lem1529877 x)). Qed.
Lemma lem1529882 (y : real) (x : real) : (term70 y x) = (term71 y x).
Proof. exact (MK_COMB (@lem1529879 x) (@lem1529870 y x)). Qed.
Lemma lem1529885 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1529886 (z : real) (y : real) (x : real) : (term72 z y x) = (term73 z y x).
Proof. exact (MK_COMB (@lem1529885 z) (@lem1529882 y x)). Qed.
Lemma lem1529891 (z : real) (y : real) (x : real) : (term73 z y x) = (term74 z y x).
Proof. exact (@lem1483484 x z (term67 y x)). Qed.
Lemma lem1529892 (z : real) (y : real) (x : real) : (term72 z y x) = (term74 z y x).
Proof. exact (TRANS (@lem1529886 z y x) (@lem1529891 z y x)). Qed.
Lemma lem1529893 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1529894 (z : real) (y : real) (x : real) : (term75 z y x) = (term76 z y x).
Proof. exact (MK_COMB (@lem1529893) (@lem1529892 z y x)). Qed.
Lemma lem1529895 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1529896 (z : real) (y : real) (x : real) : (term77 z y x) = (term78 z y x).
Proof. exact (MK_COMB (@lem1529894 z y x) (@lem1529895)). Qed.
Lemma lem1529925 (z : real) (y : real) (x : real) : (term79 z y x) = (term80 z y x).
Proof. exact (@lem1483484 (term51 x) z (term67 y x)). Qed.
Lemma lem1529926 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1529927 (z : real) (y : real) (x : real) : (term81 z y x) = (term82 z y x).
Proof. exact (MK_COMB (@lem1529926) (@lem1529925 z y x)). Qed.
Lemma lem1529928 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1529929 (z : real) (y : real) (x : real) : (term83 z y x) = (term84 z y x).
Proof. exact (MK_COMB (@lem1529927 z y x) (@lem1529928)). Qed.
Lemma lem1529930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529931 (z : real) (y : real) (x : real) : (term85 z y x) = (term86 z y x).
Proof. exact (MK_COMB (@lem1529930) (@lem1529929 z y x)). Qed.
Lemma lem1529932 (z : real) (y : real) (x : real) : (term66 z y x) = (term87 z y x).
Proof. exact (MK_COMB (@lem1529931 z y x) (@lem1529896 z y x)). Qed.
Lemma lem1529933 (z : real) (y : real) (x : real) : (term45 z y x) = (term87 z y x).
Proof. exact (TRANS (@lem1529863 z y x) (@lem1529932 z y x)). Qed.
Lemma lem1529935 (a : real) (b : real) (x : real) (r : real) : (term88 a b x r) = (term89 a b x r).
Proof. exact (proj1 (@lem1482682 x a b (@el real) (@el real) r)). Qed.
Lemma lem1529936 (z : real) (y : real) (x : real) : (term84 z y x) = (term90 z y x).
Proof. exact (@lem1529935 (term51 x) z (real_sub y x) term44). Qed.
Lemma lem1529942 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1529947 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1529949 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1529942 y x) (@lem1529947 x y)). Qed.
Lemma lem1529952 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1529953 (x : real) (y : real) : (term94 y x) = (term95 x y).
Proof. exact (MK_COMB (@lem1529952) (@lem1529949 x y)). Qed.
Lemma lem1529954 (x : real) (y : real) : (term95 x y) = (term92 x y).
Proof. exact (@lem1483460 (term92 x y)). Qed.
Lemma lem1529955 (x : real) (y : real) : (term94 y x) = (term92 x y).
Proof. exact (TRANS (@lem1529953 x y) (@lem1529954 x y)). Qed.
Lemma lem1529958 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1529959 (z : real) (x : real) (y : real) : (term96 z y x) = (term97 z x y).
Proof. exact (MK_COMB (@lem1529958 z) (@lem1529955 x y)). Qed.
Lemma lem1529960 (x : real) (z : real) (y : real) : (term97 z x y) = (term98 x z y).
Proof. exact (@lem1483484 (term51 x) z y). Qed.
Lemma lem1529961 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1529962 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1529963 (x : real) (y : real) (z : real) : (term98 x z y) = (term98 x y z).
Proof. exact (MK_COMB (@lem1529962 x) (@lem1529961 y z)). Qed.
Lemma lem1529964 (x : real) (y : real) (z : real) : (term97 z x y) = (term98 x y z).
Proof. exact (TRANS (@lem1529960 x z y) (@lem1529963 x y z)). Qed.
Lemma lem1529965 (x : real) (y : real) (z : real) : (term96 z y x) = (term98 x y z).
Proof. exact (TRANS (@lem1529959 z x y) (@lem1529964 x y z)). Qed.
Lemma lem1529974 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1529975 (x : real) (y : real) (z : real) : (term100 z y x) = (term101 x y z).
Proof. exact (MK_COMB (@lem1529974 x) (@lem1529965 x y z)). Qed.
Lemma lem1529976 (x : real) (y : real) (z : real) : (term101 x y z) = (term102 x y z).
Proof. exact (@lem1483490 (term51 x) (term51 x) (real_add y z)). Qed.
Lemma lem1529977 (x : real) : (term103 x) = (term104 x).
Proof. exact (@lem1483438 term39 term39 x). Qed.
Lemma lem1529978 : term105 = term106.
Proof. exact (@lem1367763 term107 term107). Qed.
Lemma lem1529979 : term108 = term109.
Proof. exact (@lem706885). Qed.
Lemma lem1529980 : (term108 = term109) = (term110 = term111).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term109). Qed.
Lemma lem1529981 : term110 = term111.
Proof. exact (EQ_MP (@lem1529980) (@lem1529979)). Qed.
Lemma lem1529982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529983 : term112 = term113.
Proof. exact (MK_COMB (@lem1529982) (@lem1529981)). Qed.
Lemma lem1529984 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1529985 : term106 = term114.
Proof. exact (MK_COMB (@lem1529984) (@lem1529983)). Qed.
Lemma lem1529986 : term105 = term114.
Proof. exact (TRANS (@lem1529978) (@lem1529985)). Qed.
Lemma lem1529987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529988 : term115 = term116.
Proof. exact (MK_COMB (@lem1529987) (@lem1529986)). Qed.
Lemma lem1529989 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529990 (x : real) : (term104 x) = (term117 x).
Proof. exact (MK_COMB (@lem1529988) (@lem1529989 x)). Qed.
Lemma lem1529991 (x : real) : (term103 x) = (term117 x).
Proof. exact (TRANS (@lem1529977 x) (@lem1529990 x)). Qed.
Lemma lem1529992 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529993 (x : real) : (term118 x) = (term119 x).
Proof. exact (MK_COMB (@lem1529992) (@lem1529991 x)). Qed.
Lemma lem1529994 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (eq_refl (real_add y z)). Qed.
Lemma lem1529995 (x : real) (y : real) (z : real) : (term102 x y z) = (term120 x y z).
Proof. exact (MK_COMB (@lem1529993 x) (@lem1529994 y z)). Qed.
Lemma lem1529996 (x : real) (y : real) (z : real) : (term101 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1529976 x y z) (@lem1529995 x y z)). Qed.
Lemma lem1529997 (x : real) (y : real) (z : real) : (term100 z y x) = (term120 x y z).
Proof. exact (TRANS (@lem1529975 x y z) (@lem1529996 x y z)). Qed.
Lemma lem1529998 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1529999 (x : real) (y : real) (z : real) : (term121 z y x) = (term122 x y z).
Proof. exact (MK_COMB (@lem1529998) (@lem1529997 x y z)). Qed.
Lemma lem1530000 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530001 (x : real) (y : real) (z : real) : (term123 z y x) = (term124 x y z).
Proof. exact (MK_COMB (@lem1529999 x y z) (@lem1530000)). Qed.
Lemma lem1530007 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1530012 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1530014 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1530007 y x) (@lem1530012 x y)). Qed.
Lemma lem1530017 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem1530018 (x : real) (y : real) : (term126 y x) = (term127 x y).
Proof. exact (MK_COMB (@lem1530017) (@lem1530014 x y)). Qed.
Lemma lem1530019 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (@lem1483508 (term51 x) term39 y). Qed.
Lemma lem1530020 (y : real) : (term51 y) = (term51 y).
Proof. exact (eq_refl (term51 y)). Qed.
Lemma lem1530021 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1530023 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1530024 : term133 = term134.
Proof. exact (@lem1530023 term107 term107). Qed.
Lemma lem1530025 : (term135 = (BIT1 0)) = (term136 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1530026 : term136 = term107.
Proof. exact (EQ_MP (@lem1530025) (@lem940073)). Qed.
Lemma lem1530027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1530028 : term134 = term137.
Proof. exact (MK_COMB (@lem1530027) (@lem1530026)). Qed.
Lemma lem1530029 : term133 = term137.
Proof. exact (TRANS (@lem1530024) (@lem1530028)). Qed.
Lemma lem1530030 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530031 : term138 = term93.
Proof. exact (MK_COMB (@lem1530030) (@lem1530029)). Qed.
Lemma lem1530032 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1530033 (x : real) : (term130 x) = (term68 x).
Proof. exact (MK_COMB (@lem1530031) (@lem1530032 x)). Qed.
Lemma lem1530034 (x : real) : (term129 x) = (term68 x).
Proof. exact (TRANS (@lem1530021 x) (@lem1530033 x)). Qed.
Lemma lem1530035 (x : real) : (term68 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1530036 (x : real) : (term129 x) = x.
Proof. exact (TRANS (@lem1530034 x) (@lem1530035 x)). Qed.
Lemma lem1530037 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530038 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1530037) (@lem1530036 x)). Qed.
Lemma lem1530039 (x : real) (y : real) : (term128 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1530038 x) (@lem1530020 y)). Qed.
Lemma lem1530040 (x : real) (y : real) : (term127 x y) = (term91 x y).
Proof. exact (TRANS (@lem1530019 x y) (@lem1530039 x y)). Qed.
Lemma lem1530041 (x : real) (y : real) : (term126 y x) = (term91 x y).
Proof. exact (TRANS (@lem1530018 x y) (@lem1530040 x y)). Qed.
Lemma lem1530044 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1530045 (z : real) (x : real) (y : real) : (term140 z y x) = (term141 z x y).
Proof. exact (MK_COMB (@lem1530044 z) (@lem1530041 x y)). Qed.
Lemma lem1530046 (x : real) (z : real) (y : real) : (term141 z x y) = (term141 x z y).
Proof. exact (@lem1483484 x z (term51 y)). Qed.
Lemma lem1530047 (y : real) (z : real) : (term91 z y) = (term92 y z).
Proof. exact (@lem1483488 (term51 y) z). Qed.
Lemma lem1530048 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1530049 (x : real) (y : real) (z : real) : (term141 x z y) = (term97 x y z).
Proof. exact (MK_COMB (@lem1530048 x) (@lem1530047 y z)). Qed.
Lemma lem1530050 (x : real) (y : real) (z : real) : (term141 z x y) = (term97 x y z).
Proof. exact (TRANS (@lem1530046 x z y) (@lem1530049 x y z)). Qed.
Lemma lem1530051 (x : real) (y : real) (z : real) : (term140 z y x) = (term97 x y z).
Proof. exact (TRANS (@lem1530045 z x y) (@lem1530050 x y z)). Qed.
Lemma lem1530060 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1530061 (x : real) (y : real) (z : real) : (term142 z y x) = (term143 x y z).
Proof. exact (MK_COMB (@lem1530060 x) (@lem1530051 x y z)). Qed.
Lemma lem1530062 (x : real) (y : real) (z : real) : (term143 x y z) = (term144 x y z).
Proof. exact (@lem1483490 (term51 x) x (term92 y z)). Qed.
Lemma lem1530063 (x : real) : (term145 x) = (term146 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1530065 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530066 : term148 = term44.
Proof. exact (@lem1530065 term107). Qed.
Lemma lem1530067 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530068 : term149 = term150.
Proof. exact (MK_COMB (@lem1530067) (@lem1530066)). Qed.
Lemma lem1530069 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1530070 (x : real) : (term146 x) = (term151 x).
Proof. exact (MK_COMB (@lem1530068) (@lem1530069 x)). Qed.
Lemma lem1530071 (x : real) : (term145 x) = (term151 x).
Proof. exact (TRANS (@lem1530063 x) (@lem1530070 x)). Qed.
Lemma lem1530072 (x : real) : (term151 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1530073 (x : real) : (term145 x) = term44.
Proof. exact (TRANS (@lem1530071 x) (@lem1530072 x)). Qed.
Lemma lem1530074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530075 (x : real) : (term152 x) = term153.
Proof. exact (MK_COMB (@lem1530074) (@lem1530073 x)). Qed.
Lemma lem1530076 (y : real) (z : real) : (term92 y z) = (term92 y z).
Proof. exact (eq_refl (term92 y z)). Qed.
Lemma lem1530077 (x : real) (y : real) (z : real) : (term144 x y z) = (term154 y z).
Proof. exact (MK_COMB (@lem1530075 x) (@lem1530076 y z)). Qed.
Lemma lem1530078 (x : real) (y : real) (z : real) : (term143 x y z) = (term154 y z).
Proof. exact (TRANS (@lem1530062 x y z) (@lem1530077 x y z)). Qed.
Lemma lem1530079 (y : real) (z : real) : (term154 y z) = (term92 y z).
Proof. exact (@lem1483448 (term92 y z)). Qed.
Lemma lem1530080 (x : real) (y : real) (z : real) : (term143 x y z) = (term92 y z).
Proof. exact (TRANS (@lem1530078 x y z) (@lem1530079 y z)). Qed.
Lemma lem1530081 (x : real) (y : real) (z : real) : (term142 z y x) = (term92 y z).
Proof. exact (TRANS (@lem1530061 x y z) (@lem1530080 x y z)). Qed.
Lemma lem1530082 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530083 (x : real) (y : real) (z : real) : (term155 z y x) = (term156 y z).
Proof. exact (MK_COMB (@lem1530082) (@lem1530081 x y z)). Qed.
Lemma lem1530084 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530085 (x : real) (y : real) (z : real) : (term157 z y x) = (term158 y z).
Proof. exact (MK_COMB (@lem1530083 x y z) (@lem1530084)). Qed.
Lemma lem1530086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530087 (x : real) (y : real) (z : real) : (term159 z y x) = (term160 y z).
Proof. exact (MK_COMB (@lem1530086) (@lem1530085 x y z)). Qed.
Lemma lem1530088 (x : real) (y : real) (z : real) : (term90 z y x) = (term161 x y z).
Proof. exact (MK_COMB (@lem1530087 x y z) (@lem1530001 x y z)). Qed.
Lemma lem1530089 (x : real) (y : real) (z : real) : (term84 z y x) = (term161 x y z).
Proof. exact (TRANS (@lem1529936 z y x) (@lem1530088 x y z)). Qed.
Lemma lem1530090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530091 (x : real) (y : real) (z : real) : (term86 z y x) = (term162 x y z).
Proof. exact (MK_COMB (@lem1530090) (@lem1530089 x y z)). Qed.
Lemma lem1530093 (a : real) (b : real) (x : real) (r : real) : (term88 a b x r) = (term89 a b x r).
Proof. exact (proj1 (@lem1482682 x a b (@el real) (@el real) r)). Qed.
Lemma lem1530094 (z : real) (y : real) (x : real) : (term78 z y x) = (term163 z y x).
Proof. exact (@lem1530093 x z (real_sub y x) term44). Qed.
Lemma lem1530100 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1530105 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1530107 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1530100 y x) (@lem1530105 x y)). Qed.
Lemma lem1530110 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1530111 (x : real) (y : real) : (term94 y x) = (term95 x y).
Proof. exact (MK_COMB (@lem1530110) (@lem1530107 x y)). Qed.
Lemma lem1530112 (x : real) (y : real) : (term95 x y) = (term92 x y).
Proof. exact (@lem1483460 (term92 x y)). Qed.
Lemma lem1530113 (x : real) (y : real) : (term94 y x) = (term92 x y).
Proof. exact (TRANS (@lem1530111 x y) (@lem1530112 x y)). Qed.
Lemma lem1530116 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1530117 (z : real) (x : real) (y : real) : (term96 z y x) = (term97 z x y).
Proof. exact (MK_COMB (@lem1530116 z) (@lem1530113 x y)). Qed.
Lemma lem1530118 (x : real) (z : real) (y : real) : (term97 z x y) = (term98 x z y).
Proof. exact (@lem1483484 (term51 x) z y). Qed.
Lemma lem1530119 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1530120 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1530121 (x : real) (y : real) (z : real) : (term98 x z y) = (term98 x y z).
Proof. exact (MK_COMB (@lem1530120 x) (@lem1530119 y z)). Qed.
Lemma lem1530122 (x : real) (y : real) (z : real) : (term97 z x y) = (term98 x y z).
Proof. exact (TRANS (@lem1530118 x z y) (@lem1530121 x y z)). Qed.
Lemma lem1530123 (x : real) (y : real) (z : real) : (term96 z y x) = (term98 x y z).
Proof. exact (TRANS (@lem1530117 z x y) (@lem1530122 x y z)). Qed.
Lemma lem1530126 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1530127 (x : real) (y : real) (z : real) : (term164 z y x) = (term165 x y z).
Proof. exact (MK_COMB (@lem1530126 x) (@lem1530123 x y z)). Qed.
Lemma lem1530128 (x : real) (y : real) (z : real) : (term165 x y z) = (term166 x y z).
Proof. exact (@lem1483490 x (term51 x) (real_add y z)). Qed.
Lemma lem1530129 (x : real) : (term167 x) = (term146 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1530131 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530132 : term148 = term44.
Proof. exact (@lem1530131 term107). Qed.
Lemma lem1530133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530134 : term149 = term150.
Proof. exact (MK_COMB (@lem1530133) (@lem1530132)). Qed.
Lemma lem1530135 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1530136 (x : real) : (term146 x) = (term151 x).
Proof. exact (MK_COMB (@lem1530134) (@lem1530135 x)). Qed.
Lemma lem1530137 (x : real) : (term167 x) = (term151 x).
Proof. exact (TRANS (@lem1530129 x) (@lem1530136 x)). Qed.
Lemma lem1530138 (x : real) : (term151 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1530139 (x : real) : (term167 x) = term44.
Proof. exact (TRANS (@lem1530137 x) (@lem1530138 x)). Qed.
Lemma lem1530140 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530141 (x : real) : (term168 x) = term153.
Proof. exact (MK_COMB (@lem1530140) (@lem1530139 x)). Qed.
Lemma lem1530142 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (eq_refl (real_add y z)). Qed.
Lemma lem1530143 (x : real) (y : real) (z : real) : (term166 x y z) = (term169 y z).
Proof. exact (MK_COMB (@lem1530141 x) (@lem1530142 y z)). Qed.
Lemma lem1530144 (x : real) (y : real) (z : real) : (term165 x y z) = (term169 y z).
Proof. exact (TRANS (@lem1530128 x y z) (@lem1530143 x y z)). Qed.
Lemma lem1530145 (y : real) (z : real) : (term169 y z) = (real_add y z).
Proof. exact (@lem1483448 (real_add y z)). Qed.
Lemma lem1530146 (x : real) (y : real) (z : real) : (term165 x y z) = (real_add y z).
Proof. exact (TRANS (@lem1530144 x y z) (@lem1530145 y z)). Qed.
Lemma lem1530147 (x : real) (y : real) (z : real) : (term164 z y x) = (real_add y z).
Proof. exact (TRANS (@lem1530127 x y z) (@lem1530146 x y z)). Qed.
Lemma lem1530148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530149 (x : real) (y : real) (z : real) : (term170 z y x) = (term171 y z).
Proof. exact (MK_COMB (@lem1530148) (@lem1530147 x y z)). Qed.
Lemma lem1530150 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530151 (x : real) (y : real) (z : real) : (term172 z y x) = (term173 y z).
Proof. exact (MK_COMB (@lem1530149 x y z) (@lem1530150)). Qed.
Lemma lem1530157 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1530162 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1530164 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1530157 y x) (@lem1530162 x y)). Qed.
Lemma lem1530167 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem1530168 (x : real) (y : real) : (term126 y x) = (term127 x y).
Proof. exact (MK_COMB (@lem1530167) (@lem1530164 x y)). Qed.
Lemma lem1530169 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (@lem1483508 (term51 x) term39 y). Qed.
Lemma lem1530170 (y : real) : (term51 y) = (term51 y).
Proof. exact (eq_refl (term51 y)). Qed.
Lemma lem1530171 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1530173 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1530174 : term133 = term134.
Proof. exact (@lem1530173 term107 term107). Qed.
Lemma lem1530175 : (term135 = (BIT1 0)) = (term136 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1530176 : term136 = term107.
Proof. exact (EQ_MP (@lem1530175) (@lem940073)). Qed.
Lemma lem1530177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1530178 : term134 = term137.
Proof. exact (MK_COMB (@lem1530177) (@lem1530176)). Qed.
Lemma lem1530179 : term133 = term137.
Proof. exact (TRANS (@lem1530174) (@lem1530178)). Qed.
Lemma lem1530180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530181 : term138 = term93.
Proof. exact (MK_COMB (@lem1530180) (@lem1530179)). Qed.
Lemma lem1530182 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1530183 (x : real) : (term130 x) = (term68 x).
Proof. exact (MK_COMB (@lem1530181) (@lem1530182 x)). Qed.
Lemma lem1530184 (x : real) : (term129 x) = (term68 x).
Proof. exact (TRANS (@lem1530171 x) (@lem1530183 x)). Qed.
Lemma lem1530185 (x : real) : (term68 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1530186 (x : real) : (term129 x) = x.
Proof. exact (TRANS (@lem1530184 x) (@lem1530185 x)). Qed.
Lemma lem1530187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530188 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1530187) (@lem1530186 x)). Qed.
Lemma lem1530189 (x : real) (y : real) : (term128 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1530188 x) (@lem1530170 y)). Qed.
Lemma lem1530190 (x : real) (y : real) : (term127 x y) = (term91 x y).
Proof. exact (TRANS (@lem1530169 x y) (@lem1530189 x y)). Qed.
Lemma lem1530191 (x : real) (y : real) : (term126 y x) = (term91 x y).
Proof. exact (TRANS (@lem1530168 x y) (@lem1530190 x y)). Qed.
Lemma lem1530194 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1530195 (z : real) (x : real) (y : real) : (term140 z y x) = (term141 z x y).
Proof. exact (MK_COMB (@lem1530194 z) (@lem1530191 x y)). Qed.
Lemma lem1530196 (x : real) (z : real) (y : real) : (term141 z x y) = (term141 x z y).
Proof. exact (@lem1483484 x z (term51 y)). Qed.
Lemma lem1530197 (y : real) (z : real) : (term91 z y) = (term92 y z).
Proof. exact (@lem1483488 (term51 y) z). Qed.
Lemma lem1530198 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1530199 (x : real) (y : real) (z : real) : (term141 x z y) = (term97 x y z).
Proof. exact (MK_COMB (@lem1530198 x) (@lem1530197 y z)). Qed.
Lemma lem1530200 (x : real) (y : real) (z : real) : (term141 z x y) = (term97 x y z).
Proof. exact (TRANS (@lem1530196 x z y) (@lem1530199 x y z)). Qed.
Lemma lem1530201 (x : real) (y : real) (z : real) : (term140 z y x) = (term97 x y z).
Proof. exact (TRANS (@lem1530195 z x y) (@lem1530200 x y z)). Qed.
Lemma lem1530204 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1530205 (x : real) (y : real) (z : real) : (term174 z y x) = (term175 x y z).
Proof. exact (MK_COMB (@lem1530204 x) (@lem1530201 x y z)). Qed.
Lemma lem1530206 (x : real) (y : real) (z : real) : (term175 x y z) = (term176 x y z).
Proof. exact (@lem1483490 x x (term92 y z)). Qed.
Lemma lem1530207 (x : real) : (real_add x x) = (term177 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1530208 : term178 = term112.
Proof. exact (@lem1367770 term107 term107). Qed.
Lemma lem1530209 : term108 = term109.
Proof. exact (@lem706885). Qed.
Lemma lem1530210 : (term108 = term109) = (term110 = term111).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term109). Qed.
Lemma lem1530211 : term110 = term111.
Proof. exact (EQ_MP (@lem1530210) (@lem1530209)). Qed.
Lemma lem1530212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1530213 : term112 = term113.
Proof. exact (MK_COMB (@lem1530212) (@lem1530211)). Qed.
Lemma lem1530214 : term178 = term113.
Proof. exact (TRANS (@lem1530208) (@lem1530213)). Qed.
Lemma lem1530215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530216 : term179 = term180.
Proof. exact (MK_COMB (@lem1530215) (@lem1530214)). Qed.
Lemma lem1530217 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1530218 (x : real) : (term177 x) = (term181 x).
Proof. exact (MK_COMB (@lem1530216) (@lem1530217 x)). Qed.
Lemma lem1530219 (x : real) : (real_add x x) = (term181 x).
Proof. exact (TRANS (@lem1530207 x) (@lem1530218 x)). Qed.
Lemma lem1530220 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530221 (x : real) : (term182 x) = (term183 x).
Proof. exact (MK_COMB (@lem1530220) (@lem1530219 x)). Qed.
Lemma lem1530222 (y : real) (z : real) : (term92 y z) = (term92 y z).
Proof. exact (eq_refl (term92 y z)). Qed.
Lemma lem1530223 (x : real) (y : real) (z : real) : (term176 x y z) = (term184 x y z).
Proof. exact (MK_COMB (@lem1530221 x) (@lem1530222 y z)). Qed.
Lemma lem1530224 (x : real) (y : real) (z : real) : (term175 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1530206 x y z) (@lem1530223 x y z)). Qed.
Lemma lem1530225 (x : real) (y : real) (z : real) : (term174 z y x) = (term184 x y z).
Proof. exact (TRANS (@lem1530205 x y z) (@lem1530224 x y z)). Qed.
Lemma lem1530226 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530227 (x : real) (y : real) (z : real) : (term185 z y x) = (term186 x y z).
Proof. exact (MK_COMB (@lem1530226) (@lem1530225 x y z)). Qed.
Lemma lem1530228 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530229 (x : real) (y : real) (z : real) : (term187 z y x) = (term188 x y z).
Proof. exact (MK_COMB (@lem1530227 x y z) (@lem1530228)). Qed.
Lemma lem1530230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530231 (x : real) (y : real) (z : real) : (term189 z y x) = (term190 x y z).
Proof. exact (MK_COMB (@lem1530230) (@lem1530229 x y z)). Qed.
Lemma lem1530232 (x : real) (y : real) (z : real) : (term163 z y x) = (term191 x y z).
Proof. exact (MK_COMB (@lem1530231 x y z) (@lem1530151 x y z)). Qed.
Lemma lem1530233 (x : real) (y : real) (z : real) : (term78 z y x) = (term191 x y z).
Proof. exact (TRANS (@lem1530094 z y x) (@lem1530232 x y z)). Qed.
Lemma lem1530234 (x : real) (y : real) (z : real) : (term87 z y x) = (term192 x y z).
Proof. exact (MK_COMB (@lem1530091 x y z) (@lem1530233 x y z)). Qed.
Lemma lem1530235 (x : real) (y : real) (z : real) : (term45 z y x) = (term192 x y z).
Proof. exact (TRANS (@lem1529933 z y x) (@lem1530234 x y z)). Qed.
Lemma lem1530236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530237 (x : real) (y : real) (z : real) : (term56 z y x) = (term193 x y z).
Proof. exact (MK_COMB (@lem1530236) (@lem1530235 x y z)). Qed.
Lemma lem1530238 (z : real) (y : real) : (term54 z y) = (term54 z y).
Proof. exact (eq_refl (term54 z y)). Qed.
Lemma lem1530239 (x : real) (z : real) (y : real) : (term57 x z y) = (term194 x z y).
Proof. exact (MK_COMB (@lem1530237 x y z) (@lem1530238 z y)). Qed.
Lemma lem1530240 (x : real) (z : real) (y : real) : (term195 x z y) = (term194 x z y).
Proof. exact (eq_refl (term195 x z y)). Qed.
Lemma lem1530241 (x : real) (z : real) (y : real) : (term194 x z y) = (term195 x z y).
Proof. exact (SYM (@lem1530240 x z y)). Qed.
Lemma lem1530242 (x : real) (z : real) (y : real) : (term195 x z y) = (term196 x z y).
Proof. exact (@lem1482981 (term197 x y z) y). Qed.
Lemma lem1530243 (x : real) (z : real) (y : real) : (term194 x z y) = (term196 x z y).
Proof. exact (TRANS (@lem1530241 x z y) (@lem1530242 x z y)). Qed.
Lemma lem1530244 (x : real) (z : real) (y : real) : (term198 x z y) = (term199 x z y).
Proof. exact (eq_refl (term198 x z y)). Qed.
Lemma lem1530245 (y : real) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem1530246 (x : real) (z : real) (y : real) : (term201 x z y) = (term202 x z y).
Proof. exact (MK_COMB (@lem1530245 y) (@lem1530244 x z y)). Qed.
Lemma lem1530247 (x : real) (z : real) (y : real) : (term203 x z y) = (term204 x z y).
Proof. exact (eq_refl (term203 x z y)). Qed.
Lemma lem1530248 (y : real) : (term205 y) = (term205 y).
Proof. exact (eq_refl (term205 y)). Qed.
Lemma lem1530249 (x : real) (z : real) (y : real) : (term206 x z y) = (term207 x z y).
Proof. exact (MK_COMB (@lem1530248 y) (@lem1530247 x z y)). Qed.
Lemma lem1530250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1530251 (x : real) (z : real) (y : real) : (term208 x z y) = (term209 x z y).
Proof. exact (MK_COMB (@lem1530250) (@lem1530249 x z y)). Qed.
Lemma lem1530252 (x : real) (z : real) (y : real) : (term196 x z y) = (term210 x z y).
Proof. exact (MK_COMB (@lem1530251 x z y) (@lem1530246 x z y)). Qed.
Lemma lem1530253 (x : real) (z : real) (y : real) : (term211 x z y) = (term211 x z y).
Proof. exact (eq_refl (term211 x z y)). Qed.
Lemma lem1530254 (x : real) (z : real) (y : real) : ((term194 x z y) = (term196 x z y)) = ((term194 x z y) = (term210 x z y)).
Proof. exact (MK_COMB (@lem1530253 x z y) (@lem1530252 x z y)). Qed.
Lemma lem1530255 (x : real) (z : real) (y : real) : (term194 x z y) = (term210 x z y).
Proof. exact (EQ_MP (@lem1530254 x z y) (@lem1530243 x z y)). Qed.
Lemma lem1530256 (y : real) : (term212 y) = (term213 y).
Proof. exact (@lem1483527 y term44). Qed.
Lemma lem1530262 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1483519 y term44). Qed.
Lemma lem1530264 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530265 : term217 = term44.
Proof. exact (@lem1530264 term107). Qed.
Lemma lem1530266 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1530267 (y : real) : (term215 y) = (term218 y).
Proof. exact (MK_COMB (@lem1530266 y) (@lem1530265)). Qed.
Lemma lem1530268 (y : real) : (term218 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1530269 (y : real) : (term215 y) = y.
Proof. exact (TRANS (@lem1530267 y) (@lem1530268 y)). Qed.
Lemma lem1530271 (y : real) : (term214 y) = y.
Proof. exact (TRANS (@lem1530262 y) (@lem1530269 y)). Qed.
Lemma lem1530272 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530273 (y : real) : (term219 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1530272) (@lem1530271 y)). Qed.
Lemma lem1530274 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530275 (y : real) : (term213 y) = (term212 y).
Proof. exact (MK_COMB (@lem1530273 y) (@lem1530274)). Qed.
Lemma lem1530276 (y : real) : (term212 y) = (term212 y).
Proof. exact (TRANS (@lem1530256 y) (@lem1530275 y)). Qed.
Lemma lem1530277 (y : real) (z : real) : (term158 y z) = (term220 y z).
Proof. exact (@lem1483527 (term92 y z) term44). Qed.
Lemma lem1530295 (y : real) (z : real) : (term221 y z) = (term222 y z).
Proof. exact (@lem1483519 (term92 y z) term44). Qed.
Lemma lem1530297 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530298 : term217 = term44.
Proof. exact (@lem1530297 term107). Qed.
Lemma lem1530299 (y : real) (z : real) : (term223 y z) = (term223 y z).
Proof. exact (eq_refl (term223 y z)). Qed.
Lemma lem1530300 (y : real) (z : real) : (term222 y z) = (term224 y z).
Proof. exact (MK_COMB (@lem1530299 y z) (@lem1530298)). Qed.
Lemma lem1530301 (y : real) (z : real) : (term224 y z) = (term92 y z).
Proof. exact (@lem1483450 (term92 y z)). Qed.
Lemma lem1530302 (y : real) (z : real) : (term222 y z) = (term92 y z).
Proof. exact (TRANS (@lem1530300 y z) (@lem1530301 y z)). Qed.
Lemma lem1530304 (y : real) (z : real) : (term221 y z) = (term92 y z).
Proof. exact (TRANS (@lem1530295 y z) (@lem1530302 y z)). Qed.
Lemma lem1530305 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530306 (y : real) (z : real) : (term225 y z) = (term156 y z).
Proof. exact (MK_COMB (@lem1530305) (@lem1530304 y z)). Qed.
Lemma lem1530307 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530308 (y : real) (z : real) : (term220 y z) = (term158 y z).
Proof. exact (MK_COMB (@lem1530306 y z) (@lem1530307)). Qed.
Lemma lem1530309 (y : real) (z : real) : (term158 y z) = (term158 y z).
Proof. exact (TRANS (@lem1530277 y z) (@lem1530308 y z)). Qed.
Lemma lem1530310 (x : real) (y : real) (z : real) : (term124 x y z) = (term226 x y z).
Proof. exact (@lem1483527 (term120 x y z) term44). Qed.
Lemma lem1530334 (x : real) (y : real) (z : real) : (term227 x y z) = (term228 x y z).
Proof. exact (@lem1483519 (term120 x y z) term44). Qed.
Lemma lem1530336 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530337 : term217 = term44.
Proof. exact (@lem1530336 term107). Qed.
Lemma lem1530338 (x : real) (y : real) (z : real) : (term229 x y z) = (term229 x y z).
Proof. exact (eq_refl (term229 x y z)). Qed.
Lemma lem1530339 (x : real) (y : real) (z : real) : (term228 x y z) = (term230 x y z).
Proof. exact (MK_COMB (@lem1530338 x y z) (@lem1530337)). Qed.
Lemma lem1530340 (x : real) (y : real) (z : real) : (term230 x y z) = (term120 x y z).
Proof. exact (@lem1483450 (term120 x y z)). Qed.
Lemma lem1530341 (x : real) (y : real) (z : real) : (term228 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1530339 x y z) (@lem1530340 x y z)). Qed.
Lemma lem1530343 (x : real) (y : real) (z : real) : (term227 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1530334 x y z) (@lem1530341 x y z)). Qed.
Lemma lem1530344 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530345 (x : real) (y : real) (z : real) : (term231 x y z) = (term122 x y z).
Proof. exact (MK_COMB (@lem1530344) (@lem1530343 x y z)). Qed.
Lemma lem1530346 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530347 (x : real) (y : real) (z : real) : (term226 x y z) = (term124 x y z).
Proof. exact (MK_COMB (@lem1530345 x y z) (@lem1530346)). Qed.
Lemma lem1530348 (x : real) (y : real) (z : real) : (term124 x y z) = (term124 x y z).
Proof. exact (TRANS (@lem1530310 x y z) (@lem1530347 x y z)). Qed.
Lemma lem1530349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530350 (y : real) (z : real) : (term160 y z) = (term160 y z).
Proof. exact (MK_COMB (@lem1530349) (@lem1530309 y z)). Qed.
Lemma lem1530351 (x : real) (y : real) (z : real) : (term161 x y z) = (term161 x y z).
Proof. exact (MK_COMB (@lem1530350 y z) (@lem1530348 x y z)). Qed.
Lemma lem1530352 (x : real) (y : real) (z : real) : (term188 x y z) = (term232 x y z).
Proof. exact (@lem1483527 (term184 x y z) term44). Qed.
Lemma lem1530382 (x : real) (y : real) (z : real) : (term233 x y z) = (term234 x y z).
Proof. exact (@lem1483519 (term184 x y z) term44). Qed.
Lemma lem1530384 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530385 : term217 = term44.
Proof. exact (@lem1530384 term107). Qed.
Lemma lem1530386 (x : real) (y : real) (z : real) : (term235 x y z) = (term235 x y z).
Proof. exact (eq_refl (term235 x y z)). Qed.
Lemma lem1530387 (x : real) (y : real) (z : real) : (term234 x y z) = (term236 x y z).
Proof. exact (MK_COMB (@lem1530386 x y z) (@lem1530385)). Qed.
Lemma lem1530388 (x : real) (y : real) (z : real) : (term236 x y z) = (term184 x y z).
Proof. exact (@lem1483450 (term184 x y z)). Qed.
Lemma lem1530389 (x : real) (y : real) (z : real) : (term234 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1530387 x y z) (@lem1530388 x y z)). Qed.
Lemma lem1530391 (x : real) (y : real) (z : real) : (term233 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1530382 x y z) (@lem1530389 x y z)). Qed.
Lemma lem1530392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530393 (x : real) (y : real) (z : real) : (term237 x y z) = (term186 x y z).
Proof. exact (MK_COMB (@lem1530392) (@lem1530391 x y z)). Qed.
Lemma lem1530394 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530395 (x : real) (y : real) (z : real) : (term232 x y z) = (term188 x y z).
Proof. exact (MK_COMB (@lem1530393 x y z) (@lem1530394)). Qed.
Lemma lem1530396 (x : real) (y : real) (z : real) : (term188 x y z) = (term188 x y z).
Proof. exact (TRANS (@lem1530352 x y z) (@lem1530395 x y z)). Qed.
Lemma lem1530397 (y : real) (z : real) : (term173 y z) = (term238 y z).
Proof. exact (@lem1483527 (real_add y z) term44). Qed.
Lemma lem1530409 (y : real) (z : real) : (term239 y z) = (term240 y z).
Proof. exact (@lem1483519 (real_add y z) term44). Qed.
Lemma lem1530411 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530412 : term217 = term44.
Proof. exact (@lem1530411 term107). Qed.
Lemma lem1530413 (y : real) (z : real) : (term241 y z) = (term241 y z).
Proof. exact (eq_refl (term241 y z)). Qed.
Lemma lem1530414 (y : real) (z : real) : (term240 y z) = (term242 y z).
Proof. exact (MK_COMB (@lem1530413 y z) (@lem1530412)). Qed.
Lemma lem1530415 (y : real) (z : real) : (term242 y z) = (real_add y z).
Proof. exact (@lem1483450 (real_add y z)). Qed.
Lemma lem1530416 (y : real) (z : real) : (term240 y z) = (real_add y z).
Proof. exact (TRANS (@lem1530414 y z) (@lem1530415 y z)). Qed.
Lemma lem1530418 (y : real) (z : real) : (term239 y z) = (real_add y z).
Proof. exact (TRANS (@lem1530409 y z) (@lem1530416 y z)). Qed.
Lemma lem1530419 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530420 (y : real) (z : real) : (term243 y z) = (term171 y z).
Proof. exact (MK_COMB (@lem1530419) (@lem1530418 y z)). Qed.
Lemma lem1530421 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530422 (y : real) (z : real) : (term238 y z) = (term173 y z).
Proof. exact (MK_COMB (@lem1530420 y z) (@lem1530421)). Qed.
Lemma lem1530423 (y : real) (z : real) : (term173 y z) = (term173 y z).
Proof. exact (TRANS (@lem1530397 y z) (@lem1530422 y z)). Qed.
Lemma lem1530424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530425 (x : real) (y : real) (z : real) : (term190 x y z) = (term190 x y z).
Proof. exact (MK_COMB (@lem1530424) (@lem1530396 x y z)). Qed.
Lemma lem1530426 (x : real) (y : real) (z : real) : (term191 x y z) = (term191 x y z).
Proof. exact (MK_COMB (@lem1530425 x y z) (@lem1530423 y z)). Qed.
Lemma lem1530427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530428 (x : real) (y : real) (z : real) : (term162 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1530427) (@lem1530351 x y z)). Qed.
Lemma lem1530429 (x : real) (y : real) (z : real) : (term192 x y z) = (term192 x y z).
Proof. exact (MK_COMB (@lem1530428 x y z) (@lem1530426 x y z)). Qed.
Lemma lem1530430 (z : real) (y : real) : (term244 z y) = (term245 z y).
Proof. exact (@lem1483525 (term92 z y) term44). Qed.
Lemma lem1530431 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530444 (y : real) (z : real) : (term92 z y) = (term91 y z).
Proof. exact (@lem1483488 y (term51 z)). Qed.
Lemma lem1530445 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1530446 (y : real) (z : real) : (term246 z y) = (term247 y z).
Proof. exact (MK_COMB (@lem1530445) (@lem1530444 y z)). Qed.
Lemma lem1530447 (y : real) (z : real) : (term221 z y) = (term248 y z).
Proof. exact (MK_COMB (@lem1530446 y z) (@lem1530431)). Qed.
Lemma lem1530448 (y : real) (z : real) : (term248 y z) = (term249 y z).
Proof. exact (@lem1483519 (term91 y z) term44). Qed.
Lemma lem1530450 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530451 : term217 = term44.
Proof. exact (@lem1530450 term107). Qed.
Lemma lem1530452 (y : real) (z : real) : (term250 y z) = (term250 y z).
Proof. exact (eq_refl (term250 y z)). Qed.
Lemma lem1530453 (y : real) (z : real) : (term249 y z) = (term251 y z).
Proof. exact (MK_COMB (@lem1530452 y z) (@lem1530451)). Qed.
Lemma lem1530454 (y : real) (z : real) : (term251 y z) = (term91 y z).
Proof. exact (@lem1483450 (term91 y z)). Qed.
Lemma lem1530455 (y : real) (z : real) : (term249 y z) = (term91 y z).
Proof. exact (TRANS (@lem1530453 y z) (@lem1530454 y z)). Qed.
Lemma lem1530456 (y : real) (z : real) : (term248 y z) = (term91 y z).
Proof. exact (TRANS (@lem1530448 y z) (@lem1530455 y z)). Qed.
Lemma lem1530457 (y : real) (z : real) : (term221 z y) = (term91 y z).
Proof. exact (TRANS (@lem1530447 y z) (@lem1530456 y z)). Qed.
Lemma lem1530458 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530459 (y : real) (z : real) : (term252 z y) = (term253 y z).
Proof. exact (MK_COMB (@lem1530458) (@lem1530457 y z)). Qed.
Lemma lem1530460 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530461 (y : real) (z : real) : (term245 z y) = (term254 y z).
Proof. exact (MK_COMB (@lem1530459 y z) (@lem1530460)). Qed.
Lemma lem1530462 (y : real) (z : real) : (term244 z y) = (term254 y z).
Proof. exact (TRANS (@lem1530430 z y) (@lem1530461 y z)). Qed.
Lemma lem1530463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530464 (x : real) (y : real) (z : real) : (term193 x y z) = (term193 x y z).
Proof. exact (MK_COMB (@lem1530463) (@lem1530429 x y z)). Qed.
Lemma lem1530465 (x : real) (y : real) (z : real) : (term204 x z y) = (term255 x y z).
Proof. exact (MK_COMB (@lem1530464 x y z) (@lem1530462 y z)). Qed.
Lemma lem1530466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530467 (y : real) : (term205 y) = (term205 y).
Proof. exact (MK_COMB (@lem1530466) (@lem1530276 y)). Qed.
Lemma lem1530468 (x : real) (y : real) (z : real) : (term207 x z y) = (term256 x y z).
Proof. exact (MK_COMB (@lem1530467 y) (@lem1530465 x y z)). Qed.
Lemma lem1530469 (y : real) : (term257 y) = (term258 y).
Proof. exact (@lem1483525 term44 y). Qed.
Lemma lem1530475 (y : real) : (term259 y) = (term260 y).
Proof. exact (@lem1483519 term44 y). Qed.
Lemma lem1530480 (y : real) : (term260 y) = (term51 y).
Proof. exact (@lem1483448 (term51 y)). Qed.
Lemma lem1530482 (y : real) : (term259 y) = (term51 y).
Proof. exact (TRANS (@lem1530475 y) (@lem1530480 y)). Qed.
Lemma lem1530483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530484 (y : real) : (term261 y) = (term262 y).
Proof. exact (MK_COMB (@lem1530483) (@lem1530482 y)). Qed.
Lemma lem1530485 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530486 (y : real) : (term258 y) = (term263 y).
Proof. exact (MK_COMB (@lem1530484 y) (@lem1530485)). Qed.
Lemma lem1530487 (y : real) : (term257 y) = (term263 y).
Proof. exact (TRANS (@lem1530469 y) (@lem1530486 y)). Qed.
Lemma lem1530488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530489 (y : real) (z : real) : (term160 y z) = (term160 y z).
Proof. exact (MK_COMB (@lem1530488) (@lem1530309 y z)). Qed.
Lemma lem1530490 (x : real) (y : real) (z : real) : (term161 x y z) = (term161 x y z).
Proof. exact (MK_COMB (@lem1530489 y z) (@lem1530348 x y z)). Qed.
Lemma lem1530491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530492 (x : real) (y : real) (z : real) : (term190 x y z) = (term190 x y z).
Proof. exact (MK_COMB (@lem1530491) (@lem1530396 x y z)). Qed.
Lemma lem1530493 (x : real) (y : real) (z : real) : (term191 x y z) = (term191 x y z).
Proof. exact (MK_COMB (@lem1530492 x y z) (@lem1530423 y z)). Qed.
Lemma lem1530494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530495 (x : real) (y : real) (z : real) : (term162 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1530494) (@lem1530490 x y z)). Qed.
Lemma lem1530496 (x : real) (y : real) (z : real) : (term192 x y z) = (term192 x y z).
Proof. exact (MK_COMB (@lem1530495 x y z) (@lem1530493 x y z)). Qed.
Lemma lem1530497 (z : real) (y : real) : (term264 z y) = (term265 z y).
Proof. exact (@lem1483525 (term266 z y) term44). Qed.
Lemma lem1530498 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530505 (y : real) : (real_neg y) = (term51 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1530514 (z : real) : (term99 z) = (term99 z).
Proof. exact (eq_refl (term99 z)). Qed.
Lemma lem1530515 (z : real) (y : real) : (term266 z y) = (term267 z y).
Proof. exact (MK_COMB (@lem1530514 z) (@lem1530505 y)). Qed.
Lemma lem1530516 (y : real) (z : real) : (term267 z y) = (term267 y z).
Proof. exact (@lem1483488 (term51 y) (term51 z)). Qed.
Lemma lem1530517 (y : real) (z : real) : (term266 z y) = (term267 y z).
Proof. exact (TRANS (@lem1530515 z y) (@lem1530516 y z)). Qed.
Lemma lem1530518 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1530519 (y : real) (z : real) : (term268 z y) = (term269 y z).
Proof. exact (MK_COMB (@lem1530518) (@lem1530517 y z)). Qed.
Lemma lem1530520 (y : real) (z : real) : (term270 z y) = (term271 y z).
Proof. exact (MK_COMB (@lem1530519 y z) (@lem1530498)). Qed.
Lemma lem1530521 (y : real) (z : real) : (term271 y z) = (term272 y z).
Proof. exact (@lem1483519 (term267 y z) term44). Qed.
Lemma lem1530523 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1530524 : term217 = term44.
Proof. exact (@lem1530523 term107). Qed.
Lemma lem1530525 (y : real) (z : real) : (term273 y z) = (term273 y z).
Proof. exact (eq_refl (term273 y z)). Qed.
Lemma lem1530526 (y : real) (z : real) : (term272 y z) = (term274 y z).
Proof. exact (MK_COMB (@lem1530525 y z) (@lem1530524)). Qed.
Lemma lem1530527 (y : real) (z : real) : (term274 y z) = (term267 y z).
Proof. exact (@lem1483450 (term267 y z)). Qed.
Lemma lem1530528 (y : real) (z : real) : (term272 y z) = (term267 y z).
Proof. exact (TRANS (@lem1530526 y z) (@lem1530527 y z)). Qed.
Lemma lem1530529 (y : real) (z : real) : (term271 y z) = (term267 y z).
Proof. exact (TRANS (@lem1530521 y z) (@lem1530528 y z)). Qed.
Lemma lem1530530 (y : real) (z : real) : (term270 z y) = (term267 y z).
Proof. exact (TRANS (@lem1530520 y z) (@lem1530529 y z)). Qed.
Lemma lem1530531 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530532 (y : real) (z : real) : (term275 z y) = (term276 y z).
Proof. exact (MK_COMB (@lem1530531) (@lem1530530 y z)). Qed.
Lemma lem1530533 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530534 (y : real) (z : real) : (term265 z y) = (term277 y z).
Proof. exact (MK_COMB (@lem1530532 y z) (@lem1530533)). Qed.
Lemma lem1530535 (y : real) (z : real) : (term264 z y) = (term277 y z).
Proof. exact (TRANS (@lem1530497 z y) (@lem1530534 y z)). Qed.
Lemma lem1530536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530537 (x : real) (y : real) (z : real) : (term193 x y z) = (term193 x y z).
Proof. exact (MK_COMB (@lem1530536) (@lem1530496 x y z)). Qed.
Lemma lem1530538 (x : real) (y : real) (z : real) : (term199 x z y) = (term278 x y z).
Proof. exact (MK_COMB (@lem1530537 x y z) (@lem1530535 y z)). Qed.
Lemma lem1530539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530540 (y : real) : (term200 y) = (term279 y).
Proof. exact (MK_COMB (@lem1530539) (@lem1530487 y)). Qed.
Lemma lem1530541 (x : real) (y : real) (z : real) : (term202 x z y) = (term280 x y z).
Proof. exact (MK_COMB (@lem1530540 y) (@lem1530538 x y z)). Qed.
Lemma lem1530542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1530543 (x : real) (y : real) (z : real) : (term209 x z y) = (term281 x y z).
Proof. exact (MK_COMB (@lem1530542) (@lem1530468 x y z)). Qed.
Lemma lem1530544 (x : real) (y : real) (z : real) : (term210 x z y) = (term282 x y z).
Proof. exact (MK_COMB (@lem1530543 x y z) (@lem1530541 x y z)). Qed.
Lemma lem1530555 (x : real) (y : real) (z : real) : (term194 x z y) = (term282 x y z).
Proof. exact (TRANS (@lem1530255 x z y) (@lem1530544 x y z)). Qed.
Lemma lem1530556 (x : real) (y : real) (z : real) : (term57 x z y) = (term282 x y z).
Proof. exact (TRANS (@lem1530239 x z y) (@lem1530555 x y z)). Qed.
Lemma lem1530557 (x : real) (y : real) (z : real) (h1 : term282 x y z) : term282 x y z.
Proof. exact (h1). Qed.
Lemma lem1530558 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term256 x y z.
Proof. exact (h1). Qed.
Lemma lem1530559 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term255 x y z.
Proof. exact (proj2 (@lem1530558 x y z h1)). Qed.
Lemma lem1530561 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term254 y z.
Proof. exact (proj2 (@lem1530559 x y z h1)). Qed.
Lemma lem1530562 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term192 x y z.
Proof. exact (proj1 (@lem1530559 x y z h1)). Qed.
Lemma lem1530564 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term161 x y z.
Proof. exact (proj1 (@lem1530562 x y z h1)). Qed.
Lemma lem1530566 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term158 y z.
Proof. exact (proj1 (@lem1530564 x y z h1)). Qed.
Lemma lem1530570 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530571 : term284 = term285.
Proof. exact (@lem1530570 (NUMERAL 0) term107). Qed.
Lemma lem1530572 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1530573 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1530574 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1530573 h1) (fun h1 : term285 = True => @lem1530572)). Qed.
Lemma lem1530575 : term285 = True.
Proof. exact (EQ_MP (@lem1530574) (@lem1530572)). Qed.
Lemma lem1530576 : term284 = True.
Proof. exact (TRANS (@lem1530571) (@lem1530575)). Qed.
Lemma lem1530577 : True = term284.
Proof. exact (SYM (@lem1530576)). Qed.
Lemma lem1530578 : term284.
Proof. exact (EQ_MP (@lem1530577) (@lem0)). Qed.
Lemma lem1530579 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term287 y z.
Proof. exact (conj (@lem1530578) (@lem1530566 x y z h1)). Qed.
Lemma lem1530581 (x : real) (y : real) : term288 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1530582 (y : real) (z : real) : term289 y z.
Proof. exact (@lem1530581 term137 (term92 y z)). Qed.
Lemma lem1530583 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term290 y z.
Proof. exact (@lem1530582 y z (@lem1530579 x y z h1)). Qed.
Lemma lem1530584 (y : real) (z : real) : (term95 y z) = (term92 y z).
Proof. exact (@lem1483460 (term92 y z)). Qed.
Lemma lem1530585 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530586 (y : real) (z : real) : (term291 y z) = (term156 y z).
Proof. exact (MK_COMB (@lem1530585) (@lem1530584 y z)). Qed.
Lemma lem1530587 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530588 (y : real) (z : real) : (term290 y z) = (term158 y z).
Proof. exact (MK_COMB (@lem1530586 y z) (@lem1530587)). Qed.
Lemma lem1530589 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term158 y z.
Proof. exact (EQ_MP (@lem1530588 y z) (@lem1530583 x y z h1)). Qed.
Lemma lem1530591 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530592 : term284 = term285.
Proof. exact (@lem1530591 (NUMERAL 0) term107). Qed.
Lemma lem1530593 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1530594 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1530595 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1530594 h1) (fun h1 : term285 = True => @lem1530593)). Qed.
Lemma lem1530596 : term285 = True.
Proof. exact (EQ_MP (@lem1530595) (@lem1530593)). Qed.
Lemma lem1530597 : term284 = True.
Proof. exact (TRANS (@lem1530592) (@lem1530596)). Qed.
Lemma lem1530598 : True = term284.
Proof. exact (SYM (@lem1530597)). Qed.
Lemma lem1530599 : term284.
Proof. exact (EQ_MP (@lem1530598) (@lem0)). Qed.
Lemma lem1530600 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term292 y z.
Proof. exact (conj (@lem1530599) (@lem1530561 x y z h1)). Qed.
Lemma lem1530602 (x : real) (y : real) : term293 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1530603 (y : real) (z : real) : term294 y z.
Proof. exact (@lem1530602 term137 (term91 y z)). Qed.
Lemma lem1530604 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term295 y z.
Proof. exact (@lem1530603 y z (@lem1530600 x y z h1)). Qed.
Lemma lem1530605 (y : real) (z : real) : (term296 y z) = (term91 y z).
Proof. exact (@lem1483460 (term91 y z)). Qed.
Lemma lem1530606 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530607 (y : real) (z : real) : (term297 y z) = (term253 y z).
Proof. exact (MK_COMB (@lem1530606) (@lem1530605 y z)). Qed.
Lemma lem1530608 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530609 (y : real) (z : real) : (term295 y z) = (term254 y z).
Proof. exact (MK_COMB (@lem1530607 y z) (@lem1530608)). Qed.
Lemma lem1530610 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term254 y z.
Proof. exact (EQ_MP (@lem1530609 y z) (@lem1530604 x y z h1)). Qed.
Lemma lem1530611 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term298 y z.
Proof. exact (conj (@lem1530610 x y z h1) (@lem1530589 x y z h1)). Qed.
Lemma lem1530613 (x : real) (y : real) : term299 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1530614 (y : real) (z : real) : term300 y z.
Proof. exact (@lem1530613 (term91 y z) (term92 y z)). Qed.
Lemma lem1530615 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term301 y z.
Proof. exact (@lem1530614 y z (@lem1530611 x y z h1)). Qed.
Lemma lem1530616 (y : real) (z : real) : (term302 y z) = (term303 y z).
Proof. exact (@lem1483480 y (term51 y) (term51 z) z). Qed.
Lemma lem1530617 (y : real) : (term167 y) = (term146 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1530619 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530620 : term148 = term44.
Proof. exact (@lem1530619 term107). Qed.
Lemma lem1530621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530622 : term149 = term150.
Proof. exact (MK_COMB (@lem1530621) (@lem1530620)). Qed.
Lemma lem1530623 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1530624 (y : real) : (term146 y) = (term151 y).
Proof. exact (MK_COMB (@lem1530622) (@lem1530623 y)). Qed.
Lemma lem1530625 (y : real) : (term167 y) = (term151 y).
Proof. exact (TRANS (@lem1530617 y) (@lem1530624 y)). Qed.
Lemma lem1530626 (y : real) : (term151 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1530627 (y : real) : (term167 y) = term44.
Proof. exact (TRANS (@lem1530625 y) (@lem1530626 y)). Qed.
Lemma lem1530628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530629 (y : real) : (term168 y) = term153.
Proof. exact (MK_COMB (@lem1530628) (@lem1530627 y)). Qed.
Lemma lem1530630 (z : real) : (term145 z) = (term146 z).
Proof. exact (@lem1483440 term39 z). Qed.
Lemma lem1530632 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530633 : term148 = term44.
Proof. exact (@lem1530632 term107). Qed.
Lemma lem1530634 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530635 : term149 = term150.
Proof. exact (MK_COMB (@lem1530634) (@lem1530633)). Qed.
Lemma lem1530636 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1530637 (z : real) : (term146 z) = (term151 z).
Proof. exact (MK_COMB (@lem1530635) (@lem1530636 z)). Qed.
Lemma lem1530638 (z : real) : (term145 z) = (term151 z).
Proof. exact (TRANS (@lem1530630 z) (@lem1530637 z)). Qed.
Lemma lem1530639 (z : real) : (term151 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1530640 (z : real) : (term145 z) = term44.
Proof. exact (TRANS (@lem1530638 z) (@lem1530639 z)). Qed.
Lemma lem1530641 (y : real) (z : real) : (term303 y z) = term304.
Proof. exact (MK_COMB (@lem1530629 y) (@lem1530640 z)). Qed.
Lemma lem1530642 (y : real) (z : real) : (term302 y z) = term304.
Proof. exact (TRANS (@lem1530616 y z) (@lem1530641 y z)). Qed.
Lemma lem1530643 : term304 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1530644 (y : real) (z : real) : (term302 y z) = term44.
Proof. exact (TRANS (@lem1530642 y z) (@lem1530643)). Qed.
Lemma lem1530645 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530646 (y : real) (z : real) : (term305 y z) = term306.
Proof. exact (MK_COMB (@lem1530645) (@lem1530644 y z)). Qed.
Lemma lem1530647 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530648 (y : real) (z : real) : (term301 y z) = term307.
Proof. exact (MK_COMB (@lem1530646 y z) (@lem1530647)). Qed.
Lemma lem1530649 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term307.
Proof. exact (EQ_MP (@lem1530648 y z) (@lem1530615 x y z h1)). Qed.
Lemma lem1530651 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530652 : term307 = term308.
Proof. exact (@lem1530651 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1530653 : term308 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1530654 : term307 = False.
Proof. exact (TRANS (@lem1530652) (@lem1530653)). Qed.
Lemma lem1530655 (x : real) (y : real) (z : real) (h1 : term256 x y z) : False.
Proof. exact (EQ_MP (@lem1530654) (@lem1530649 x y z h1)). Qed.
Lemma lem1530656 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term280 x y z.
Proof. exact (h1). Qed.
Lemma lem1530657 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term278 x y z.
Proof. exact (proj2 (@lem1530656 x y z h1)). Qed.
Lemma lem1530659 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term277 y z.
Proof. exact (proj2 (@lem1530657 x y z h1)). Qed.
Lemma lem1530660 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term192 x y z.
Proof. exact (proj1 (@lem1530657 x y z h1)). Qed.
Lemma lem1530661 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term191 x y z.
Proof. exact (proj2 (@lem1530660 x y z h1)). Qed.
Lemma lem1530665 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term173 y z.
Proof. exact (proj2 (@lem1530661 x y z h1)). Qed.
Lemma lem1530668 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530669 : term284 = term285.
Proof. exact (@lem1530668 (NUMERAL 0) term107). Qed.
Lemma lem1530670 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1530671 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1530672 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1530671 h1) (fun h1 : term285 = True => @lem1530670)). Qed.
Lemma lem1530673 : term285 = True.
Proof. exact (EQ_MP (@lem1530672) (@lem1530670)). Qed.
Lemma lem1530674 : term284 = True.
Proof. exact (TRANS (@lem1530669) (@lem1530673)). Qed.
Lemma lem1530675 : True = term284.
Proof. exact (SYM (@lem1530674)). Qed.
Lemma lem1530676 : term284.
Proof. exact (EQ_MP (@lem1530675) (@lem0)). Qed.
Lemma lem1530677 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term309 y z.
Proof. exact (conj (@lem1530676) (@lem1530665 x y z h1)). Qed.
Lemma lem1530679 (x : real) (y : real) : term288 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1530680 (y : real) (z : real) : term310 y z.
Proof. exact (@lem1530679 term137 (real_add y z)). Qed.
Lemma lem1530681 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term311 y z.
Proof. exact (@lem1530680 y z (@lem1530677 x y z h1)). Qed.
Lemma lem1530682 (y : real) (z : real) : (term312 y z) = (real_add y z).
Proof. exact (@lem1483460 (real_add y z)). Qed.
Lemma lem1530683 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530684 (y : real) (z : real) : (term313 y z) = (term171 y z).
Proof. exact (MK_COMB (@lem1530683) (@lem1530682 y z)). Qed.
Lemma lem1530685 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530686 (y : real) (z : real) : (term311 y z) = (term173 y z).
Proof. exact (MK_COMB (@lem1530684 y z) (@lem1530685)). Qed.
Lemma lem1530687 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term173 y z.
Proof. exact (EQ_MP (@lem1530686 y z) (@lem1530681 x y z h1)). Qed.
Lemma lem1530689 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530690 : term284 = term285.
Proof. exact (@lem1530689 (NUMERAL 0) term107). Qed.
Lemma lem1530691 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1530692 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1530693 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1530692 h1) (fun h1 : term285 = True => @lem1530691)). Qed.
Lemma lem1530694 : term285 = True.
Proof. exact (EQ_MP (@lem1530693) (@lem1530691)). Qed.
Lemma lem1530695 : term284 = True.
Proof. exact (TRANS (@lem1530690) (@lem1530694)). Qed.
Lemma lem1530696 : True = term284.
Proof. exact (SYM (@lem1530695)). Qed.
Lemma lem1530697 : term284.
Proof. exact (EQ_MP (@lem1530696) (@lem0)). Qed.
Lemma lem1530698 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term314 y z.
Proof. exact (conj (@lem1530697) (@lem1530659 x y z h1)). Qed.
Lemma lem1530700 (x : real) (y : real) : term293 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1530701 (y : real) (z : real) : term315 y z.
Proof. exact (@lem1530700 term137 (term267 y z)). Qed.
Lemma lem1530702 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term316 y z.
Proof. exact (@lem1530701 y z (@lem1530698 x y z h1)). Qed.
Lemma lem1530703 (y : real) (z : real) : (term317 y z) = (term267 y z).
Proof. exact (@lem1483460 (term267 y z)). Qed.
Lemma lem1530704 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530705 (y : real) (z : real) : (term318 y z) = (term276 y z).
Proof. exact (MK_COMB (@lem1530704) (@lem1530703 y z)). Qed.
Lemma lem1530706 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530707 (y : real) (z : real) : (term316 y z) = (term277 y z).
Proof. exact (MK_COMB (@lem1530705 y z) (@lem1530706)). Qed.
Lemma lem1530708 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term277 y z.
Proof. exact (EQ_MP (@lem1530707 y z) (@lem1530702 x y z h1)). Qed.
Lemma lem1530709 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term319 y z.
Proof. exact (conj (@lem1530708 x y z h1) (@lem1530687 x y z h1)). Qed.
Lemma lem1530711 (x : real) (y : real) : term299 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1530712 (y : real) (z : real) : term320 y z.
Proof. exact (@lem1530711 (term267 y z) (real_add y z)). Qed.
Lemma lem1530713 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term321 y z.
Proof. exact (@lem1530712 y z (@lem1530709 x y z h1)). Qed.
Lemma lem1530714 (y : real) (z : real) : (term322 y z) = (term323 y z).
Proof. exact (@lem1483480 (term51 y) y (term51 z) z). Qed.
Lemma lem1530715 (y : real) : (term145 y) = (term146 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1530717 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530718 : term148 = term44.
Proof. exact (@lem1530717 term107). Qed.
Lemma lem1530719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530720 : term149 = term150.
Proof. exact (MK_COMB (@lem1530719) (@lem1530718)). Qed.
Lemma lem1530721 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1530722 (y : real) : (term146 y) = (term151 y).
Proof. exact (MK_COMB (@lem1530720) (@lem1530721 y)). Qed.
Lemma lem1530723 (y : real) : (term145 y) = (term151 y).
Proof. exact (TRANS (@lem1530715 y) (@lem1530722 y)). Qed.
Lemma lem1530724 (y : real) : (term151 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1530725 (y : real) : (term145 y) = term44.
Proof. exact (TRANS (@lem1530723 y) (@lem1530724 y)). Qed.
Lemma lem1530726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1530727 (y : real) : (term152 y) = term153.
Proof. exact (MK_COMB (@lem1530726) (@lem1530725 y)). Qed.
Lemma lem1530728 (z : real) : (term145 z) = (term146 z).
Proof. exact (@lem1483440 term39 z). Qed.
Lemma lem1530730 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1530731 : term148 = term44.
Proof. exact (@lem1530730 term107). Qed.
Lemma lem1530732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1530733 : term149 = term150.
Proof. exact (MK_COMB (@lem1530732) (@lem1530731)). Qed.
Lemma lem1530734 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1530735 (z : real) : (term146 z) = (term151 z).
Proof. exact (MK_COMB (@lem1530733) (@lem1530734 z)). Qed.
Lemma lem1530736 (z : real) : (term145 z) = (term151 z).
Proof. exact (TRANS (@lem1530728 z) (@lem1530735 z)). Qed.
Lemma lem1530737 (z : real) : (term151 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1530738 (z : real) : (term145 z) = term44.
Proof. exact (TRANS (@lem1530736 z) (@lem1530737 z)). Qed.
Lemma lem1530739 (y : real) (z : real) : (term323 y z) = term304.
Proof. exact (MK_COMB (@lem1530727 y) (@lem1530738 z)). Qed.
Lemma lem1530740 (y : real) (z : real) : (term322 y z) = term304.
Proof. exact (TRANS (@lem1530714 y z) (@lem1530739 y z)). Qed.
Lemma lem1530741 : term304 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1530742 (y : real) (z : real) : (term322 y z) = term44.
Proof. exact (TRANS (@lem1530740 y z) (@lem1530741)). Qed.
Lemma lem1530743 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530744 (y : real) (z : real) : (term324 y z) = term306.
Proof. exact (MK_COMB (@lem1530743) (@lem1530742 y z)). Qed.
Lemma lem1530745 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530746 (y : real) (z : real) : (term321 y z) = term307.
Proof. exact (MK_COMB (@lem1530744 y z) (@lem1530745)). Qed.
Lemma lem1530747 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term307.
Proof. exact (EQ_MP (@lem1530746 y z) (@lem1530713 x y z h1)). Qed.
Lemma lem1530749 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1530750 : term307 = term308.
Proof. exact (@lem1530749 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1530751 : term308 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1530752 : term307 = False.
Proof. exact (TRANS (@lem1530750) (@lem1530751)). Qed.
Lemma lem1530753 (x : real) (y : real) (z : real) (h1 : term280 x y z) : False.
Proof. exact (EQ_MP (@lem1530752) (@lem1530747 x y z h1)). Qed.
Lemma lem1530754 (x : real) (y : real) (z : real) (h1 : term282 x y z) : False.
Proof. exact (or_elim (@lem1530557 x y z h1) (fun h0 : term256 x y z => @lem1530655 x y z h0) (fun h0 : term280 x y z => @lem1530753 x y z h0)). Qed.
Lemma lem1530755 (x : real) (z : real) (y : real) (h1 : term57 x z y) : term57 x z y.
Proof. exact (h1). Qed.
Lemma lem1530756 (x : real) (z : real) (y : real) (h1 : term57 x z y) : term282 x y z.
Proof. exact (EQ_MP (@lem1530556 x y z) (@lem1530755 x z y h1)). Qed.
Lemma lem1530757 (x : real) (z : real) (y : real) (h1 : term57 x z y) : (term282 x y z) = False.
Proof. exact (prop_ext (fun h2 : term282 x y z => @lem1530754 x y z h2) (fun h2 : False => @lem1530756 x z y h1)). Qed.
Lemma lem1530758 (x : real) (z : real) (y : real) (h1 : term57 x z y) : False.
Proof. exact (EQ_MP (@lem1530757 x z y h1) (@lem1530756 x z y h1)). Qed.
Lemma lem1530759 (x : real) (y : real) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem1530760 (x : real) (y : real) (h1 : term59 x y) : False.
Proof. exact (ex_elim (@lem1530759 x y h1) (fun z : real => fun h0 : term58 x y z => @lem1530758 x z y h0)). Qed.
Lemma lem1530761 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (h1). Qed.
Lemma lem1530762 (x : real) (h1 : term61 x) : False.
Proof. exact (ex_elim (@lem1530761 x h1) (fun y : real => fun h0 : term60 x y => @lem1530760 x y h0)). Qed.
Lemma lem1530763 (h1 : term63) : term63.
Proof. exact (h1). Qed.
Lemma lem1530764 (h1 : term63) : False.
Proof. exact (ex_elim (@lem1530763 h1) (fun x : real => fun h0 : term62 x => @lem1530762 x h0)). Qed.
Lemma lem1530765 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1530766 (h1 : term24) : term63.
Proof. exact (EQ_MP (@lem1529860) (@lem1530765 h1)). Qed.
Lemma lem1530767 (h1 : term24) : term63 = False.
Proof. exact (prop_ext (fun h2 : term63 => @lem1530764 h2) (fun h2 : False => @lem1530766 h1)). Qed.
Lemma lem1530768 (h1 : term24) : False.
Proof. exact (EQ_MP (@lem1530767 h1) (@lem1530766 h1)). Qed.
Lemma lem1530769 : term325.
Proof. exact (fun h0 : term24 => @lem1530768 h0). Qed.
Lemma lem1530770 : term326.
Proof. exact (@lem1386578 term327). Qed.
Lemma lem1530771 : term327.
Proof. exact (@lem1530770 (@lem1530769)). Qed.
