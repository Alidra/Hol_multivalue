Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_TRIANGLE_LT_term_abbrevs.
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
Require Import thm1482705_spec.
Require Import thm1482706_spec.
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
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1530795 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17362 (term2 y x z) (term3 y z)). Qed.
Lemma lem1530796 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1530797 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1530796 (term8 x y)). Qed.
Lemma lem1530798 (x : real) (y : real) (z : real) : (term9 x y z) = (term10 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1530799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1530800 (x : real) (y : real) (z : real) : (term11 x y z) = (term0 x y z).
Proof. exact (MK_COMB (@lem1530799) (@lem1530798 x y z)). Qed.
Lemma lem1530801 (x : real) (y : real) (z : real) : (term11 x y z) = (term1 x y z).
Proof. exact (TRANS (@lem1530800 x y z) (@lem1530795 x y z)). Qed.
Lemma lem1530802 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (fun_ext (fun z : real => @lem1530801 x y z)). Qed.
Lemma lem1530803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530804 (x : real) (y : real) : (term7 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1530803) (@lem1530802 x y)). Qed.
Lemma lem1530805 (x : real) (y : real) : (term6 x y) = (term14 x y).
Proof. exact (TRANS (@lem1530797 x y) (@lem1530804 x y)). Qed.
Lemma lem1530806 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1530807 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1530806 (term17 x)). Qed.
Lemma lem1530808 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1530809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1530810 (x : real) (y : real) : (term20 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1530809) (@lem1530808 x y)). Qed.
Lemma lem1530811 (x : real) (y : real) : (term20 x y) = (term14 x y).
Proof. exact (TRANS (@lem1530810 x y) (@lem1530805 x y)). Qed.
Lemma lem1530812 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1530811 x y)). Qed.
Lemma lem1530813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530814 (x : real) : (term16 x) = (term23 x).
Proof. exact (MK_COMB (@lem1530813) (@lem1530812 x)). Qed.
Lemma lem1530815 (x : real) : (term15 x) = (term23 x).
Proof. exact (TRANS (@lem1530807 x) (@lem1530814 x)). Qed.
Lemma lem1530816 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1530817 : term24 = term25.
Proof. exact (@lem1530816 term26). Qed.
Lemma lem1530818 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1530819 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1530820 (x : real) : (term29 x) = (term15 x).
Proof. exact (MK_COMB (@lem1530819) (@lem1530818 x)). Qed.
Lemma lem1530821 (x : real) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem1530820 x) (@lem1530815 x)). Qed.
Lemma lem1530822 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1530821 x)). Qed.
Lemma lem1530823 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530824 : term25 = term32.
Proof. exact (MK_COMB (@lem1530823) (@lem1530822)). Qed.
Lemma lem1530826 : term24 = term32.
Proof. exact (TRANS (@lem1530817) (@lem1530824)). Qed.
Lemma lem1530833 (x : real) (y : real) (z : real) : (term1 x y z) = (term1 x y z).
Proof. exact (eq_refl (term1 x y z)). Qed.
Lemma lem1530834 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (fun_ext (fun z : real => @lem1530833 x y z)). Qed.
Lemma lem1530835 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530836 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1530835) (@lem1530834 x y)). Qed.
Lemma lem1530837 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1530836 x y)). Qed.
Lemma lem1530838 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530839 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1530838) (@lem1530837 x)). Qed.
Lemma lem1530840 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1530839 x)). Qed.
Lemma lem1530841 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530842 : term32 = term32.
Proof. exact (MK_COMB (@lem1530841) (@lem1530840)). Qed.
Lemma lem1530843 : term24 = term32.
Proof. exact (TRANS (@lem1530826) (@lem1530842)). Qed.
Lemma lem1530844 (z : real) (y : real) (x : real) : (term2 y x z) = (term33 z y x).
Proof. exact (@lem1483521 z (term34 y x)). Qed.
Lemma lem1530856 (z : real) (y : real) (x : real) : (term35 z y x) = (term36 z y x).
Proof. exact (@lem1483519 z (term34 y x)). Qed.
Lemma lem1530863 (y : real) (x : real) : (term37 y x) = (term38 y x).
Proof. exact (@lem1483508 (real_abs x) term39 (term40 y x)). Qed.
Lemma lem1530864 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1530867 (z : real) (y : real) (x : real) : (term36 z y x) = (term41 z y x).
Proof. exact (MK_COMB (@lem1530864 z) (@lem1530863 y x)). Qed.
Lemma lem1530869 (z : real) (y : real) (x : real) : (term35 z y x) = (term41 z y x).
Proof. exact (TRANS (@lem1530856 z y x) (@lem1530867 z y x)). Qed.
Lemma lem1530870 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1530871 (z : real) (y : real) (x : real) : (term42 z y x) = (term43 z y x).
Proof. exact (MK_COMB (@lem1530870) (@lem1530869 z y x)). Qed.
Lemma lem1530872 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530873 (z : real) (y : real) (x : real) : (term33 z y x) = (term45 z y x).
Proof. exact (MK_COMB (@lem1530871 z y x) (@lem1530872)). Qed.
Lemma lem1530874 (z : real) (y : real) (x : real) : (term2 y x z) = (term45 z y x).
Proof. exact (TRANS (@lem1530844 z y x) (@lem1530873 z y x)). Qed.
Lemma lem1530875 (y : real) (z : real) : (term46 y z) = (term47 y z).
Proof. exact (@lem1483531 (real_abs y) z). Qed.
Lemma lem1530881 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483519 (real_abs y) z). Qed.
Lemma lem1530886 (z : real) (y : real) : (term49 y z) = (term50 z y).
Proof. exact (@lem1483488 (term51 z) (real_abs y)). Qed.
Lemma lem1530888 (z : real) (y : real) : (term48 y z) = (term50 z y).
Proof. exact (TRANS (@lem1530881 y z) (@lem1530886 z y)). Qed.
Lemma lem1530889 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1530890 (z : real) (y : real) : (term52 y z) = (term53 z y).
Proof. exact (MK_COMB (@lem1530889) (@lem1530888 z y)). Qed.
Lemma lem1530891 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1530892 (z : real) (y : real) : (term47 y z) = (term54 z y).
Proof. exact (MK_COMB (@lem1530890 z y) (@lem1530891)). Qed.
Lemma lem1530893 (z : real) (y : real) : (term46 y z) = (term54 z y).
Proof. exact (TRANS (@lem1530875 y z) (@lem1530892 z y)). Qed.
Lemma lem1530894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1530895 (z : real) (y : real) (x : real) : (term55 y x z) = (term56 z y x).
Proof. exact (MK_COMB (@lem1530894) (@lem1530874 z y x)). Qed.
Lemma lem1530896 (x : real) (z : real) (y : real) : (term1 x y z) = (term57 x z y).
Proof. exact (MK_COMB (@lem1530895 z y x) (@lem1530893 z y)). Qed.
Lemma lem1530897 (x : real) (y : real) : (term13 x y) = (term58 x y).
Proof. exact (fun_ext (fun z : real => @lem1530896 x z y)). Qed.
Lemma lem1530898 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530899 (x : real) (y : real) : (term14 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1530898) (@lem1530897 x y)). Qed.
Lemma lem1530900 (x : real) : (term22 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1530899 x y)). Qed.
Lemma lem1530901 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530902 (x : real) : (term23 x) = (term61 x).
Proof. exact (MK_COMB (@lem1530901) (@lem1530900 x)). Qed.
Lemma lem1530903 : term31 = term62.
Proof. exact (fun_ext (fun x : real => @lem1530902 x)). Qed.
Lemma lem1530904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530905 : term32 = term63.
Proof. exact (MK_COMB (@lem1530904) (@lem1530903)). Qed.
Lemma lem1530968 : term24 = term63.
Proof. exact (TRANS (@lem1530843) (@lem1530905)). Qed.
Lemma lem1530975 (x : real) (z : real) (y : real) : (term57 x z y) = (term57 x z y).
Proof. exact (eq_refl (term57 x z y)). Qed.
Lemma lem1530976 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (fun_ext (fun z : real => @lem1530975 x z y)). Qed.
Lemma lem1530977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530978 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1530977) (@lem1530976 x y)). Qed.
Lemma lem1530979 (x : real) : (term60 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1530978 x y)). Qed.
Lemma lem1530980 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530981 (x : real) : (term61 x) = (term61 x).
Proof. exact (MK_COMB (@lem1530980) (@lem1530979 x)). Qed.
Lemma lem1530982 : term62 = term62.
Proof. exact (fun_ext (fun x : real => @lem1530981 x)). Qed.
Lemma lem1530983 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1530984 : term63 = term63.
Proof. exact (MK_COMB (@lem1530983) (@lem1530982)). Qed.
Lemma lem1530985 : term24 = term63.
Proof. exact (TRANS (@lem1530968) (@lem1530984)). Qed.
Lemma lem1530987 (a : real) (x : real) (b : real) (r : real) : (term64 a x b r) = (term65 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1530988 (z : real) (y : real) (x : real) : (term45 z y x) = (term66 z y x).
Proof. exact (@lem1530987 z x (term67 y x) term44). Qed.
Lemma lem1530995 (y : real) (x : real) : (term67 y x) = (term67 y x).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1531002 (x : real) : (term68 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1531003 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531004 (x : real) : (term69 x) = (real_add x).
Proof. exact (MK_COMB (@lem1531003) (@lem1531002 x)). Qed.
Lemma lem1531007 (y : real) (x : real) : (term70 y x) = (term71 y x).
Proof. exact (MK_COMB (@lem1531004 x) (@lem1530995 y x)). Qed.
Lemma lem1531010 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1531011 (z : real) (y : real) (x : real) : (term72 z y x) = (term73 z y x).
Proof. exact (MK_COMB (@lem1531010 z) (@lem1531007 y x)). Qed.
Lemma lem1531016 (z : real) (y : real) (x : real) : (term73 z y x) = (term74 z y x).
Proof. exact (@lem1483484 x z (term67 y x)). Qed.
Lemma lem1531017 (z : real) (y : real) (x : real) : (term72 z y x) = (term74 z y x).
Proof. exact (TRANS (@lem1531011 z y x) (@lem1531016 z y x)). Qed.
Lemma lem1531018 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531019 (z : real) (y : real) (x : real) : (term75 z y x) = (term76 z y x).
Proof. exact (MK_COMB (@lem1531018) (@lem1531017 z y x)). Qed.
Lemma lem1531020 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531021 (z : real) (y : real) (x : real) : (term77 z y x) = (term78 z y x).
Proof. exact (MK_COMB (@lem1531019 z y x) (@lem1531020)). Qed.
Lemma lem1531050 (z : real) (y : real) (x : real) : (term79 z y x) = (term80 z y x).
Proof. exact (@lem1483484 (term51 x) z (term67 y x)). Qed.
Lemma lem1531051 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531052 (z : real) (y : real) (x : real) : (term81 z y x) = (term82 z y x).
Proof. exact (MK_COMB (@lem1531051) (@lem1531050 z y x)). Qed.
Lemma lem1531053 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531054 (z : real) (y : real) (x : real) : (term83 z y x) = (term84 z y x).
Proof. exact (MK_COMB (@lem1531052 z y x) (@lem1531053)). Qed.
Lemma lem1531055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531056 (z : real) (y : real) (x : real) : (term85 z y x) = (term86 z y x).
Proof. exact (MK_COMB (@lem1531055) (@lem1531054 z y x)). Qed.
Lemma lem1531057 (z : real) (y : real) (x : real) : (term66 z y x) = (term87 z y x).
Proof. exact (MK_COMB (@lem1531056 z y x) (@lem1531021 z y x)). Qed.
Lemma lem1531058 (z : real) (y : real) (x : real) : (term45 z y x) = (term87 z y x).
Proof. exact (TRANS (@lem1530988 z y x) (@lem1531057 z y x)). Qed.
Lemma lem1531060 (a : real) (b : real) (x : real) (r : real) : (term88 a b x r) = (term89 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1531061 (z : real) (y : real) (x : real) : (term84 z y x) = (term90 z y x).
Proof. exact (@lem1531060 (term51 x) z (real_sub y x) term44). Qed.
Lemma lem1531067 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1531072 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1531074 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1531067 y x) (@lem1531072 x y)). Qed.
Lemma lem1531077 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1531078 (x : real) (y : real) : (term94 y x) = (term95 x y).
Proof. exact (MK_COMB (@lem1531077) (@lem1531074 x y)). Qed.
Lemma lem1531079 (x : real) (y : real) : (term95 x y) = (term92 x y).
Proof. exact (@lem1483460 (term92 x y)). Qed.
Lemma lem1531080 (x : real) (y : real) : (term94 y x) = (term92 x y).
Proof. exact (TRANS (@lem1531078 x y) (@lem1531079 x y)). Qed.
Lemma lem1531083 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1531084 (z : real) (x : real) (y : real) : (term96 z y x) = (term97 z x y).
Proof. exact (MK_COMB (@lem1531083 z) (@lem1531080 x y)). Qed.
Lemma lem1531085 (x : real) (z : real) (y : real) : (term97 z x y) = (term98 x z y).
Proof. exact (@lem1483484 (term51 x) z y). Qed.
Lemma lem1531086 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1531087 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1531088 (x : real) (y : real) (z : real) : (term98 x z y) = (term98 x y z).
Proof. exact (MK_COMB (@lem1531087 x) (@lem1531086 y z)). Qed.
Lemma lem1531089 (x : real) (y : real) (z : real) : (term97 z x y) = (term98 x y z).
Proof. exact (TRANS (@lem1531085 x z y) (@lem1531088 x y z)). Qed.
Lemma lem1531090 (x : real) (y : real) (z : real) : (term96 z y x) = (term98 x y z).
Proof. exact (TRANS (@lem1531084 z x y) (@lem1531089 x y z)). Qed.
Lemma lem1531099 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1531100 (x : real) (y : real) (z : real) : (term100 z y x) = (term101 x y z).
Proof. exact (MK_COMB (@lem1531099 x) (@lem1531090 x y z)). Qed.
Lemma lem1531101 (x : real) (y : real) (z : real) : (term101 x y z) = (term102 x y z).
Proof. exact (@lem1483490 (term51 x) (term51 x) (real_add y z)). Qed.
Lemma lem1531102 (x : real) : (term103 x) = (term104 x).
Proof. exact (@lem1483438 term39 term39 x). Qed.
Lemma lem1531103 : term105 = term106.
Proof. exact (@lem1367763 term107 term107). Qed.
Lemma lem1531104 : term108 = term109.
Proof. exact (@lem706885). Qed.
Lemma lem1531105 : (term108 = term109) = (term110 = term111).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term109). Qed.
Lemma lem1531106 : term110 = term111.
Proof. exact (EQ_MP (@lem1531105) (@lem1531104)). Qed.
Lemma lem1531107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1531108 : term112 = term113.
Proof. exact (MK_COMB (@lem1531107) (@lem1531106)). Qed.
Lemma lem1531109 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1531110 : term106 = term114.
Proof. exact (MK_COMB (@lem1531109) (@lem1531108)). Qed.
Lemma lem1531111 : term105 = term114.
Proof. exact (TRANS (@lem1531103) (@lem1531110)). Qed.
Lemma lem1531112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531113 : term115 = term116.
Proof. exact (MK_COMB (@lem1531112) (@lem1531111)). Qed.
Lemma lem1531114 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531115 (x : real) : (term104 x) = (term117 x).
Proof. exact (MK_COMB (@lem1531113) (@lem1531114 x)). Qed.
Lemma lem1531116 (x : real) : (term103 x) = (term117 x).
Proof. exact (TRANS (@lem1531102 x) (@lem1531115 x)). Qed.
Lemma lem1531117 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531118 (x : real) : (term118 x) = (term119 x).
Proof. exact (MK_COMB (@lem1531117) (@lem1531116 x)). Qed.
Lemma lem1531119 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (eq_refl (real_add y z)). Qed.
Lemma lem1531120 (x : real) (y : real) (z : real) : (term102 x y z) = (term120 x y z).
Proof. exact (MK_COMB (@lem1531118 x) (@lem1531119 y z)). Qed.
Lemma lem1531121 (x : real) (y : real) (z : real) : (term101 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1531101 x y z) (@lem1531120 x y z)). Qed.
Lemma lem1531122 (x : real) (y : real) (z : real) : (term100 z y x) = (term120 x y z).
Proof. exact (TRANS (@lem1531100 x y z) (@lem1531121 x y z)). Qed.
Lemma lem1531123 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531124 (x : real) (y : real) (z : real) : (term121 z y x) = (term122 x y z).
Proof. exact (MK_COMB (@lem1531123) (@lem1531122 x y z)). Qed.
Lemma lem1531125 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531126 (x : real) (y : real) (z : real) : (term123 z y x) = (term124 x y z).
Proof. exact (MK_COMB (@lem1531124 x y z) (@lem1531125)). Qed.
Lemma lem1531132 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1531137 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1531139 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1531132 y x) (@lem1531137 x y)). Qed.
Lemma lem1531142 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem1531143 (x : real) (y : real) : (term126 y x) = (term127 x y).
Proof. exact (MK_COMB (@lem1531142) (@lem1531139 x y)). Qed.
Lemma lem1531144 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (@lem1483508 (term51 x) term39 y). Qed.
Lemma lem1531145 (y : real) : (term51 y) = (term51 y).
Proof. exact (eq_refl (term51 y)). Qed.
Lemma lem1531146 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1531148 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1531149 : term133 = term134.
Proof. exact (@lem1531148 term107 term107). Qed.
Lemma lem1531150 : (term135 = (BIT1 0)) = (term136 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1531151 : term136 = term107.
Proof. exact (EQ_MP (@lem1531150) (@lem940073)). Qed.
Lemma lem1531152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1531153 : term134 = term137.
Proof. exact (MK_COMB (@lem1531152) (@lem1531151)). Qed.
Lemma lem1531154 : term133 = term137.
Proof. exact (TRANS (@lem1531149) (@lem1531153)). Qed.
Lemma lem1531155 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531156 : term138 = term93.
Proof. exact (MK_COMB (@lem1531155) (@lem1531154)). Qed.
Lemma lem1531157 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531158 (x : real) : (term130 x) = (term68 x).
Proof. exact (MK_COMB (@lem1531156) (@lem1531157 x)). Qed.
Lemma lem1531159 (x : real) : (term129 x) = (term68 x).
Proof. exact (TRANS (@lem1531146 x) (@lem1531158 x)). Qed.
Lemma lem1531160 (x : real) : (term68 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1531161 (x : real) : (term129 x) = x.
Proof. exact (TRANS (@lem1531159 x) (@lem1531160 x)). Qed.
Lemma lem1531162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531163 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1531162) (@lem1531161 x)). Qed.
Lemma lem1531164 (x : real) (y : real) : (term128 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1531163 x) (@lem1531145 y)). Qed.
Lemma lem1531165 (x : real) (y : real) : (term127 x y) = (term91 x y).
Proof. exact (TRANS (@lem1531144 x y) (@lem1531164 x y)). Qed.
Lemma lem1531166 (x : real) (y : real) : (term126 y x) = (term91 x y).
Proof. exact (TRANS (@lem1531143 x y) (@lem1531165 x y)). Qed.
Lemma lem1531169 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1531170 (z : real) (x : real) (y : real) : (term140 z y x) = (term141 z x y).
Proof. exact (MK_COMB (@lem1531169 z) (@lem1531166 x y)). Qed.
Lemma lem1531171 (x : real) (z : real) (y : real) : (term141 z x y) = (term141 x z y).
Proof. exact (@lem1483484 x z (term51 y)). Qed.
Lemma lem1531172 (y : real) (z : real) : (term91 z y) = (term92 y z).
Proof. exact (@lem1483488 (term51 y) z). Qed.
Lemma lem1531173 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1531174 (x : real) (y : real) (z : real) : (term141 x z y) = (term97 x y z).
Proof. exact (MK_COMB (@lem1531173 x) (@lem1531172 y z)). Qed.
Lemma lem1531175 (x : real) (y : real) (z : real) : (term141 z x y) = (term97 x y z).
Proof. exact (TRANS (@lem1531171 x z y) (@lem1531174 x y z)). Qed.
Lemma lem1531176 (x : real) (y : real) (z : real) : (term140 z y x) = (term97 x y z).
Proof. exact (TRANS (@lem1531170 z x y) (@lem1531175 x y z)). Qed.
Lemma lem1531185 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1531186 (x : real) (y : real) (z : real) : (term142 z y x) = (term143 x y z).
Proof. exact (MK_COMB (@lem1531185 x) (@lem1531176 x y z)). Qed.
Lemma lem1531187 (x : real) (y : real) (z : real) : (term143 x y z) = (term144 x y z).
Proof. exact (@lem1483490 (term51 x) x (term92 y z)). Qed.
Lemma lem1531188 (x : real) : (term145 x) = (term146 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1531190 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531191 : term148 = term44.
Proof. exact (@lem1531190 term107). Qed.
Lemma lem1531192 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531193 : term149 = term150.
Proof. exact (MK_COMB (@lem1531192) (@lem1531191)). Qed.
Lemma lem1531194 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531195 (x : real) : (term146 x) = (term151 x).
Proof. exact (MK_COMB (@lem1531193) (@lem1531194 x)). Qed.
Lemma lem1531196 (x : real) : (term145 x) = (term151 x).
Proof. exact (TRANS (@lem1531188 x) (@lem1531195 x)). Qed.
Lemma lem1531197 (x : real) : (term151 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1531198 (x : real) : (term145 x) = term44.
Proof. exact (TRANS (@lem1531196 x) (@lem1531197 x)). Qed.
Lemma lem1531199 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531200 (x : real) : (term152 x) = term153.
Proof. exact (MK_COMB (@lem1531199) (@lem1531198 x)). Qed.
Lemma lem1531201 (y : real) (z : real) : (term92 y z) = (term92 y z).
Proof. exact (eq_refl (term92 y z)). Qed.
Lemma lem1531202 (x : real) (y : real) (z : real) : (term144 x y z) = (term154 y z).
Proof. exact (MK_COMB (@lem1531200 x) (@lem1531201 y z)). Qed.
Lemma lem1531203 (x : real) (y : real) (z : real) : (term143 x y z) = (term154 y z).
Proof. exact (TRANS (@lem1531187 x y z) (@lem1531202 x y z)). Qed.
Lemma lem1531204 (y : real) (z : real) : (term154 y z) = (term92 y z).
Proof. exact (@lem1483448 (term92 y z)). Qed.
Lemma lem1531205 (x : real) (y : real) (z : real) : (term143 x y z) = (term92 y z).
Proof. exact (TRANS (@lem1531203 x y z) (@lem1531204 y z)). Qed.
Lemma lem1531206 (x : real) (y : real) (z : real) : (term142 z y x) = (term92 y z).
Proof. exact (TRANS (@lem1531186 x y z) (@lem1531205 x y z)). Qed.
Lemma lem1531207 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531208 (x : real) (y : real) (z : real) : (term155 z y x) = (term156 y z).
Proof. exact (MK_COMB (@lem1531207) (@lem1531206 x y z)). Qed.
Lemma lem1531209 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531210 (x : real) (y : real) (z : real) : (term157 z y x) = (term158 y z).
Proof. exact (MK_COMB (@lem1531208 x y z) (@lem1531209)). Qed.
Lemma lem1531211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531212 (x : real) (y : real) (z : real) : (term159 z y x) = (term160 y z).
Proof. exact (MK_COMB (@lem1531211) (@lem1531210 x y z)). Qed.
Lemma lem1531213 (x : real) (y : real) (z : real) : (term90 z y x) = (term161 x y z).
Proof. exact (MK_COMB (@lem1531212 x y z) (@lem1531126 x y z)). Qed.
Lemma lem1531214 (x : real) (y : real) (z : real) : (term84 z y x) = (term161 x y z).
Proof. exact (TRANS (@lem1531061 z y x) (@lem1531213 x y z)). Qed.
Lemma lem1531215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531216 (x : real) (y : real) (z : real) : (term86 z y x) = (term162 x y z).
Proof. exact (MK_COMB (@lem1531215) (@lem1531214 x y z)). Qed.
Lemma lem1531218 (a : real) (b : real) (x : real) (r : real) : (term88 a b x r) = (term89 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1531219 (z : real) (y : real) (x : real) : (term78 z y x) = (term163 z y x).
Proof. exact (@lem1531218 x z (real_sub y x) term44). Qed.
Lemma lem1531225 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1531230 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1531232 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1531225 y x) (@lem1531230 x y)). Qed.
Lemma lem1531235 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1531236 (x : real) (y : real) : (term94 y x) = (term95 x y).
Proof. exact (MK_COMB (@lem1531235) (@lem1531232 x y)). Qed.
Lemma lem1531237 (x : real) (y : real) : (term95 x y) = (term92 x y).
Proof. exact (@lem1483460 (term92 x y)). Qed.
Lemma lem1531238 (x : real) (y : real) : (term94 y x) = (term92 x y).
Proof. exact (TRANS (@lem1531236 x y) (@lem1531237 x y)). Qed.
Lemma lem1531241 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1531242 (z : real) (x : real) (y : real) : (term96 z y x) = (term97 z x y).
Proof. exact (MK_COMB (@lem1531241 z) (@lem1531238 x y)). Qed.
Lemma lem1531243 (x : real) (z : real) (y : real) : (term97 z x y) = (term98 x z y).
Proof. exact (@lem1483484 (term51 x) z y). Qed.
Lemma lem1531244 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1531245 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1531246 (x : real) (y : real) (z : real) : (term98 x z y) = (term98 x y z).
Proof. exact (MK_COMB (@lem1531245 x) (@lem1531244 y z)). Qed.
Lemma lem1531247 (x : real) (y : real) (z : real) : (term97 z x y) = (term98 x y z).
Proof. exact (TRANS (@lem1531243 x z y) (@lem1531246 x y z)). Qed.
Lemma lem1531248 (x : real) (y : real) (z : real) : (term96 z y x) = (term98 x y z).
Proof. exact (TRANS (@lem1531242 z x y) (@lem1531247 x y z)). Qed.
Lemma lem1531251 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1531252 (x : real) (y : real) (z : real) : (term164 z y x) = (term165 x y z).
Proof. exact (MK_COMB (@lem1531251 x) (@lem1531248 x y z)). Qed.
Lemma lem1531253 (x : real) (y : real) (z : real) : (term165 x y z) = (term166 x y z).
Proof. exact (@lem1483490 x (term51 x) (real_add y z)). Qed.
Lemma lem1531254 (x : real) : (term167 x) = (term146 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1531256 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531257 : term148 = term44.
Proof. exact (@lem1531256 term107). Qed.
Lemma lem1531258 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531259 : term149 = term150.
Proof. exact (MK_COMB (@lem1531258) (@lem1531257)). Qed.
Lemma lem1531260 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531261 (x : real) : (term146 x) = (term151 x).
Proof. exact (MK_COMB (@lem1531259) (@lem1531260 x)). Qed.
Lemma lem1531262 (x : real) : (term167 x) = (term151 x).
Proof. exact (TRANS (@lem1531254 x) (@lem1531261 x)). Qed.
Lemma lem1531263 (x : real) : (term151 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1531264 (x : real) : (term167 x) = term44.
Proof. exact (TRANS (@lem1531262 x) (@lem1531263 x)). Qed.
Lemma lem1531265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531266 (x : real) : (term168 x) = term153.
Proof. exact (MK_COMB (@lem1531265) (@lem1531264 x)). Qed.
Lemma lem1531267 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (eq_refl (real_add y z)). Qed.
Lemma lem1531268 (x : real) (y : real) (z : real) : (term166 x y z) = (term169 y z).
Proof. exact (MK_COMB (@lem1531266 x) (@lem1531267 y z)). Qed.
Lemma lem1531269 (x : real) (y : real) (z : real) : (term165 x y z) = (term169 y z).
Proof. exact (TRANS (@lem1531253 x y z) (@lem1531268 x y z)). Qed.
Lemma lem1531270 (y : real) (z : real) : (term169 y z) = (real_add y z).
Proof. exact (@lem1483448 (real_add y z)). Qed.
Lemma lem1531271 (x : real) (y : real) (z : real) : (term165 x y z) = (real_add y z).
Proof. exact (TRANS (@lem1531269 x y z) (@lem1531270 y z)). Qed.
Lemma lem1531272 (x : real) (y : real) (z : real) : (term164 z y x) = (real_add y z).
Proof. exact (TRANS (@lem1531252 x y z) (@lem1531271 x y z)). Qed.
Lemma lem1531273 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531274 (x : real) (y : real) (z : real) : (term170 z y x) = (term171 y z).
Proof. exact (MK_COMB (@lem1531273) (@lem1531272 x y z)). Qed.
Lemma lem1531275 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531276 (x : real) (y : real) (z : real) : (term172 z y x) = (term173 y z).
Proof. exact (MK_COMB (@lem1531274 x y z) (@lem1531275)). Qed.
Lemma lem1531282 (y : real) (x : real) : (real_sub y x) = (term91 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1531287 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (@lem1483488 (term51 x) y). Qed.
Lemma lem1531289 (x : real) (y : real) : (real_sub y x) = (term92 x y).
Proof. exact (TRANS (@lem1531282 y x) (@lem1531287 x y)). Qed.
Lemma lem1531292 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem1531293 (x : real) (y : real) : (term126 y x) = (term127 x y).
Proof. exact (MK_COMB (@lem1531292) (@lem1531289 x y)). Qed.
Lemma lem1531294 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (@lem1483508 (term51 x) term39 y). Qed.
Lemma lem1531295 (y : real) : (term51 y) = (term51 y).
Proof. exact (eq_refl (term51 y)). Qed.
Lemma lem1531296 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1531298 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1531299 : term133 = term134.
Proof. exact (@lem1531298 term107 term107). Qed.
Lemma lem1531300 : (term135 = (BIT1 0)) = (term136 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1531301 : term136 = term107.
Proof. exact (EQ_MP (@lem1531300) (@lem940073)). Qed.
Lemma lem1531302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1531303 : term134 = term137.
Proof. exact (MK_COMB (@lem1531302) (@lem1531301)). Qed.
Lemma lem1531304 : term133 = term137.
Proof. exact (TRANS (@lem1531299) (@lem1531303)). Qed.
Lemma lem1531305 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531306 : term138 = term93.
Proof. exact (MK_COMB (@lem1531305) (@lem1531304)). Qed.
Lemma lem1531307 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531308 (x : real) : (term130 x) = (term68 x).
Proof. exact (MK_COMB (@lem1531306) (@lem1531307 x)). Qed.
Lemma lem1531309 (x : real) : (term129 x) = (term68 x).
Proof. exact (TRANS (@lem1531296 x) (@lem1531308 x)). Qed.
Lemma lem1531310 (x : real) : (term68 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1531311 (x : real) : (term129 x) = x.
Proof. exact (TRANS (@lem1531309 x) (@lem1531310 x)). Qed.
Lemma lem1531312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531313 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1531312) (@lem1531311 x)). Qed.
Lemma lem1531314 (x : real) (y : real) : (term128 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1531313 x) (@lem1531295 y)). Qed.
Lemma lem1531315 (x : real) (y : real) : (term127 x y) = (term91 x y).
Proof. exact (TRANS (@lem1531294 x y) (@lem1531314 x y)). Qed.
Lemma lem1531316 (x : real) (y : real) : (term126 y x) = (term91 x y).
Proof. exact (TRANS (@lem1531293 x y) (@lem1531315 x y)). Qed.
Lemma lem1531319 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1531320 (z : real) (x : real) (y : real) : (term140 z y x) = (term141 z x y).
Proof. exact (MK_COMB (@lem1531319 z) (@lem1531316 x y)). Qed.
Lemma lem1531321 (x : real) (z : real) (y : real) : (term141 z x y) = (term141 x z y).
Proof. exact (@lem1483484 x z (term51 y)). Qed.
Lemma lem1531322 (y : real) (z : real) : (term91 z y) = (term92 y z).
Proof. exact (@lem1483488 (term51 y) z). Qed.
Lemma lem1531323 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1531324 (x : real) (y : real) (z : real) : (term141 x z y) = (term97 x y z).
Proof. exact (MK_COMB (@lem1531323 x) (@lem1531322 y z)). Qed.
Lemma lem1531325 (x : real) (y : real) (z : real) : (term141 z x y) = (term97 x y z).
Proof. exact (TRANS (@lem1531321 x z y) (@lem1531324 x y z)). Qed.
Lemma lem1531326 (x : real) (y : real) (z : real) : (term140 z y x) = (term97 x y z).
Proof. exact (TRANS (@lem1531320 z x y) (@lem1531325 x y z)). Qed.
Lemma lem1531329 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1531330 (x : real) (y : real) (z : real) : (term174 z y x) = (term175 x y z).
Proof. exact (MK_COMB (@lem1531329 x) (@lem1531326 x y z)). Qed.
Lemma lem1531331 (x : real) (y : real) (z : real) : (term175 x y z) = (term176 x y z).
Proof. exact (@lem1483490 x x (term92 y z)). Qed.
Lemma lem1531332 (x : real) : (real_add x x) = (term177 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1531333 : term178 = term112.
Proof. exact (@lem1367770 term107 term107). Qed.
Lemma lem1531334 : term108 = term109.
Proof. exact (@lem706885). Qed.
Lemma lem1531335 : (term108 = term109) = (term110 = term111).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term109). Qed.
Lemma lem1531336 : term110 = term111.
Proof. exact (EQ_MP (@lem1531335) (@lem1531334)). Qed.
Lemma lem1531337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1531338 : term112 = term113.
Proof. exact (MK_COMB (@lem1531337) (@lem1531336)). Qed.
Lemma lem1531339 : term178 = term113.
Proof. exact (TRANS (@lem1531333) (@lem1531338)). Qed.
Lemma lem1531340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531341 : term179 = term180.
Proof. exact (MK_COMB (@lem1531340) (@lem1531339)). Qed.
Lemma lem1531342 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1531343 (x : real) : (term177 x) = (term181 x).
Proof. exact (MK_COMB (@lem1531341) (@lem1531342 x)). Qed.
Lemma lem1531344 (x : real) : (real_add x x) = (term181 x).
Proof. exact (TRANS (@lem1531332 x) (@lem1531343 x)). Qed.
Lemma lem1531345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531346 (x : real) : (term182 x) = (term183 x).
Proof. exact (MK_COMB (@lem1531345) (@lem1531344 x)). Qed.
Lemma lem1531347 (y : real) (z : real) : (term92 y z) = (term92 y z).
Proof. exact (eq_refl (term92 y z)). Qed.
Lemma lem1531348 (x : real) (y : real) (z : real) : (term176 x y z) = (term184 x y z).
Proof. exact (MK_COMB (@lem1531346 x) (@lem1531347 y z)). Qed.
Lemma lem1531349 (x : real) (y : real) (z : real) : (term175 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1531331 x y z) (@lem1531348 x y z)). Qed.
Lemma lem1531350 (x : real) (y : real) (z : real) : (term174 z y x) = (term184 x y z).
Proof. exact (TRANS (@lem1531330 x y z) (@lem1531349 x y z)). Qed.
Lemma lem1531351 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531352 (x : real) (y : real) (z : real) : (term185 z y x) = (term186 x y z).
Proof. exact (MK_COMB (@lem1531351) (@lem1531350 x y z)). Qed.
Lemma lem1531353 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531354 (x : real) (y : real) (z : real) : (term187 z y x) = (term188 x y z).
Proof. exact (MK_COMB (@lem1531352 x y z) (@lem1531353)). Qed.
Lemma lem1531355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531356 (x : real) (y : real) (z : real) : (term189 z y x) = (term190 x y z).
Proof. exact (MK_COMB (@lem1531355) (@lem1531354 x y z)). Qed.
Lemma lem1531357 (x : real) (y : real) (z : real) : (term163 z y x) = (term191 x y z).
Proof. exact (MK_COMB (@lem1531356 x y z) (@lem1531276 x y z)). Qed.
Lemma lem1531358 (x : real) (y : real) (z : real) : (term78 z y x) = (term191 x y z).
Proof. exact (TRANS (@lem1531219 z y x) (@lem1531357 x y z)). Qed.
Lemma lem1531359 (x : real) (y : real) (z : real) : (term87 z y x) = (term192 x y z).
Proof. exact (MK_COMB (@lem1531216 x y z) (@lem1531358 x y z)). Qed.
Lemma lem1531360 (x : real) (y : real) (z : real) : (term45 z y x) = (term192 x y z).
Proof. exact (TRANS (@lem1531058 z y x) (@lem1531359 x y z)). Qed.
Lemma lem1531361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531362 (x : real) (y : real) (z : real) : (term56 z y x) = (term193 x y z).
Proof. exact (MK_COMB (@lem1531361) (@lem1531360 x y z)). Qed.
Lemma lem1531363 (z : real) (y : real) : (term54 z y) = (term54 z y).
Proof. exact (eq_refl (term54 z y)). Qed.
Lemma lem1531364 (x : real) (z : real) (y : real) : (term57 x z y) = (term194 x z y).
Proof. exact (MK_COMB (@lem1531362 x y z) (@lem1531363 z y)). Qed.
Lemma lem1531365 (x : real) (z : real) (y : real) : (term195 x z y) = (term194 x z y).
Proof. exact (eq_refl (term195 x z y)). Qed.
Lemma lem1531366 (x : real) (z : real) (y : real) : (term194 x z y) = (term195 x z y).
Proof. exact (SYM (@lem1531365 x z y)). Qed.
Lemma lem1531367 (x : real) (z : real) (y : real) : (term195 x z y) = (term196 x z y).
Proof. exact (@lem1482981 (term197 x y z) y). Qed.
Lemma lem1531368 (x : real) (z : real) (y : real) : (term194 x z y) = (term196 x z y).
Proof. exact (TRANS (@lem1531366 x z y) (@lem1531367 x z y)). Qed.
Lemma lem1531369 (x : real) (z : real) (y : real) : (term198 x z y) = (term199 x z y).
Proof. exact (eq_refl (term198 x z y)). Qed.
Lemma lem1531370 (y : real) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem1531371 (x : real) (z : real) (y : real) : (term201 x z y) = (term202 x z y).
Proof. exact (MK_COMB (@lem1531370 y) (@lem1531369 x z y)). Qed.
Lemma lem1531372 (x : real) (z : real) (y : real) : (term203 x z y) = (term204 x z y).
Proof. exact (eq_refl (term203 x z y)). Qed.
Lemma lem1531373 (y : real) : (term205 y) = (term205 y).
Proof. exact (eq_refl (term205 y)). Qed.
Lemma lem1531374 (x : real) (z : real) (y : real) : (term206 x z y) = (term207 x z y).
Proof. exact (MK_COMB (@lem1531373 y) (@lem1531372 x z y)). Qed.
Lemma lem1531375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1531376 (x : real) (z : real) (y : real) : (term208 x z y) = (term209 x z y).
Proof. exact (MK_COMB (@lem1531375) (@lem1531374 x z y)). Qed.
Lemma lem1531377 (x : real) (z : real) (y : real) : (term196 x z y) = (term210 x z y).
Proof. exact (MK_COMB (@lem1531376 x z y) (@lem1531371 x z y)). Qed.
Lemma lem1531378 (x : real) (z : real) (y : real) : (term211 x z y) = (term211 x z y).
Proof. exact (eq_refl (term211 x z y)). Qed.
Lemma lem1531379 (x : real) (z : real) (y : real) : ((term194 x z y) = (term196 x z y)) = ((term194 x z y) = (term210 x z y)).
Proof. exact (MK_COMB (@lem1531378 x z y) (@lem1531377 x z y)). Qed.
Lemma lem1531380 (x : real) (z : real) (y : real) : (term194 x z y) = (term210 x z y).
Proof. exact (EQ_MP (@lem1531379 x z y) (@lem1531368 x z y)). Qed.
Lemma lem1531381 (y : real) : (term212 y) = (term213 y).
Proof. exact (@lem1483527 y term44). Qed.
Lemma lem1531387 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1483519 y term44). Qed.
Lemma lem1531389 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531390 : term217 = term44.
Proof. exact (@lem1531389 term107). Qed.
Lemma lem1531391 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1531392 (y : real) : (term215 y) = (term218 y).
Proof. exact (MK_COMB (@lem1531391 y) (@lem1531390)). Qed.
Lemma lem1531393 (y : real) : (term218 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1531394 (y : real) : (term215 y) = y.
Proof. exact (TRANS (@lem1531392 y) (@lem1531393 y)). Qed.
Lemma lem1531396 (y : real) : (term214 y) = y.
Proof. exact (TRANS (@lem1531387 y) (@lem1531394 y)). Qed.
Lemma lem1531397 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1531398 (y : real) : (term219 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1531397) (@lem1531396 y)). Qed.
Lemma lem1531399 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531400 (y : real) : (term213 y) = (term212 y).
Proof. exact (MK_COMB (@lem1531398 y) (@lem1531399)). Qed.
Lemma lem1531401 (y : real) : (term212 y) = (term212 y).
Proof. exact (TRANS (@lem1531381 y) (@lem1531400 y)). Qed.
Lemma lem1531402 (y : real) (z : real) : (term158 y z) = (term220 y z).
Proof. exact (@lem1483525 (term92 y z) term44). Qed.
Lemma lem1531420 (y : real) (z : real) : (term221 y z) = (term222 y z).
Proof. exact (@lem1483519 (term92 y z) term44). Qed.
Lemma lem1531422 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531423 : term217 = term44.
Proof. exact (@lem1531422 term107). Qed.
Lemma lem1531424 (y : real) (z : real) : (term223 y z) = (term223 y z).
Proof. exact (eq_refl (term223 y z)). Qed.
Lemma lem1531425 (y : real) (z : real) : (term222 y z) = (term224 y z).
Proof. exact (MK_COMB (@lem1531424 y z) (@lem1531423)). Qed.
Lemma lem1531426 (y : real) (z : real) : (term224 y z) = (term92 y z).
Proof. exact (@lem1483450 (term92 y z)). Qed.
Lemma lem1531427 (y : real) (z : real) : (term222 y z) = (term92 y z).
Proof. exact (TRANS (@lem1531425 y z) (@lem1531426 y z)). Qed.
Lemma lem1531429 (y : real) (z : real) : (term221 y z) = (term92 y z).
Proof. exact (TRANS (@lem1531420 y z) (@lem1531427 y z)). Qed.
Lemma lem1531430 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531431 (y : real) (z : real) : (term225 y z) = (term156 y z).
Proof. exact (MK_COMB (@lem1531430) (@lem1531429 y z)). Qed.
Lemma lem1531432 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531433 (y : real) (z : real) : (term220 y z) = (term158 y z).
Proof. exact (MK_COMB (@lem1531431 y z) (@lem1531432)). Qed.
Lemma lem1531434 (y : real) (z : real) : (term158 y z) = (term158 y z).
Proof. exact (TRANS (@lem1531402 y z) (@lem1531433 y z)). Qed.
Lemma lem1531435 (x : real) (y : real) (z : real) : (term124 x y z) = (term226 x y z).
Proof. exact (@lem1483525 (term120 x y z) term44). Qed.
Lemma lem1531459 (x : real) (y : real) (z : real) : (term227 x y z) = (term228 x y z).
Proof. exact (@lem1483519 (term120 x y z) term44). Qed.
Lemma lem1531461 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531462 : term217 = term44.
Proof. exact (@lem1531461 term107). Qed.
Lemma lem1531463 (x : real) (y : real) (z : real) : (term229 x y z) = (term229 x y z).
Proof. exact (eq_refl (term229 x y z)). Qed.
Lemma lem1531464 (x : real) (y : real) (z : real) : (term228 x y z) = (term230 x y z).
Proof. exact (MK_COMB (@lem1531463 x y z) (@lem1531462)). Qed.
Lemma lem1531465 (x : real) (y : real) (z : real) : (term230 x y z) = (term120 x y z).
Proof. exact (@lem1483450 (term120 x y z)). Qed.
Lemma lem1531466 (x : real) (y : real) (z : real) : (term228 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1531464 x y z) (@lem1531465 x y z)). Qed.
Lemma lem1531468 (x : real) (y : real) (z : real) : (term227 x y z) = (term120 x y z).
Proof. exact (TRANS (@lem1531459 x y z) (@lem1531466 x y z)). Qed.
Lemma lem1531469 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531470 (x : real) (y : real) (z : real) : (term231 x y z) = (term122 x y z).
Proof. exact (MK_COMB (@lem1531469) (@lem1531468 x y z)). Qed.
Lemma lem1531471 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531472 (x : real) (y : real) (z : real) : (term226 x y z) = (term124 x y z).
Proof. exact (MK_COMB (@lem1531470 x y z) (@lem1531471)). Qed.
Lemma lem1531473 (x : real) (y : real) (z : real) : (term124 x y z) = (term124 x y z).
Proof. exact (TRANS (@lem1531435 x y z) (@lem1531472 x y z)). Qed.
Lemma lem1531474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531475 (y : real) (z : real) : (term160 y z) = (term160 y z).
Proof. exact (MK_COMB (@lem1531474) (@lem1531434 y z)). Qed.
Lemma lem1531476 (x : real) (y : real) (z : real) : (term161 x y z) = (term161 x y z).
Proof. exact (MK_COMB (@lem1531475 y z) (@lem1531473 x y z)). Qed.
Lemma lem1531477 (x : real) (y : real) (z : real) : (term188 x y z) = (term232 x y z).
Proof. exact (@lem1483525 (term184 x y z) term44). Qed.
Lemma lem1531507 (x : real) (y : real) (z : real) : (term233 x y z) = (term234 x y z).
Proof. exact (@lem1483519 (term184 x y z) term44). Qed.
Lemma lem1531509 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531510 : term217 = term44.
Proof. exact (@lem1531509 term107). Qed.
Lemma lem1531511 (x : real) (y : real) (z : real) : (term235 x y z) = (term235 x y z).
Proof. exact (eq_refl (term235 x y z)). Qed.
Lemma lem1531512 (x : real) (y : real) (z : real) : (term234 x y z) = (term236 x y z).
Proof. exact (MK_COMB (@lem1531511 x y z) (@lem1531510)). Qed.
Lemma lem1531513 (x : real) (y : real) (z : real) : (term236 x y z) = (term184 x y z).
Proof. exact (@lem1483450 (term184 x y z)). Qed.
Lemma lem1531514 (x : real) (y : real) (z : real) : (term234 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1531512 x y z) (@lem1531513 x y z)). Qed.
Lemma lem1531516 (x : real) (y : real) (z : real) : (term233 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1531507 x y z) (@lem1531514 x y z)). Qed.
Lemma lem1531517 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531518 (x : real) (y : real) (z : real) : (term237 x y z) = (term186 x y z).
Proof. exact (MK_COMB (@lem1531517) (@lem1531516 x y z)). Qed.
Lemma lem1531519 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531520 (x : real) (y : real) (z : real) : (term232 x y z) = (term188 x y z).
Proof. exact (MK_COMB (@lem1531518 x y z) (@lem1531519)). Qed.
Lemma lem1531521 (x : real) (y : real) (z : real) : (term188 x y z) = (term188 x y z).
Proof. exact (TRANS (@lem1531477 x y z) (@lem1531520 x y z)). Qed.
Lemma lem1531522 (y : real) (z : real) : (term173 y z) = (term238 y z).
Proof. exact (@lem1483525 (real_add y z) term44). Qed.
Lemma lem1531534 (y : real) (z : real) : (term239 y z) = (term240 y z).
Proof. exact (@lem1483519 (real_add y z) term44). Qed.
Lemma lem1531536 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531537 : term217 = term44.
Proof. exact (@lem1531536 term107). Qed.
Lemma lem1531538 (y : real) (z : real) : (term241 y z) = (term241 y z).
Proof. exact (eq_refl (term241 y z)). Qed.
Lemma lem1531539 (y : real) (z : real) : (term240 y z) = (term242 y z).
Proof. exact (MK_COMB (@lem1531538 y z) (@lem1531537)). Qed.
Lemma lem1531540 (y : real) (z : real) : (term242 y z) = (real_add y z).
Proof. exact (@lem1483450 (real_add y z)). Qed.
Lemma lem1531541 (y : real) (z : real) : (term240 y z) = (real_add y z).
Proof. exact (TRANS (@lem1531539 y z) (@lem1531540 y z)). Qed.
Lemma lem1531543 (y : real) (z : real) : (term239 y z) = (real_add y z).
Proof. exact (TRANS (@lem1531534 y z) (@lem1531541 y z)). Qed.
Lemma lem1531544 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531545 (y : real) (z : real) : (term243 y z) = (term171 y z).
Proof. exact (MK_COMB (@lem1531544) (@lem1531543 y z)). Qed.
Lemma lem1531546 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531547 (y : real) (z : real) : (term238 y z) = (term173 y z).
Proof. exact (MK_COMB (@lem1531545 y z) (@lem1531546)). Qed.
Lemma lem1531548 (y : real) (z : real) : (term173 y z) = (term173 y z).
Proof. exact (TRANS (@lem1531522 y z) (@lem1531547 y z)). Qed.
Lemma lem1531549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531550 (x : real) (y : real) (z : real) : (term190 x y z) = (term190 x y z).
Proof. exact (MK_COMB (@lem1531549) (@lem1531521 x y z)). Qed.
Lemma lem1531551 (x : real) (y : real) (z : real) : (term191 x y z) = (term191 x y z).
Proof. exact (MK_COMB (@lem1531550 x y z) (@lem1531548 y z)). Qed.
Lemma lem1531552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531553 (x : real) (y : real) (z : real) : (term162 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1531552) (@lem1531476 x y z)). Qed.
Lemma lem1531554 (x : real) (y : real) (z : real) : (term192 x y z) = (term192 x y z).
Proof. exact (MK_COMB (@lem1531553 x y z) (@lem1531551 x y z)). Qed.
Lemma lem1531555 (z : real) (y : real) : (term244 z y) = (term245 z y).
Proof. exact (@lem1483527 (term92 z y) term44). Qed.
Lemma lem1531556 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531569 (y : real) (z : real) : (term92 z y) = (term91 y z).
Proof. exact (@lem1483488 y (term51 z)). Qed.
Lemma lem1531570 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1531571 (y : real) (z : real) : (term246 z y) = (term247 y z).
Proof. exact (MK_COMB (@lem1531570) (@lem1531569 y z)). Qed.
Lemma lem1531572 (y : real) (z : real) : (term221 z y) = (term248 y z).
Proof. exact (MK_COMB (@lem1531571 y z) (@lem1531556)). Qed.
Lemma lem1531573 (y : real) (z : real) : (term248 y z) = (term249 y z).
Proof. exact (@lem1483519 (term91 y z) term44). Qed.
Lemma lem1531575 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531576 : term217 = term44.
Proof. exact (@lem1531575 term107). Qed.
Lemma lem1531577 (y : real) (z : real) : (term250 y z) = (term250 y z).
Proof. exact (eq_refl (term250 y z)). Qed.
Lemma lem1531578 (y : real) (z : real) : (term249 y z) = (term251 y z).
Proof. exact (MK_COMB (@lem1531577 y z) (@lem1531576)). Qed.
Lemma lem1531579 (y : real) (z : real) : (term251 y z) = (term91 y z).
Proof. exact (@lem1483450 (term91 y z)). Qed.
Lemma lem1531580 (y : real) (z : real) : (term249 y z) = (term91 y z).
Proof. exact (TRANS (@lem1531578 y z) (@lem1531579 y z)). Qed.
Lemma lem1531581 (y : real) (z : real) : (term248 y z) = (term91 y z).
Proof. exact (TRANS (@lem1531573 y z) (@lem1531580 y z)). Qed.
Lemma lem1531582 (y : real) (z : real) : (term221 z y) = (term91 y z).
Proof. exact (TRANS (@lem1531572 y z) (@lem1531581 y z)). Qed.
Lemma lem1531583 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1531584 (y : real) (z : real) : (term252 z y) = (term253 y z).
Proof. exact (MK_COMB (@lem1531583) (@lem1531582 y z)). Qed.
Lemma lem1531585 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531586 (y : real) (z : real) : (term245 z y) = (term254 y z).
Proof. exact (MK_COMB (@lem1531584 y z) (@lem1531585)). Qed.
Lemma lem1531587 (y : real) (z : real) : (term244 z y) = (term254 y z).
Proof. exact (TRANS (@lem1531555 z y) (@lem1531586 y z)). Qed.
Lemma lem1531588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531589 (x : real) (y : real) (z : real) : (term193 x y z) = (term193 x y z).
Proof. exact (MK_COMB (@lem1531588) (@lem1531554 x y z)). Qed.
Lemma lem1531590 (x : real) (y : real) (z : real) : (term204 x z y) = (term255 x y z).
Proof. exact (MK_COMB (@lem1531589 x y z) (@lem1531587 y z)). Qed.
Lemma lem1531591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531592 (y : real) : (term205 y) = (term205 y).
Proof. exact (MK_COMB (@lem1531591) (@lem1531401 y)). Qed.
Lemma lem1531593 (x : real) (y : real) (z : real) : (term207 x z y) = (term256 x y z).
Proof. exact (MK_COMB (@lem1531592 y) (@lem1531590 x y z)). Qed.
Lemma lem1531594 (y : real) : (term257 y) = (term258 y).
Proof. exact (@lem1483525 term44 y). Qed.
Lemma lem1531600 (y : real) : (term259 y) = (term260 y).
Proof. exact (@lem1483519 term44 y). Qed.
Lemma lem1531605 (y : real) : (term260 y) = (term51 y).
Proof. exact (@lem1483448 (term51 y)). Qed.
Lemma lem1531607 (y : real) : (term259 y) = (term51 y).
Proof. exact (TRANS (@lem1531600 y) (@lem1531605 y)). Qed.
Lemma lem1531608 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531609 (y : real) : (term261 y) = (term262 y).
Proof. exact (MK_COMB (@lem1531608) (@lem1531607 y)). Qed.
Lemma lem1531610 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531611 (y : real) : (term258 y) = (term263 y).
Proof. exact (MK_COMB (@lem1531609 y) (@lem1531610)). Qed.
Lemma lem1531612 (y : real) : (term257 y) = (term263 y).
Proof. exact (TRANS (@lem1531594 y) (@lem1531611 y)). Qed.
Lemma lem1531613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531614 (y : real) (z : real) : (term160 y z) = (term160 y z).
Proof. exact (MK_COMB (@lem1531613) (@lem1531434 y z)). Qed.
Lemma lem1531615 (x : real) (y : real) (z : real) : (term161 x y z) = (term161 x y z).
Proof. exact (MK_COMB (@lem1531614 y z) (@lem1531473 x y z)). Qed.
Lemma lem1531616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531617 (x : real) (y : real) (z : real) : (term190 x y z) = (term190 x y z).
Proof. exact (MK_COMB (@lem1531616) (@lem1531521 x y z)). Qed.
Lemma lem1531618 (x : real) (y : real) (z : real) : (term191 x y z) = (term191 x y z).
Proof. exact (MK_COMB (@lem1531617 x y z) (@lem1531548 y z)). Qed.
Lemma lem1531619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531620 (x : real) (y : real) (z : real) : (term162 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1531619) (@lem1531615 x y z)). Qed.
Lemma lem1531621 (x : real) (y : real) (z : real) : (term192 x y z) = (term192 x y z).
Proof. exact (MK_COMB (@lem1531620 x y z) (@lem1531618 x y z)). Qed.
Lemma lem1531622 (z : real) (y : real) : (term264 z y) = (term265 z y).
Proof. exact (@lem1483527 (term266 z y) term44). Qed.
Lemma lem1531623 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531630 (y : real) : (real_neg y) = (term51 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1531639 (z : real) : (term99 z) = (term99 z).
Proof. exact (eq_refl (term99 z)). Qed.
Lemma lem1531640 (z : real) (y : real) : (term266 z y) = (term267 z y).
Proof. exact (MK_COMB (@lem1531639 z) (@lem1531630 y)). Qed.
Lemma lem1531641 (y : real) (z : real) : (term267 z y) = (term267 y z).
Proof. exact (@lem1483488 (term51 y) (term51 z)). Qed.
Lemma lem1531642 (y : real) (z : real) : (term266 z y) = (term267 y z).
Proof. exact (TRANS (@lem1531640 z y) (@lem1531641 y z)). Qed.
Lemma lem1531643 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1531644 (y : real) (z : real) : (term268 z y) = (term269 y z).
Proof. exact (MK_COMB (@lem1531643) (@lem1531642 y z)). Qed.
Lemma lem1531645 (y : real) (z : real) : (term270 z y) = (term271 y z).
Proof. exact (MK_COMB (@lem1531644 y z) (@lem1531623)). Qed.
Lemma lem1531646 (y : real) (z : real) : (term271 y z) = (term272 y z).
Proof. exact (@lem1483519 (term267 y z) term44). Qed.
Lemma lem1531648 (x : nat) : (term216 x) = term44.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1531649 : term217 = term44.
Proof. exact (@lem1531648 term107). Qed.
Lemma lem1531650 (y : real) (z : real) : (term273 y z) = (term273 y z).
Proof. exact (eq_refl (term273 y z)). Qed.
Lemma lem1531651 (y : real) (z : real) : (term272 y z) = (term274 y z).
Proof. exact (MK_COMB (@lem1531650 y z) (@lem1531649)). Qed.
Lemma lem1531652 (y : real) (z : real) : (term274 y z) = (term267 y z).
Proof. exact (@lem1483450 (term267 y z)). Qed.
Lemma lem1531653 (y : real) (z : real) : (term272 y z) = (term267 y z).
Proof. exact (TRANS (@lem1531651 y z) (@lem1531652 y z)). Qed.
Lemma lem1531654 (y : real) (z : real) : (term271 y z) = (term267 y z).
Proof. exact (TRANS (@lem1531646 y z) (@lem1531653 y z)). Qed.
Lemma lem1531655 (y : real) (z : real) : (term270 z y) = (term267 y z).
Proof. exact (TRANS (@lem1531645 y z) (@lem1531654 y z)). Qed.
Lemma lem1531656 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1531657 (y : real) (z : real) : (term275 z y) = (term276 y z).
Proof. exact (MK_COMB (@lem1531656) (@lem1531655 y z)). Qed.
Lemma lem1531658 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531659 (y : real) (z : real) : (term265 z y) = (term277 y z).
Proof. exact (MK_COMB (@lem1531657 y z) (@lem1531658)). Qed.
Lemma lem1531660 (y : real) (z : real) : (term264 z y) = (term277 y z).
Proof. exact (TRANS (@lem1531622 z y) (@lem1531659 y z)). Qed.
Lemma lem1531661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531662 (x : real) (y : real) (z : real) : (term193 x y z) = (term193 x y z).
Proof. exact (MK_COMB (@lem1531661) (@lem1531621 x y z)). Qed.
Lemma lem1531663 (x : real) (y : real) (z : real) : (term199 x z y) = (term278 x y z).
Proof. exact (MK_COMB (@lem1531662 x y z) (@lem1531660 y z)). Qed.
Lemma lem1531664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1531665 (y : real) : (term200 y) = (term279 y).
Proof. exact (MK_COMB (@lem1531664) (@lem1531612 y)). Qed.
Lemma lem1531666 (x : real) (y : real) (z : real) : (term202 x z y) = (term280 x y z).
Proof. exact (MK_COMB (@lem1531665 y) (@lem1531663 x y z)). Qed.
Lemma lem1531667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1531668 (x : real) (y : real) (z : real) : (term209 x z y) = (term281 x y z).
Proof. exact (MK_COMB (@lem1531667) (@lem1531593 x y z)). Qed.
Lemma lem1531669 (x : real) (y : real) (z : real) : (term210 x z y) = (term282 x y z).
Proof. exact (MK_COMB (@lem1531668 x y z) (@lem1531666 x y z)). Qed.
Lemma lem1531680 (x : real) (y : real) (z : real) : (term194 x z y) = (term282 x y z).
Proof. exact (TRANS (@lem1531380 x z y) (@lem1531669 x y z)). Qed.
Lemma lem1531681 (x : real) (y : real) (z : real) : (term57 x z y) = (term282 x y z).
Proof. exact (TRANS (@lem1531364 x z y) (@lem1531680 x y z)). Qed.
Lemma lem1531682 (x : real) (y : real) (z : real) (h1 : term282 x y z) : term282 x y z.
Proof. exact (h1). Qed.
Lemma lem1531683 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term256 x y z.
Proof. exact (h1). Qed.
Lemma lem1531684 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term255 x y z.
Proof. exact (proj2 (@lem1531683 x y z h1)). Qed.
Lemma lem1531686 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term254 y z.
Proof. exact (proj2 (@lem1531684 x y z h1)). Qed.
Lemma lem1531687 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term192 x y z.
Proof. exact (proj1 (@lem1531684 x y z h1)). Qed.
Lemma lem1531689 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term161 x y z.
Proof. exact (proj1 (@lem1531687 x y z h1)). Qed.
Lemma lem1531691 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term158 y z.
Proof. exact (proj1 (@lem1531689 x y z h1)). Qed.
Lemma lem1531695 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531696 : term284 = term285.
Proof. exact (@lem1531695 (NUMERAL 0) term107). Qed.
Lemma lem1531697 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1531698 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1531699 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1531698 h1) (fun h1 : term285 = True => @lem1531697)). Qed.
Lemma lem1531700 : term285 = True.
Proof. exact (EQ_MP (@lem1531699) (@lem1531697)). Qed.
Lemma lem1531701 : term284 = True.
Proof. exact (TRANS (@lem1531696) (@lem1531700)). Qed.
Lemma lem1531702 : True = term284.
Proof. exact (SYM (@lem1531701)). Qed.
Lemma lem1531703 : term284.
Proof. exact (EQ_MP (@lem1531702) (@lem0)). Qed.
Lemma lem1531704 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term287 y z.
Proof. exact (conj (@lem1531703) (@lem1531686 x y z h1)). Qed.
Lemma lem1531706 (x : real) (y : real) : term288 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1531707 (y : real) (z : real) : term289 y z.
Proof. exact (@lem1531706 term137 (term91 y z)). Qed.
Lemma lem1531708 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term290 y z.
Proof. exact (@lem1531707 y z (@lem1531704 x y z h1)). Qed.
Lemma lem1531709 (y : real) (z : real) : (term291 y z) = (term91 y z).
Proof. exact (@lem1483460 (term91 y z)). Qed.
Lemma lem1531710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1531711 (y : real) (z : real) : (term292 y z) = (term253 y z).
Proof. exact (MK_COMB (@lem1531710) (@lem1531709 y z)). Qed.
Lemma lem1531712 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531713 (y : real) (z : real) : (term290 y z) = (term254 y z).
Proof. exact (MK_COMB (@lem1531711 y z) (@lem1531712)). Qed.
Lemma lem1531714 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term254 y z.
Proof. exact (EQ_MP (@lem1531713 y z) (@lem1531708 x y z h1)). Qed.
Lemma lem1531716 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531717 : term284 = term285.
Proof. exact (@lem1531716 (NUMERAL 0) term107). Qed.
Lemma lem1531718 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1531719 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1531720 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1531719 h1) (fun h1 : term285 = True => @lem1531718)). Qed.
Lemma lem1531721 : term285 = True.
Proof. exact (EQ_MP (@lem1531720) (@lem1531718)). Qed.
Lemma lem1531722 : term284 = True.
Proof. exact (TRANS (@lem1531717) (@lem1531721)). Qed.
Lemma lem1531723 : True = term284.
Proof. exact (SYM (@lem1531722)). Qed.
Lemma lem1531724 : term284.
Proof. exact (EQ_MP (@lem1531723) (@lem0)). Qed.
Lemma lem1531725 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term293 y z.
Proof. exact (conj (@lem1531724) (@lem1531691 x y z h1)). Qed.
Lemma lem1531727 (x : real) (y : real) : term294 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1531728 (y : real) (z : real) : term295 y z.
Proof. exact (@lem1531727 term137 (term92 y z)). Qed.
Lemma lem1531729 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term296 y z.
Proof. exact (@lem1531728 y z (@lem1531725 x y z h1)). Qed.
Lemma lem1531730 (y : real) (z : real) : (term95 y z) = (term92 y z).
Proof. exact (@lem1483460 (term92 y z)). Qed.
Lemma lem1531731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531732 (y : real) (z : real) : (term297 y z) = (term156 y z).
Proof. exact (MK_COMB (@lem1531731) (@lem1531730 y z)). Qed.
Lemma lem1531733 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531734 (y : real) (z : real) : (term296 y z) = (term158 y z).
Proof. exact (MK_COMB (@lem1531732 y z) (@lem1531733)). Qed.
Lemma lem1531735 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term158 y z.
Proof. exact (EQ_MP (@lem1531734 y z) (@lem1531729 x y z h1)). Qed.
Lemma lem1531736 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term298 y z.
Proof. exact (conj (@lem1531735 x y z h1) (@lem1531714 x y z h1)). Qed.
Lemma lem1531738 (x : real) (y : real) : term299 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1531739 (y : real) (z : real) : term300 y z.
Proof. exact (@lem1531738 (term92 y z) (term91 y z)). Qed.
Lemma lem1531740 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term301 y z.
Proof. exact (@lem1531739 y z (@lem1531736 x y z h1)). Qed.
Lemma lem1531741 (y : real) (z : real) : (term302 y z) = (term303 y z).
Proof. exact (@lem1483480 (term51 y) y z (term51 z)). Qed.
Lemma lem1531742 (y : real) : (term145 y) = (term146 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1531744 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531745 : term148 = term44.
Proof. exact (@lem1531744 term107). Qed.
Lemma lem1531746 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531747 : term149 = term150.
Proof. exact (MK_COMB (@lem1531746) (@lem1531745)). Qed.
Lemma lem1531748 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1531749 (y : real) : (term146 y) = (term151 y).
Proof. exact (MK_COMB (@lem1531747) (@lem1531748 y)). Qed.
Lemma lem1531750 (y : real) : (term145 y) = (term151 y).
Proof. exact (TRANS (@lem1531742 y) (@lem1531749 y)). Qed.
Lemma lem1531751 (y : real) : (term151 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1531752 (y : real) : (term145 y) = term44.
Proof. exact (TRANS (@lem1531750 y) (@lem1531751 y)). Qed.
Lemma lem1531753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531754 (y : real) : (term152 y) = term153.
Proof. exact (MK_COMB (@lem1531753) (@lem1531752 y)). Qed.
Lemma lem1531755 (z : real) : (term167 z) = (term146 z).
Proof. exact (@lem1483442 term39 z). Qed.
Lemma lem1531757 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531758 : term148 = term44.
Proof. exact (@lem1531757 term107). Qed.
Lemma lem1531759 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531760 : term149 = term150.
Proof. exact (MK_COMB (@lem1531759) (@lem1531758)). Qed.
Lemma lem1531761 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1531762 (z : real) : (term146 z) = (term151 z).
Proof. exact (MK_COMB (@lem1531760) (@lem1531761 z)). Qed.
Lemma lem1531763 (z : real) : (term167 z) = (term151 z).
Proof. exact (TRANS (@lem1531755 z) (@lem1531762 z)). Qed.
Lemma lem1531764 (z : real) : (term151 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1531765 (z : real) : (term167 z) = term44.
Proof. exact (TRANS (@lem1531763 z) (@lem1531764 z)). Qed.
Lemma lem1531766 (y : real) (z : real) : (term303 y z) = term304.
Proof. exact (MK_COMB (@lem1531754 y) (@lem1531765 z)). Qed.
Lemma lem1531767 (y : real) (z : real) : (term302 y z) = term304.
Proof. exact (TRANS (@lem1531741 y z) (@lem1531766 y z)). Qed.
Lemma lem1531768 : term304 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1531769 (y : real) (z : real) : (term302 y z) = term44.
Proof. exact (TRANS (@lem1531767 y z) (@lem1531768)). Qed.
Lemma lem1531770 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531771 (y : real) (z : real) : (term305 y z) = term306.
Proof. exact (MK_COMB (@lem1531770) (@lem1531769 y z)). Qed.
Lemma lem1531772 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531773 (y : real) (z : real) : (term301 y z) = term307.
Proof. exact (MK_COMB (@lem1531771 y z) (@lem1531772)). Qed.
Lemma lem1531774 (x : real) (y : real) (z : real) (h1 : term256 x y z) : term307.
Proof. exact (EQ_MP (@lem1531773 y z) (@lem1531740 x y z h1)). Qed.
Lemma lem1531776 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531777 : term307 = term308.
Proof. exact (@lem1531776 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1531778 : term308 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1531779 : term307 = False.
Proof. exact (TRANS (@lem1531777) (@lem1531778)). Qed.
Lemma lem1531780 (x : real) (y : real) (z : real) (h1 : term256 x y z) : False.
Proof. exact (EQ_MP (@lem1531779) (@lem1531774 x y z h1)). Qed.
Lemma lem1531781 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term280 x y z.
Proof. exact (h1). Qed.
Lemma lem1531782 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term278 x y z.
Proof. exact (proj2 (@lem1531781 x y z h1)). Qed.
Lemma lem1531784 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term277 y z.
Proof. exact (proj2 (@lem1531782 x y z h1)). Qed.
Lemma lem1531785 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term192 x y z.
Proof. exact (proj1 (@lem1531782 x y z h1)). Qed.
Lemma lem1531786 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term191 x y z.
Proof. exact (proj2 (@lem1531785 x y z h1)). Qed.
Lemma lem1531790 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term173 y z.
Proof. exact (proj2 (@lem1531786 x y z h1)). Qed.
Lemma lem1531793 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531794 : term284 = term285.
Proof. exact (@lem1531793 (NUMERAL 0) term107). Qed.
Lemma lem1531795 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1531796 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1531797 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1531796 h1) (fun h1 : term285 = True => @lem1531795)). Qed.
Lemma lem1531798 : term285 = True.
Proof. exact (EQ_MP (@lem1531797) (@lem1531795)). Qed.
Lemma lem1531799 : term284 = True.
Proof. exact (TRANS (@lem1531794) (@lem1531798)). Qed.
Lemma lem1531800 : True = term284.
Proof. exact (SYM (@lem1531799)). Qed.
Lemma lem1531801 : term284.
Proof. exact (EQ_MP (@lem1531800) (@lem0)). Qed.
Lemma lem1531802 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term309 y z.
Proof. exact (conj (@lem1531801) (@lem1531784 x y z h1)). Qed.
Lemma lem1531804 (x : real) (y : real) : term288 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1531805 (y : real) (z : real) : term310 y z.
Proof. exact (@lem1531804 term137 (term267 y z)). Qed.
Lemma lem1531806 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term311 y z.
Proof. exact (@lem1531805 y z (@lem1531802 x y z h1)). Qed.
Lemma lem1531807 (y : real) (z : real) : (term312 y z) = (term267 y z).
Proof. exact (@lem1483460 (term267 y z)). Qed.
Lemma lem1531808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1531809 (y : real) (z : real) : (term313 y z) = (term276 y z).
Proof. exact (MK_COMB (@lem1531808) (@lem1531807 y z)). Qed.
Lemma lem1531810 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531811 (y : real) (z : real) : (term311 y z) = (term277 y z).
Proof. exact (MK_COMB (@lem1531809 y z) (@lem1531810)). Qed.
Lemma lem1531812 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term277 y z.
Proof. exact (EQ_MP (@lem1531811 y z) (@lem1531806 x y z h1)). Qed.
Lemma lem1531814 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531815 : term284 = term285.
Proof. exact (@lem1531814 (NUMERAL 0) term107). Qed.
Lemma lem1531816 : term286 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1531817 (h1 : term286 = (BIT1 0)) : term285 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1531818 : (term286 = (BIT1 0)) = (term285 = True).
Proof. exact (prop_ext (fun h1 : term286 = (BIT1 0) => @lem1531817 h1) (fun h1 : term285 = True => @lem1531816)). Qed.
Lemma lem1531819 : term285 = True.
Proof. exact (EQ_MP (@lem1531818) (@lem1531816)). Qed.
Lemma lem1531820 : term284 = True.
Proof. exact (TRANS (@lem1531815) (@lem1531819)). Qed.
Lemma lem1531821 : True = term284.
Proof. exact (SYM (@lem1531820)). Qed.
Lemma lem1531822 : term284.
Proof. exact (EQ_MP (@lem1531821) (@lem0)). Qed.
Lemma lem1531823 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term314 y z.
Proof. exact (conj (@lem1531822) (@lem1531790 x y z h1)). Qed.
Lemma lem1531825 (x : real) (y : real) : term294 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1531826 (y : real) (z : real) : term315 y z.
Proof. exact (@lem1531825 term137 (real_add y z)). Qed.
Lemma lem1531827 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term316 y z.
Proof. exact (@lem1531826 y z (@lem1531823 x y z h1)). Qed.
Lemma lem1531828 (y : real) (z : real) : (term317 y z) = (real_add y z).
Proof. exact (@lem1483460 (real_add y z)). Qed.
Lemma lem1531829 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531830 (y : real) (z : real) : (term318 y z) = (term171 y z).
Proof. exact (MK_COMB (@lem1531829) (@lem1531828 y z)). Qed.
Lemma lem1531831 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531832 (y : real) (z : real) : (term316 y z) = (term173 y z).
Proof. exact (MK_COMB (@lem1531830 y z) (@lem1531831)). Qed.
Lemma lem1531833 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term173 y z.
Proof. exact (EQ_MP (@lem1531832 y z) (@lem1531827 x y z h1)). Qed.
Lemma lem1531834 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term319 y z.
Proof. exact (conj (@lem1531833 x y z h1) (@lem1531812 x y z h1)). Qed.
Lemma lem1531836 (x : real) (y : real) : term299 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1531837 (y : real) (z : real) : term320 y z.
Proof. exact (@lem1531836 (real_add y z) (term267 y z)). Qed.
Lemma lem1531838 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term321 y z.
Proof. exact (@lem1531837 y z (@lem1531834 x y z h1)). Qed.
Lemma lem1531839 (y : real) (z : real) : (term322 y z) = (term323 y z).
Proof. exact (@lem1483480 y (term51 y) z (term51 z)). Qed.
Lemma lem1531840 (y : real) : (term167 y) = (term146 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1531842 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531843 : term148 = term44.
Proof. exact (@lem1531842 term107). Qed.
Lemma lem1531844 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531845 : term149 = term150.
Proof. exact (MK_COMB (@lem1531844) (@lem1531843)). Qed.
Lemma lem1531846 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1531847 (y : real) : (term146 y) = (term151 y).
Proof. exact (MK_COMB (@lem1531845) (@lem1531846 y)). Qed.
Lemma lem1531848 (y : real) : (term167 y) = (term151 y).
Proof. exact (TRANS (@lem1531840 y) (@lem1531847 y)). Qed.
Lemma lem1531849 (y : real) : (term151 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1531850 (y : real) : (term167 y) = term44.
Proof. exact (TRANS (@lem1531848 y) (@lem1531849 y)). Qed.
Lemma lem1531851 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1531852 (y : real) : (term168 y) = term153.
Proof. exact (MK_COMB (@lem1531851) (@lem1531850 y)). Qed.
Lemma lem1531853 (z : real) : (term167 z) = (term146 z).
Proof. exact (@lem1483442 term39 z). Qed.
Lemma lem1531855 (m : nat) : (term147 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1531856 : term148 = term44.
Proof. exact (@lem1531855 term107). Qed.
Lemma lem1531857 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1531858 : term149 = term150.
Proof. exact (MK_COMB (@lem1531857) (@lem1531856)). Qed.
Lemma lem1531859 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1531860 (z : real) : (term146 z) = (term151 z).
Proof. exact (MK_COMB (@lem1531858) (@lem1531859 z)). Qed.
Lemma lem1531861 (z : real) : (term167 z) = (term151 z).
Proof. exact (TRANS (@lem1531853 z) (@lem1531860 z)). Qed.
Lemma lem1531862 (z : real) : (term151 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1531863 (z : real) : (term167 z) = term44.
Proof. exact (TRANS (@lem1531861 z) (@lem1531862 z)). Qed.
Lemma lem1531864 (y : real) (z : real) : (term323 y z) = term304.
Proof. exact (MK_COMB (@lem1531852 y) (@lem1531863 z)). Qed.
Lemma lem1531865 (y : real) (z : real) : (term322 y z) = term304.
Proof. exact (TRANS (@lem1531839 y z) (@lem1531864 y z)). Qed.
Lemma lem1531866 : term304 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1531867 (y : real) (z : real) : (term322 y z) = term44.
Proof. exact (TRANS (@lem1531865 y z) (@lem1531866)). Qed.
Lemma lem1531868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531869 (y : real) (z : real) : (term324 y z) = term306.
Proof. exact (MK_COMB (@lem1531868) (@lem1531867 y z)). Qed.
Lemma lem1531870 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1531871 (y : real) (z : real) : (term321 y z) = term307.
Proof. exact (MK_COMB (@lem1531869 y z) (@lem1531870)). Qed.
Lemma lem1531872 (x : real) (y : real) (z : real) (h1 : term280 x y z) : term307.
Proof. exact (EQ_MP (@lem1531871 y z) (@lem1531838 x y z h1)). Qed.
Lemma lem1531874 (n : nat) (m : nat) : (term283 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531875 : term307 = term308.
Proof. exact (@lem1531874 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1531876 : term308 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1531877 : term307 = False.
Proof. exact (TRANS (@lem1531875) (@lem1531876)). Qed.
Lemma lem1531878 (x : real) (y : real) (z : real) (h1 : term280 x y z) : False.
Proof. exact (EQ_MP (@lem1531877) (@lem1531872 x y z h1)). Qed.
Lemma lem1531879 (x : real) (y : real) (z : real) (h1 : term282 x y z) : False.
Proof. exact (or_elim (@lem1531682 x y z h1) (fun h0 : term256 x y z => @lem1531780 x y z h0) (fun h0 : term280 x y z => @lem1531878 x y z h0)). Qed.
Lemma lem1531880 (x : real) (z : real) (y : real) (h1 : term57 x z y) : term57 x z y.
Proof. exact (h1). Qed.
Lemma lem1531881 (x : real) (z : real) (y : real) (h1 : term57 x z y) : term282 x y z.
Proof. exact (EQ_MP (@lem1531681 x y z) (@lem1531880 x z y h1)). Qed.
Lemma lem1531882 (x : real) (z : real) (y : real) (h1 : term57 x z y) : (term282 x y z) = False.
Proof. exact (prop_ext (fun h2 : term282 x y z => @lem1531879 x y z h2) (fun h2 : False => @lem1531881 x z y h1)). Qed.
Lemma lem1531883 (x : real) (z : real) (y : real) (h1 : term57 x z y) : False.
Proof. exact (EQ_MP (@lem1531882 x z y h1) (@lem1531881 x z y h1)). Qed.
Lemma lem1531884 (x : real) (y : real) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem1531885 (x : real) (y : real) (h1 : term59 x y) : False.
Proof. exact (ex_elim (@lem1531884 x y h1) (fun z : real => fun h0 : term58 x y z => @lem1531883 x z y h0)). Qed.
Lemma lem1531886 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (h1). Qed.
Lemma lem1531887 (x : real) (h1 : term61 x) : False.
Proof. exact (ex_elim (@lem1531886 x h1) (fun y : real => fun h0 : term60 x y => @lem1531885 x y h0)). Qed.
Lemma lem1531888 (h1 : term63) : term63.
Proof. exact (h1). Qed.
Lemma lem1531889 (h1 : term63) : False.
Proof. exact (ex_elim (@lem1531888 h1) (fun x : real => fun h0 : term62 x => @lem1531887 x h0)). Qed.
Lemma lem1531890 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1531891 (h1 : term24) : term63.
Proof. exact (EQ_MP (@lem1530985) (@lem1531890 h1)). Qed.
Lemma lem1531892 (h1 : term24) : term63 = False.
Proof. exact (prop_ext (fun h2 : term63 => @lem1531889 h2) (fun h2 : False => @lem1531891 h1)). Qed.
Lemma lem1531893 (h1 : term24) : False.
Proof. exact (EQ_MP (@lem1531892 h1) (@lem1531891 h1)). Qed.
Lemma lem1531894 : term325.
Proof. exact (fun h0 : term24 => @lem1531893 h0). Qed.
Lemma lem1531895 : term326.
Proof. exact (@lem1386578 term327). Qed.
Lemma lem1531896 : term327.
Proof. exact (@lem1531895 (@lem1531894)). Qed.
