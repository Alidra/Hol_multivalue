Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_NEGTOTAL_term_abbrevs.
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
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm18392_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1498864 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17160 (term2 x) (term3 x)). Qed.
Lemma lem1498866 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1498867 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1498866 x) (@lem1498864 x)). Qed.
Lemma lem1498868 (x : real) : (term7 x) = (term5 x).
Proof. exact (@lem17160 (x = term8) (term9 x)). Qed.
Lemma lem1498869 (x : real) : (term7 x) = (term6 x).
Proof. exact (TRANS (@lem1498868 x) (@lem1498867 x)). Qed.
Lemma lem1498870 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1498871 : term12 = term13.
Proof. exact (@lem1498870 term14). Qed.
Lemma lem1498872 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1498873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1498874 (x : real) : (term17 x) = (term7 x).
Proof. exact (MK_COMB (@lem1498873) (@lem1498872 x)). Qed.
Lemma lem1498875 (x : real) : (term17 x) = (term6 x).
Proof. exact (TRANS (@lem1498874 x) (@lem1498869 x)). Qed.
Lemma lem1498876 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1498875 x)). Qed.
Lemma lem1498877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498878 : term13 = term20.
Proof. exact (MK_COMB (@lem1498877) (@lem1498876)). Qed.
Lemma lem1498880 : term12 = term20.
Proof. exact (TRANS (@lem1498871) (@lem1498878)). Qed.
Lemma lem1498895 (x : real) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1498896 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1498895 x)). Qed.
Lemma lem1498897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498898 : term20 = term20.
Proof. exact (MK_COMB (@lem1498897) (@lem1498896)). Qed.
Lemma lem1498899 : term12 = term20.
Proof. exact (TRANS (@lem1498880) (@lem1498898)). Qed.
Lemma lem1498900 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1483554 x term8). Qed.
Lemma lem1498906 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term8). Qed.
Lemma lem1498908 (x : nat) : (term25 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1498909 : term26 = term8.
Proof. exact (@lem1498908 term27). Qed.
Lemma lem1498910 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1498911 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1498910 x) (@lem1498909)). Qed.
Lemma lem1498912 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1498913 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1498911 x) (@lem1498912 x)). Qed.
Lemma lem1498915 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1498906 x) (@lem1498913 x)). Qed.
Lemma lem1498916 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1498917 (x : real) : (term29 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1498916) (@lem1498915 x)). Qed.
Lemma lem1498920 (x : real) : (real_neg x) = (term30 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1498921 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1498922 (x : real) : ((term29 x) = (real_neg x)) = ((term29 x) = (term30 x)).
Proof. exact (MK_COMB (@lem1498921 x) (@lem1498920 x)). Qed.
Lemma lem1498923 (x : real) : (term29 x) = (term30 x).
Proof. exact (EQ_MP (@lem1498922 x) (@lem1498917 x)). Qed.
Lemma lem1498924 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498925 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1498924) (@lem1498923 x)). Qed.
Lemma lem1498926 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1498927 (x : real) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1498925 x) (@lem1498926)). Qed.
Lemma lem1498928 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498929 (x : real) : (term36 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1498928) (@lem1498915 x)). Qed.
Lemma lem1498930 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1498931 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1498929 x) (@lem1498930)). Qed.
Lemma lem1498932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1498933 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1498932) (@lem1498931 x)). Qed.
Lemma lem1498934 (x : real) : (term22 x) = (term41 x).
Proof. exact (MK_COMB (@lem1498933 x) (@lem1498927 x)). Qed.
Lemma lem1498935 (x : real) : (term21 x) = (term41 x).
Proof. exact (TRANS (@lem1498900 x) (@lem1498934 x)). Qed.
Lemma lem1498936 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483531 term8 x). Qed.
Lemma lem1498942 (x : real) : (term44 x) = (term45 x).
Proof. exact (@lem1483519 term8 x). Qed.
Lemma lem1498947 (x : real) : (term45 x) = (term30 x).
Proof. exact (@lem1483448 (term30 x)). Qed.
Lemma lem1498949 (x : real) : (term44 x) = (term30 x).
Proof. exact (TRANS (@lem1498942 x) (@lem1498947 x)). Qed.
Lemma lem1498950 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498951 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1498950) (@lem1498949 x)). Qed.
Lemma lem1498952 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1498953 (x : real) : (term43 x) = (term48 x).
Proof. exact (MK_COMB (@lem1498951 x) (@lem1498952)). Qed.
Lemma lem1498954 (x : real) : (term42 x) = (term48 x).
Proof. exact (TRANS (@lem1498936 x) (@lem1498953 x)). Qed.
Lemma lem1498955 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1483531 term8 (real_neg x)). Qed.
Lemma lem1498962 (x : real) : (real_neg x) = (term30 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1498965 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1498966 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1498965) (@lem1498962 x)). Qed.
Lemma lem1498967 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1483519 term8 (term30 x)). Qed.
Lemma lem1498968 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1483476 term57 term57 x). Qed.
Lemma lem1498970 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1498971 : term60 = term61.
Proof. exact (@lem1498970 term27 term27). Qed.
Lemma lem1498972 : (term62 = (BIT1 0)) = (term63 = term27).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1498973 : term63 = term27.
Proof. exact (EQ_MP (@lem1498972) (@lem940073)). Qed.
Lemma lem1498974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1498975 : term61 = term64.
Proof. exact (MK_COMB (@lem1498974) (@lem1498973)). Qed.
Lemma lem1498976 : term60 = term64.
Proof. exact (TRANS (@lem1498971) (@lem1498975)). Qed.
Lemma lem1498977 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498978 : term65 = term66.
Proof. exact (MK_COMB (@lem1498977) (@lem1498976)). Qed.
Lemma lem1498979 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1498980 (x : real) : (term56 x) = (term67 x).
Proof. exact (MK_COMB (@lem1498978) (@lem1498979 x)). Qed.
Lemma lem1498981 (x : real) : (term55 x) = (term67 x).
Proof. exact (TRANS (@lem1498968 x) (@lem1498980 x)). Qed.
Lemma lem1498982 (x : real) : (term67 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1498983 (x : real) : (term55 x) = x.
Proof. exact (TRANS (@lem1498981 x) (@lem1498982 x)). Qed.
Lemma lem1498984 : term68 = term68.
Proof. exact (eq_refl term68). Qed.
Lemma lem1498985 (x : real) : (term54 x) = (term69 x).
Proof. exact (MK_COMB (@lem1498984) (@lem1498983 x)). Qed.
Lemma lem1498986 (x : real) : (term69 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1498987 (x : real) : (term54 x) = x.
Proof. exact (TRANS (@lem1498985 x) (@lem1498986 x)). Qed.
Lemma lem1498988 (x : real) : (term53 x) = x.
Proof. exact (TRANS (@lem1498967 x) (@lem1498987 x)). Qed.
Lemma lem1498989 (x : real) : (term52 x) = x.
Proof. exact (TRANS (@lem1498966 x) (@lem1498988 x)). Qed.
Lemma lem1498990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498991 (x : real) : (term70 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1498990) (@lem1498989 x)). Qed.
Lemma lem1498992 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1498993 (x : real) : (term50 x) = (term71 x).
Proof. exact (MK_COMB (@lem1498991 x) (@lem1498992)). Qed.
Lemma lem1498994 (x : real) : (term49 x) = (term71 x).
Proof. exact (TRANS (@lem1498955 x) (@lem1498993 x)). Qed.
Lemma lem1498995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1498996 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem1498995) (@lem1498954 x)). Qed.
Lemma lem1498997 (x : real) : (term1 x) = (term74 x).
Proof. exact (MK_COMB (@lem1498996 x) (@lem1498994 x)). Qed.
Lemma lem1498998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1498999 (x : real) : (term4 x) = (term75 x).
Proof. exact (MK_COMB (@lem1498998) (@lem1498935 x)). Qed.
Lemma lem1499000 (x : real) : (term6 x) = (term76 x).
Proof. exact (MK_COMB (@lem1498999 x) (@lem1498997 x)). Qed.
Lemma lem1499001 : term19 = term77.
Proof. exact (fun_ext (fun x : real => @lem1499000 x)). Qed.
Lemma lem1499002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499003 : term20 = term78.
Proof. exact (MK_COMB (@lem1499002) (@lem1499001)). Qed.
Lemma lem1499058 : term12 = term78.
Proof. exact (TRANS (@lem1498899) (@lem1499003)). Qed.
Lemma lem1499081 (x : real) : (term76 x) = (term79 x).
Proof. exact (@lem19367 (term38 x) (term35 x) (term74 x)). Qed.
Lemma lem1499082 : term77 = term80.
Proof. exact (fun_ext (fun x : real => @lem1499081 x)). Qed.
Lemma lem1499083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499084 : term78 = term81.
Proof. exact (MK_COMB (@lem1499083) (@lem1499082)). Qed.
Lemma lem1499085 : term12 = term81.
Proof. exact (TRANS (@lem1499058) (@lem1499084)). Qed.
Lemma lem1499095 (x : real) (h1 : term79 x) : term79 x.
Proof. exact (h1). Qed.
Lemma lem1499096 (x : real) (h1 : term82 x) : term82 x.
Proof. exact (h1). Qed.
Lemma lem1499097 (x : real) (h1 : term82 x) : term74 x.
Proof. exact (proj2 (@lem1499096 x h1)). Qed.
Lemma lem1499098 (x : real) (h1 : term82 x) : term38 x.
Proof. exact (proj1 (@lem1499096 x h1)). Qed.
Lemma lem1499100 (x : real) (h1 : term82 x) : term48 x.
Proof. exact (proj1 (@lem1499097 x h1)). Qed.
Lemma lem1499102 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499103 : term84 = term85.
Proof. exact (@lem1499102 (NUMERAL 0) term27). Qed.
Lemma lem1499104 : term86 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1499105 (h1 : term86 = (BIT1 0)) : term85 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1499106 : (term86 = (BIT1 0)) = (term85 = True).
Proof. exact (prop_ext (fun h1 : term86 = (BIT1 0) => @lem1499105 h1) (fun h1 : term85 = True => @lem1499104)). Qed.
Lemma lem1499107 : term85 = True.
Proof. exact (EQ_MP (@lem1499106) (@lem1499104)). Qed.
Lemma lem1499108 : term84 = True.
Proof. exact (TRANS (@lem1499103) (@lem1499107)). Qed.
Lemma lem1499109 : True = term84.
Proof. exact (SYM (@lem1499108)). Qed.
Lemma lem1499110 : term84.
Proof. exact (EQ_MP (@lem1499109) (@lem0)). Qed.
Lemma lem1499111 (x : real) (h1 : term82 x) : term87 x.
Proof. exact (conj (@lem1499110) (@lem1499100 x h1)). Qed.
Lemma lem1499113 (x : real) (y : real) : term88 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1499114 (x : real) : term89 x.
Proof. exact (@lem1499113 term64 (term30 x)). Qed.
Lemma lem1499115 (x : real) (h1 : term82 x) : term90 x.
Proof. exact (@lem1499114 x (@lem1499111 x h1)). Qed.
Lemma lem1499116 (x : real) : (term91 x) = (term30 x).
Proof. exact (@lem1483460 (term30 x)). Qed.
Lemma lem1499117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1499118 (x : real) : (term92 x) = (term47 x).
Proof. exact (MK_COMB (@lem1499117) (@lem1499116 x)). Qed.
Lemma lem1499119 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499120 (x : real) : (term90 x) = (term48 x).
Proof. exact (MK_COMB (@lem1499118 x) (@lem1499119)). Qed.
Lemma lem1499121 (x : real) (h1 : term82 x) : term48 x.
Proof. exact (EQ_MP (@lem1499120 x) (@lem1499115 x h1)). Qed.
Lemma lem1499123 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499124 : term84 = term85.
Proof. exact (@lem1499123 (NUMERAL 0) term27). Qed.
Lemma lem1499125 : term86 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1499126 (h1 : term86 = (BIT1 0)) : term85 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1499127 : (term86 = (BIT1 0)) = (term85 = True).
Proof. exact (prop_ext (fun h1 : term86 = (BIT1 0) => @lem1499126 h1) (fun h1 : term85 = True => @lem1499125)). Qed.
Lemma lem1499128 : term85 = True.
Proof. exact (EQ_MP (@lem1499127) (@lem1499125)). Qed.
Lemma lem1499129 : term84 = True.
Proof. exact (TRANS (@lem1499124) (@lem1499128)). Qed.
Lemma lem1499130 : True = term84.
Proof. exact (SYM (@lem1499129)). Qed.
Lemma lem1499131 : term84.
Proof. exact (EQ_MP (@lem1499130) (@lem0)). Qed.
Lemma lem1499132 (x : real) (h1 : term82 x) : term93 x.
Proof. exact (conj (@lem1499131) (@lem1499098 x h1)). Qed.
Lemma lem1499134 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1499135 (x : real) : term95 x.
Proof. exact (@lem1499134 term64 x). Qed.
Lemma lem1499136 (x : real) (h1 : term82 x) : term96 x.
Proof. exact (@lem1499135 x (@lem1499132 x h1)). Qed.
Lemma lem1499137 (x : real) : (term67 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1499138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499139 (x : real) : (term97 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1499138) (@lem1499137 x)). Qed.
Lemma lem1499140 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499141 (x : real) : (term96 x) = (term38 x).
Proof. exact (MK_COMB (@lem1499139 x) (@lem1499140)). Qed.
Lemma lem1499142 (x : real) (h1 : term82 x) : term38 x.
Proof. exact (EQ_MP (@lem1499141 x) (@lem1499136 x h1)). Qed.
Lemma lem1499143 (x : real) (h1 : term82 x) : term98 x.
Proof. exact (conj (@lem1499142 x h1) (@lem1499121 x h1)). Qed.
Lemma lem1499145 (x : real) (y : real) : term99 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1499146 (x : real) : term100 x.
Proof. exact (@lem1499145 x (term30 x)). Qed.
Lemma lem1499147 (x : real) (h1 : term82 x) : term101 x.
Proof. exact (@lem1499146 x (@lem1499143 x h1)). Qed.
Lemma lem1499148 (x : real) : (term102 x) = (term103 x).
Proof. exact (@lem1483442 term57 x). Qed.
Lemma lem1499150 (m : nat) : (term104 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1499151 : term105 = term8.
Proof. exact (@lem1499150 term27). Qed.
Lemma lem1499152 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1499153 : term106 = term107.
Proof. exact (MK_COMB (@lem1499152) (@lem1499151)). Qed.
Lemma lem1499154 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1499155 (x : real) : (term103 x) = (term108 x).
Proof. exact (MK_COMB (@lem1499153) (@lem1499154 x)). Qed.
Lemma lem1499156 (x : real) : (term102 x) = (term108 x).
Proof. exact (TRANS (@lem1499148 x) (@lem1499155 x)). Qed.
Lemma lem1499157 (x : real) : (term108 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1499158 (x : real) : (term102 x) = term8.
Proof. exact (TRANS (@lem1499156 x) (@lem1499157 x)). Qed.
Lemma lem1499159 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499160 (x : real) : (term109 x) = term110.
Proof. exact (MK_COMB (@lem1499159) (@lem1499158 x)). Qed.
Lemma lem1499161 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499162 (x : real) : (term101 x) = term111.
Proof. exact (MK_COMB (@lem1499160 x) (@lem1499161)). Qed.
Lemma lem1499163 (x : real) (h1 : term82 x) : term111.
Proof. exact (EQ_MP (@lem1499162 x) (@lem1499147 x h1)). Qed.
Lemma lem1499165 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499166 : term111 = term112.
Proof. exact (@lem1499165 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1499167 : term112 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1499168 : term111 = False.
Proof. exact (TRANS (@lem1499166) (@lem1499167)). Qed.
Lemma lem1499169 (x : real) (h1 : term82 x) : False.
Proof. exact (EQ_MP (@lem1499168) (@lem1499163 x h1)). Qed.
Lemma lem1499170 (x : real) (h1 : term113 x) : term113 x.
Proof. exact (h1). Qed.
Lemma lem1499171 (x : real) (h1 : term113 x) : term74 x.
Proof. exact (proj2 (@lem1499170 x h1)). Qed.
Lemma lem1499172 (x : real) (h1 : term113 x) : term35 x.
Proof. exact (proj1 (@lem1499170 x h1)). Qed.
Lemma lem1499173 (x : real) (h1 : term113 x) : term71 x.
Proof. exact (proj2 (@lem1499171 x h1)). Qed.
Lemma lem1499176 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499177 : term84 = term85.
Proof. exact (@lem1499176 (NUMERAL 0) term27). Qed.
Lemma lem1499178 : term86 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1499179 (h1 : term86 = (BIT1 0)) : term85 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1499180 : (term86 = (BIT1 0)) = (term85 = True).
Proof. exact (prop_ext (fun h1 : term86 = (BIT1 0) => @lem1499179 h1) (fun h1 : term85 = True => @lem1499178)). Qed.
Lemma lem1499181 : term85 = True.
Proof. exact (EQ_MP (@lem1499180) (@lem1499178)). Qed.
Lemma lem1499182 : term84 = True.
Proof. exact (TRANS (@lem1499177) (@lem1499181)). Qed.
Lemma lem1499183 : True = term84.
Proof. exact (SYM (@lem1499182)). Qed.
Lemma lem1499184 : term84.
Proof. exact (EQ_MP (@lem1499183) (@lem0)). Qed.
Lemma lem1499185 (x : real) (h1 : term113 x) : term114 x.
Proof. exact (conj (@lem1499184) (@lem1499173 x h1)). Qed.
Lemma lem1499187 (x : real) (y : real) : term88 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1499188 (x : real) : term115 x.
Proof. exact (@lem1499187 term64 x). Qed.
Lemma lem1499189 (x : real) (h1 : term113 x) : term116 x.
Proof. exact (@lem1499188 x (@lem1499185 x h1)). Qed.
Lemma lem1499190 (x : real) : (term67 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1499191 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1499192 (x : real) : (term117 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1499191) (@lem1499190 x)). Qed.
Lemma lem1499193 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499194 (x : real) : (term116 x) = (term71 x).
Proof. exact (MK_COMB (@lem1499192 x) (@lem1499193)). Qed.
Lemma lem1499195 (x : real) (h1 : term113 x) : term71 x.
Proof. exact (EQ_MP (@lem1499194 x) (@lem1499189 x h1)). Qed.
Lemma lem1499197 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499198 : term84 = term85.
Proof. exact (@lem1499197 (NUMERAL 0) term27). Qed.
Lemma lem1499199 : term86 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1499200 (h1 : term86 = (BIT1 0)) : term85 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1499201 : (term86 = (BIT1 0)) = (term85 = True).
Proof. exact (prop_ext (fun h1 : term86 = (BIT1 0) => @lem1499200 h1) (fun h1 : term85 = True => @lem1499199)). Qed.
Lemma lem1499202 : term85 = True.
Proof. exact (EQ_MP (@lem1499201) (@lem1499199)). Qed.
Lemma lem1499203 : term84 = True.
Proof. exact (TRANS (@lem1499198) (@lem1499202)). Qed.
Lemma lem1499204 : True = term84.
Proof. exact (SYM (@lem1499203)). Qed.
Lemma lem1499205 : term84.
Proof. exact (EQ_MP (@lem1499204) (@lem0)). Qed.
Lemma lem1499206 (x : real) (h1 : term113 x) : term118 x.
Proof. exact (conj (@lem1499205) (@lem1499172 x h1)). Qed.
Lemma lem1499208 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1499209 (x : real) : term119 x.
Proof. exact (@lem1499208 term64 (term30 x)). Qed.
Lemma lem1499210 (x : real) (h1 : term113 x) : term120 x.
Proof. exact (@lem1499209 x (@lem1499206 x h1)). Qed.
Lemma lem1499211 (x : real) : (term91 x) = (term30 x).
Proof. exact (@lem1483460 (term30 x)). Qed.
Lemma lem1499212 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499213 (x : real) : (term121 x) = (term33 x).
Proof. exact (MK_COMB (@lem1499212) (@lem1499211 x)). Qed.
Lemma lem1499214 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499215 (x : real) : (term120 x) = (term35 x).
Proof. exact (MK_COMB (@lem1499213 x) (@lem1499214)). Qed.
Lemma lem1499216 (x : real) (h1 : term113 x) : term35 x.
Proof. exact (EQ_MP (@lem1499215 x) (@lem1499210 x h1)). Qed.
Lemma lem1499217 (x : real) (h1 : term113 x) : term122 x.
Proof. exact (conj (@lem1499216 x h1) (@lem1499195 x h1)). Qed.
Lemma lem1499219 (x : real) (y : real) : term99 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1499220 (x : real) : term123 x.
Proof. exact (@lem1499219 (term30 x) x). Qed.
Lemma lem1499221 (x : real) (h1 : term113 x) : term124 x.
Proof. exact (@lem1499220 x (@lem1499217 x h1)). Qed.
Lemma lem1499222 (x : real) : (term125 x) = (term103 x).
Proof. exact (@lem1483440 term57 x). Qed.
Lemma lem1499224 (m : nat) : (term104 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1499225 : term105 = term8.
Proof. exact (@lem1499224 term27). Qed.
Lemma lem1499226 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1499227 : term106 = term107.
Proof. exact (MK_COMB (@lem1499226) (@lem1499225)). Qed.
Lemma lem1499228 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1499229 (x : real) : (term103 x) = (term108 x).
Proof. exact (MK_COMB (@lem1499227) (@lem1499228 x)). Qed.
Lemma lem1499230 (x : real) : (term125 x) = (term108 x).
Proof. exact (TRANS (@lem1499222 x) (@lem1499229 x)). Qed.
Lemma lem1499231 (x : real) : (term108 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1499232 (x : real) : (term125 x) = term8.
Proof. exact (TRANS (@lem1499230 x) (@lem1499231 x)). Qed.
Lemma lem1499233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499234 (x : real) : (term126 x) = term110.
Proof. exact (MK_COMB (@lem1499233) (@lem1499232 x)). Qed.
Lemma lem1499235 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1499236 (x : real) : (term124 x) = term111.
Proof. exact (MK_COMB (@lem1499234 x) (@lem1499235)). Qed.
Lemma lem1499237 (x : real) (h1 : term113 x) : term111.
Proof. exact (EQ_MP (@lem1499236 x) (@lem1499221 x h1)). Qed.
Lemma lem1499239 (n : nat) (m : nat) : (term83 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1499240 : term111 = term112.
Proof. exact (@lem1499239 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1499241 : term112 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1499242 : term111 = False.
Proof. exact (TRANS (@lem1499240) (@lem1499241)). Qed.
Lemma lem1499243 (x : real) (h1 : term113 x) : False.
Proof. exact (EQ_MP (@lem1499242) (@lem1499237 x h1)). Qed.
Lemma lem1499244 (x : real) (h1 : term79 x) : False.
Proof. exact (or_elim (@lem1499095 x h1) (fun h0 : term82 x => @lem1499169 x h0) (fun h0 : term113 x => @lem1499243 x h0)). Qed.
Lemma lem1499246 (x : real) (h1 : term79 x) : term79 x.
Proof. exact (h1). Qed.
Lemma lem1499247 (x : real) (h1 : term79 x) : (term79 x) = False.
Proof. exact (prop_ext (fun h2 : term79 x => @lem1499244 x h1) (fun h2 : False => @lem1499246 x h1)). Qed.
Lemma lem1499248 (x : real) (h1 : term79 x) : False.
Proof. exact (EQ_MP (@lem1499247 x h1) (@lem1499246 x h1)). Qed.
Lemma lem1499249 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem1499250 (h1 : term81) : False.
Proof. exact (ex_elim (@lem1499249 h1) (fun x : real => fun h0 : term80 x => @lem1499248 x h0)). Qed.
Lemma lem1499251 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1499252 (h1 : term12) : term81.
Proof. exact (EQ_MP (@lem1499085) (@lem1499251 h1)). Qed.
Lemma lem1499253 (h1 : term12) : term81 = False.
Proof. exact (prop_ext (fun h2 : term81 => @lem1499250 h2) (fun h2 : False => @lem1499252 h1)). Qed.
Lemma lem1499254 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1499253 h1) (@lem1499252 h1)). Qed.
Lemma lem1499255 : term127.
Proof. exact (fun h0 : term12 => @lem1499254 h0). Qed.
Lemma lem1499256 : term128.
Proof. exact (@lem1386578 term129). Qed.
Lemma lem1499257 : term129.
Proof. exact (@lem1499256 (@lem1499255)). Qed.
