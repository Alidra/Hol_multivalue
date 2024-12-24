Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_BETWEEN2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367765_spec.
Require Import thm1367767_spec.
Require Import thm1367769_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483486_spec.
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
Require Import thm706887_spec.
Require Import thm706949_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1548016 (y0 : real) (x0 : real) (x : real) (y : real) : (term0 y0 x0 x y) = (term1 y0 x0 x y).
Proof. exact (@lem17362 (term2 x y y0 x0) (real_lt x y)). Qed.
Lemma lem1548017 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1548018 (y0 : real) (x0 : real) (x : real) : (term5 y0 x0 x) = (term6 y0 x0 x).
Proof. exact (@lem1548017 (term7 y0 x0 x)). Qed.
Lemma lem1548019 (y0 : real) (x0 : real) (x : real) (y : real) : (term8 y0 x0 x y) = (term9 y0 x0 x y).
Proof. exact (eq_refl (term8 y0 x0 x y)). Qed.
Lemma lem1548020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1548021 (y0 : real) (x0 : real) (x : real) (y : real) : (term10 y0 x0 x y) = (term0 y0 x0 x y).
Proof. exact (MK_COMB (@lem1548020) (@lem1548019 y0 x0 x y)). Qed.
Lemma lem1548022 (y0 : real) (x0 : real) (x : real) (y : real) : (term10 y0 x0 x y) = (term1 y0 x0 x y).
Proof. exact (TRANS (@lem1548021 y0 x0 x y) (@lem1548016 y0 x0 x y)). Qed.
Lemma lem1548023 (y0 : real) (x0 : real) (x : real) : (term11 y0 x0 x) = (term12 y0 x0 x).
Proof. exact (fun_ext (fun y : real => @lem1548022 y0 x0 x y)). Qed.
Lemma lem1548024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548025 (y0 : real) (x0 : real) (x : real) : (term6 y0 x0 x) = (term13 y0 x0 x).
Proof. exact (MK_COMB (@lem1548024) (@lem1548023 y0 x0 x)). Qed.
Lemma lem1548026 (y0 : real) (x0 : real) (x : real) : (term5 y0 x0 x) = (term13 y0 x0 x).
Proof. exact (TRANS (@lem1548018 y0 x0 x) (@lem1548025 y0 x0 x)). Qed.
Lemma lem1548027 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1548028 (x0 : real) (x : real) : (term14 x0 x) = (term15 x0 x).
Proof. exact (@lem1548027 (term16 x0 x)). Qed.
Lemma lem1548029 (y0 : real) (x0 : real) (x : real) : (term17 x0 x y0) = (term18 y0 x0 x).
Proof. exact (eq_refl (term17 x0 x y0)). Qed.
Lemma lem1548030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1548031 (y0 : real) (x0 : real) (x : real) : (term19 x0 x y0) = (term5 y0 x0 x).
Proof. exact (MK_COMB (@lem1548030) (@lem1548029 y0 x0 x)). Qed.
Lemma lem1548032 (y0 : real) (x0 : real) (x : real) : (term19 x0 x y0) = (term13 y0 x0 x).
Proof. exact (TRANS (@lem1548031 y0 x0 x) (@lem1548026 y0 x0 x)). Qed.
Lemma lem1548033 (x0 : real) (x : real) : (term20 x0 x) = (term21 x0 x).
Proof. exact (fun_ext (fun y0 : real => @lem1548032 y0 x0 x)). Qed.
Lemma lem1548034 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548035 (x0 : real) (x : real) : (term15 x0 x) = (term22 x0 x).
Proof. exact (MK_COMB (@lem1548034) (@lem1548033 x0 x)). Qed.
Lemma lem1548036 (x0 : real) (x : real) : (term14 x0 x) = (term22 x0 x).
Proof. exact (TRANS (@lem1548028 x0 x) (@lem1548035 x0 x)). Qed.
Lemma lem1548037 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1548038 (x0 : real) : (term23 x0) = (term24 x0).
Proof. exact (@lem1548037 (term25 x0)). Qed.
Lemma lem1548039 (x0 : real) (x : real) : (term26 x0 x) = (term27 x0 x).
Proof. exact (eq_refl (term26 x0 x)). Qed.
Lemma lem1548040 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1548041 (x0 : real) (x : real) : (term28 x0 x) = (term14 x0 x).
Proof. exact (MK_COMB (@lem1548040) (@lem1548039 x0 x)). Qed.
Lemma lem1548042 (x0 : real) (x : real) : (term28 x0 x) = (term22 x0 x).
Proof. exact (TRANS (@lem1548041 x0 x) (@lem1548036 x0 x)). Qed.
Lemma lem1548043 (x0 : real) : (term29 x0) = (term30 x0).
Proof. exact (fun_ext (fun x : real => @lem1548042 x0 x)). Qed.
Lemma lem1548044 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548045 (x0 : real) : (term24 x0) = (term31 x0).
Proof. exact (MK_COMB (@lem1548044) (@lem1548043 x0)). Qed.
Lemma lem1548046 (x0 : real) : (term23 x0) = (term31 x0).
Proof. exact (TRANS (@lem1548038 x0) (@lem1548045 x0)). Qed.
Lemma lem1548047 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1548048 : term32 = term33.
Proof. exact (@lem1548047 term34). Qed.
Lemma lem1548049 (x0 : real) : (term35 x0) = (term36 x0).
Proof. exact (eq_refl (term35 x0)). Qed.
Lemma lem1548050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1548051 (x0 : real) : (term37 x0) = (term23 x0).
Proof. exact (MK_COMB (@lem1548050) (@lem1548049 x0)). Qed.
Lemma lem1548052 (x0 : real) : (term37 x0) = (term31 x0).
Proof. exact (TRANS (@lem1548051 x0) (@lem1548046 x0)). Qed.
Lemma lem1548053 : term38 = term39.
Proof. exact (fun_ext (fun x0 : real => @lem1548052 x0)). Qed.
Lemma lem1548054 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548055 : term33 = term40.
Proof. exact (MK_COMB (@lem1548054) (@lem1548053)). Qed.
Lemma lem1548057 : term32 = term40.
Proof. exact (TRANS (@lem1548048) (@lem1548055)). Qed.
Lemma lem1548072 (y0 : real) (x0 : real) (x : real) (y : real) : (term1 y0 x0 x y) = (term1 y0 x0 x y).
Proof. exact (eq_refl (term1 y0 x0 x y)). Qed.
Lemma lem1548073 (y0 : real) (x0 : real) (x : real) : (term12 y0 x0 x) = (term12 y0 x0 x).
Proof. exact (fun_ext (fun y : real => @lem1548072 y0 x0 x y)). Qed.
Lemma lem1548074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548075 (y0 : real) (x0 : real) (x : real) : (term13 y0 x0 x) = (term13 y0 x0 x).
Proof. exact (MK_COMB (@lem1548074) (@lem1548073 y0 x0 x)). Qed.
Lemma lem1548076 (x0 : real) (x : real) : (term21 x0 x) = (term21 x0 x).
Proof. exact (fun_ext (fun y0 : real => @lem1548075 y0 x0 x)). Qed.
Lemma lem1548077 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548078 (x0 : real) (x : real) : (term22 x0 x) = (term22 x0 x).
Proof. exact (MK_COMB (@lem1548077) (@lem1548076 x0 x)). Qed.
Lemma lem1548079 (x0 : real) : (term30 x0) = (term30 x0).
Proof. exact (fun_ext (fun x : real => @lem1548078 x0 x)). Qed.
Lemma lem1548080 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548081 (x0 : real) : (term31 x0) = (term31 x0).
Proof. exact (MK_COMB (@lem1548080) (@lem1548079 x0)). Qed.
Lemma lem1548082 : term39 = term39.
Proof. exact (fun_ext (fun x0 : real => @lem1548081 x0)). Qed.
Lemma lem1548083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548084 : term40 = term40.
Proof. exact (MK_COMB (@lem1548083) (@lem1548082)). Qed.
Lemma lem1548085 : term32 = term40.
Proof. exact (TRANS (@lem1548057) (@lem1548084)). Qed.
Lemma lem1548086 (y0 : real) (x0 : real) : (real_lt x0 y0) = (term41 y0 x0).
Proof. exact (@lem1483521 y0 x0). Qed.
Lemma lem1548092 (y0 : real) (x0 : real) : (real_sub y0 x0) = (term42 y0 x0).
Proof. exact (@lem1483519 y0 x0). Qed.
Lemma lem1548097 (x0 : real) (y0 : real) : (term42 y0 x0) = (term43 x0 y0).
Proof. exact (@lem1483488 (term44 x0) y0). Qed.
Lemma lem1548099 (x0 : real) (y0 : real) : (real_sub y0 x0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1548092 y0 x0) (@lem1548097 x0 y0)). Qed.
Lemma lem1548100 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548101 (x0 : real) (y0 : real) : (term45 y0 x0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1548100) (@lem1548099 x0 y0)). Qed.
Lemma lem1548102 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548103 (x0 : real) (y0 : real) : (term41 y0 x0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1548101 x0 y0) (@lem1548102)). Qed.
Lemma lem1548104 (x0 : real) (y0 : real) : (real_lt x0 y0) = (term48 x0 y0).
Proof. exact (TRANS (@lem1548086 y0 x0) (@lem1548103 x0 y0)). Qed.
Lemma lem1548105 (y0 : real) (x : real) (x0 : real) : (term49 x y0 x0) = (term50 y0 x x0).
Proof. exact (@lem1483521 (real_sub y0 x0) (term51 x x0)). Qed.
Lemma lem1548112 (x : real) (x0 : real) : (term51 x x0) = (term51 x x0).
Proof. exact (eq_refl (term51 x x0)). Qed.
Lemma lem1548118 (y0 : real) (x0 : real) : (real_sub y0 x0) = (term42 y0 x0).
Proof. exact (@lem1483519 y0 x0). Qed.
Lemma lem1548123 (x0 : real) (y0 : real) : (term42 y0 x0) = (term43 x0 y0).
Proof. exact (@lem1483488 (term44 x0) y0). Qed.
Lemma lem1548125 (x0 : real) (y0 : real) : (real_sub y0 x0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1548118 y0 x0) (@lem1548123 x0 y0)). Qed.
Lemma lem1548126 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548127 (x0 : real) (y0 : real) : (term52 y0 x0) = (term53 x0 y0).
Proof. exact (MK_COMB (@lem1548126) (@lem1548125 x0 y0)). Qed.
Lemma lem1548128 (y0 : real) (x : real) (x0 : real) : (term54 y0 x x0) = (term55 y0 x x0).
Proof. exact (MK_COMB (@lem1548127 x0 y0) (@lem1548112 x x0)). Qed.
Lemma lem1548129 (y0 : real) (x : real) (x0 : real) : (term55 y0 x x0) = (term56 y0 x x0).
Proof. exact (@lem1483519 (term43 x0 y0) (term51 x x0)). Qed.
Lemma lem1548130 (x : real) (x0 : real) : (term57 x x0) = (term58 x x0).
Proof. exact (@lem1483476 term59 term60 (term61 x x0)). Qed.
Lemma lem1548132 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1548133 : term64 = term65.
Proof. exact (@lem1548132 term66 term67). Qed.
Lemma lem1548134 : term68 = term69.
Proof. exact (@lem996238 term69). Qed.
Lemma lem1548135 : (term68 = term69) = (term70 = term67).
Proof. exact (@lem1007663 (BIT1 0) term69 term69). Qed.
Lemma lem1548136 : term70 = term67.
Proof. exact (EQ_MP (@lem1548135) (@lem1548134)). Qed.
Lemma lem1548137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548138 : term71 = term60.
Proof. exact (MK_COMB (@lem1548137) (@lem1548136)). Qed.
Lemma lem1548139 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1548140 : term65 = term72.
Proof. exact (MK_COMB (@lem1548139) (@lem1548138)). Qed.
Lemma lem1548141 : term64 = term72.
Proof. exact (TRANS (@lem1548133) (@lem1548140)). Qed.
Lemma lem1548142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548143 : term73 = term74.
Proof. exact (MK_COMB (@lem1548142) (@lem1548141)). Qed.
Lemma lem1548144 (x : real) (x0 : real) : (term61 x x0) = (term61 x x0).
Proof. exact (eq_refl (term61 x x0)). Qed.
Lemma lem1548145 (x : real) (x0 : real) : (term58 x x0) = (term75 x x0).
Proof. exact (MK_COMB (@lem1548143) (@lem1548144 x x0)). Qed.
Lemma lem1548146 (x : real) (x0 : real) : (term57 x x0) = (term75 x x0).
Proof. exact (TRANS (@lem1548130 x x0) (@lem1548145 x x0)). Qed.
Lemma lem1548147 (x0 : real) (y0 : real) : (term76 x0 y0) = (term76 x0 y0).
Proof. exact (eq_refl (term76 x0 y0)). Qed.
Lemma lem1548148 (y0 : real) (x : real) (x0 : real) : (term56 y0 x x0) = (term77 y0 x x0).
Proof. exact (MK_COMB (@lem1548147 x0 y0) (@lem1548146 x x0)). Qed.
Lemma lem1548153 (y0 : real) (x : real) (x0 : real) : (term77 y0 x x0) = (term78 y0 x x0).
Proof. exact (@lem1483482 (term44 x0) y0 (term75 x x0)). Qed.
Lemma lem1548154 (y0 : real) (x : real) (x0 : real) : (term56 y0 x x0) = (term78 y0 x x0).
Proof. exact (TRANS (@lem1548148 y0 x x0) (@lem1548153 y0 x x0)). Qed.
Lemma lem1548155 (y0 : real) (x : real) (x0 : real) : (term55 y0 x x0) = (term78 y0 x x0).
Proof. exact (TRANS (@lem1548129 y0 x x0) (@lem1548154 y0 x x0)). Qed.
Lemma lem1548156 (y0 : real) (x : real) (x0 : real) : (term54 y0 x x0) = (term78 y0 x x0).
Proof. exact (TRANS (@lem1548128 y0 x x0) (@lem1548155 y0 x x0)). Qed.
Lemma lem1548157 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548158 (y0 : real) (x : real) (x0 : real) : (term79 y0 x x0) = (term80 y0 x x0).
Proof. exact (MK_COMB (@lem1548157) (@lem1548156 y0 x x0)). Qed.
Lemma lem1548159 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548160 (y0 : real) (x : real) (x0 : real) : (term50 y0 x x0) = (term81 y0 x x0).
Proof. exact (MK_COMB (@lem1548158 y0 x x0) (@lem1548159)). Qed.
Lemma lem1548161 (y0 : real) (x : real) (x0 : real) : (term49 x y0 x0) = (term81 y0 x x0).
Proof. exact (TRANS (@lem1548105 y0 x x0) (@lem1548160 y0 x x0)). Qed.
Lemma lem1548162 (x0 : real) (y : real) (y0 : real) : (term82 y y0 x0) = (term83 x0 y y0).
Proof. exact (@lem1483521 (real_sub y0 x0) (term51 y y0)). Qed.
Lemma lem1548169 (y : real) (y0 : real) : (term51 y y0) = (term51 y y0).
Proof. exact (eq_refl (term51 y y0)). Qed.
Lemma lem1548175 (y0 : real) (x0 : real) : (real_sub y0 x0) = (term42 y0 x0).
Proof. exact (@lem1483519 y0 x0). Qed.
Lemma lem1548180 (x0 : real) (y0 : real) : (term42 y0 x0) = (term43 x0 y0).
Proof. exact (@lem1483488 (term44 x0) y0). Qed.
Lemma lem1548182 (x0 : real) (y0 : real) : (real_sub y0 x0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1548175 y0 x0) (@lem1548180 x0 y0)). Qed.
Lemma lem1548183 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548184 (x0 : real) (y0 : real) : (term52 y0 x0) = (term53 x0 y0).
Proof. exact (MK_COMB (@lem1548183) (@lem1548182 x0 y0)). Qed.
Lemma lem1548185 (x0 : real) (y : real) (y0 : real) : (term84 x0 y y0) = (term85 x0 y y0).
Proof. exact (MK_COMB (@lem1548184 x0 y0) (@lem1548169 y y0)). Qed.
Lemma lem1548186 (x0 : real) (y : real) (y0 : real) : (term85 x0 y y0) = (term86 x0 y y0).
Proof. exact (@lem1483519 (term43 x0 y0) (term51 y y0)). Qed.
Lemma lem1548187 (y : real) (y0 : real) : (term57 y y0) = (term58 y y0).
Proof. exact (@lem1483476 term59 term60 (term61 y y0)). Qed.
Lemma lem1548189 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1548190 : term64 = term65.
Proof. exact (@lem1548189 term66 term67). Qed.
Lemma lem1548191 : term68 = term69.
Proof. exact (@lem996238 term69). Qed.
Lemma lem1548192 : (term68 = term69) = (term70 = term67).
Proof. exact (@lem1007663 (BIT1 0) term69 term69). Qed.
Lemma lem1548193 : term70 = term67.
Proof. exact (EQ_MP (@lem1548192) (@lem1548191)). Qed.
Lemma lem1548194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548195 : term71 = term60.
Proof. exact (MK_COMB (@lem1548194) (@lem1548193)). Qed.
Lemma lem1548196 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1548197 : term65 = term72.
Proof. exact (MK_COMB (@lem1548196) (@lem1548195)). Qed.
Lemma lem1548198 : term64 = term72.
Proof. exact (TRANS (@lem1548190) (@lem1548197)). Qed.
Lemma lem1548199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548200 : term73 = term74.
Proof. exact (MK_COMB (@lem1548199) (@lem1548198)). Qed.
Lemma lem1548201 (y : real) (y0 : real) : (term61 y y0) = (term61 y y0).
Proof. exact (eq_refl (term61 y y0)). Qed.
Lemma lem1548202 (y : real) (y0 : real) : (term58 y y0) = (term75 y y0).
Proof. exact (MK_COMB (@lem1548200) (@lem1548201 y y0)). Qed.
Lemma lem1548203 (y : real) (y0 : real) : (term57 y y0) = (term75 y y0).
Proof. exact (TRANS (@lem1548187 y y0) (@lem1548202 y y0)). Qed.
Lemma lem1548204 (x0 : real) (y0 : real) : (term76 x0 y0) = (term76 x0 y0).
Proof. exact (eq_refl (term76 x0 y0)). Qed.
Lemma lem1548205 (x0 : real) (y : real) (y0 : real) : (term86 x0 y y0) = (term87 x0 y y0).
Proof. exact (MK_COMB (@lem1548204 x0 y0) (@lem1548203 y y0)). Qed.
Lemma lem1548210 (x0 : real) (y : real) (y0 : real) : (term87 x0 y y0) = (term88 x0 y y0).
Proof. exact (@lem1483482 (term44 x0) y0 (term75 y y0)). Qed.
Lemma lem1548211 (x0 : real) (y : real) (y0 : real) : (term86 x0 y y0) = (term88 x0 y y0).
Proof. exact (TRANS (@lem1548205 x0 y y0) (@lem1548210 x0 y y0)). Qed.
Lemma lem1548212 (x0 : real) (y : real) (y0 : real) : (term85 x0 y y0) = (term88 x0 y y0).
Proof. exact (TRANS (@lem1548186 x0 y y0) (@lem1548211 x0 y y0)). Qed.
Lemma lem1548213 (x0 : real) (y : real) (y0 : real) : (term84 x0 y y0) = (term88 x0 y y0).
Proof. exact (TRANS (@lem1548185 x0 y y0) (@lem1548212 x0 y y0)). Qed.
Lemma lem1548214 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548215 (x0 : real) (y : real) (y0 : real) : (term89 x0 y y0) = (term90 x0 y y0).
Proof. exact (MK_COMB (@lem1548214) (@lem1548213 x0 y y0)). Qed.
Lemma lem1548216 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548217 (x0 : real) (y : real) (y0 : real) : (term83 x0 y y0) = (term91 x0 y y0).
Proof. exact (MK_COMB (@lem1548215 x0 y y0) (@lem1548216)). Qed.
Lemma lem1548218 (x0 : real) (y : real) (y0 : real) : (term82 y y0 x0) = (term91 x0 y y0).
Proof. exact (TRANS (@lem1548162 x0 y y0) (@lem1548217 x0 y y0)). Qed.
Lemma lem1548219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548220 (y0 : real) (x : real) (x0 : real) : (term92 x y0 x0) = (term93 y0 x x0).
Proof. exact (MK_COMB (@lem1548219) (@lem1548161 y0 x x0)). Qed.
Lemma lem1548221 (x : real) (x0 : real) (y : real) (y0 : real) : (term94 x y y0 x0) = (term95 x x0 y y0).
Proof. exact (MK_COMB (@lem1548220 y0 x x0) (@lem1548218 x0 y y0)). Qed.
Lemma lem1548222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548223 (x0 : real) (y0 : real) : (term96 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1548222) (@lem1548104 x0 y0)). Qed.
Lemma lem1548224 (x : real) (x0 : real) (y : real) (y0 : real) : (term2 x y y0 x0) = (term98 x x0 y y0).
Proof. exact (MK_COMB (@lem1548223 x0 y0) (@lem1548221 x x0 y y0)). Qed.
Lemma lem1548225 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (@lem1483531 x y). Qed.
Lemma lem1548238 (x : real) (y : real) : (real_sub x y) = (term42 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1548239 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1548240 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1548239) (@lem1548238 x y)). Qed.
Lemma lem1548241 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548242 (x : real) (y : real) : (term100 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1548240 x y) (@lem1548241)). Qed.
Lemma lem1548243 (x : real) (y : real) : (term99 x y) = (term103 x y).
Proof. exact (TRANS (@lem1548225 x y) (@lem1548242 x y)). Qed.
Lemma lem1548244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548245 (x : real) (x0 : real) (y : real) (y0 : real) : (term104 x y y0 x0) = (term105 x x0 y y0).
Proof. exact (MK_COMB (@lem1548244) (@lem1548224 x x0 y y0)). Qed.
Lemma lem1548246 (x0 : real) (y0 : real) (x : real) (y : real) : (term1 y0 x0 x y) = (term106 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548245 x x0 y y0) (@lem1548243 x y)). Qed.
Lemma lem1548247 (x0 : real) (y0 : real) (x : real) : (term12 y0 x0 x) = (term107 x0 y0 x).
Proof. exact (fun_ext (fun y : real => @lem1548246 x0 y0 x y)). Qed.
Lemma lem1548248 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548249 (x0 : real) (y0 : real) (x : real) : (term13 y0 x0 x) = (term108 x0 y0 x).
Proof. exact (MK_COMB (@lem1548248) (@lem1548247 x0 y0 x)). Qed.
Lemma lem1548250 (x0 : real) (x : real) : (term21 x0 x) = (term109 x0 x).
Proof. exact (fun_ext (fun y0 : real => @lem1548249 x0 y0 x)). Qed.
Lemma lem1548251 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548252 (x0 : real) (x : real) : (term22 x0 x) = (term110 x0 x).
Proof. exact (MK_COMB (@lem1548251) (@lem1548250 x0 x)). Qed.
Lemma lem1548253 (x0 : real) : (term30 x0) = (term111 x0).
Proof. exact (fun_ext (fun x : real => @lem1548252 x0 x)). Qed.
Lemma lem1548254 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548255 (x0 : real) : (term31 x0) = (term112 x0).
Proof. exact (MK_COMB (@lem1548254) (@lem1548253 x0)). Qed.
Lemma lem1548256 : term39 = term113.
Proof. exact (fun_ext (fun x0 : real => @lem1548255 x0)). Qed.
Lemma lem1548257 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548258 : term40 = term114.
Proof. exact (MK_COMB (@lem1548257) (@lem1548256)). Qed.
Lemma lem1548325 : term32 = term114.
Proof. exact (TRANS (@lem1548085) (@lem1548258)). Qed.
Lemma lem1548344 (x0 : real) (y0 : real) (x : real) (y : real) : (term106 x0 y0 x y) = (term106 x0 y0 x y).
Proof. exact (eq_refl (term106 x0 y0 x y)). Qed.
Lemma lem1548345 (x0 : real) (y0 : real) (x : real) : (term107 x0 y0 x) = (term107 x0 y0 x).
Proof. exact (fun_ext (fun y : real => @lem1548344 x0 y0 x y)). Qed.
Lemma lem1548346 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548347 (x0 : real) (y0 : real) (x : real) : (term108 x0 y0 x) = (term108 x0 y0 x).
Proof. exact (MK_COMB (@lem1548346) (@lem1548345 x0 y0 x)). Qed.
Lemma lem1548348 (x0 : real) (x : real) : (term109 x0 x) = (term109 x0 x).
Proof. exact (fun_ext (fun y0 : real => @lem1548347 x0 y0 x)). Qed.
Lemma lem1548349 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548350 (x0 : real) (x : real) : (term110 x0 x) = (term110 x0 x).
Proof. exact (MK_COMB (@lem1548349) (@lem1548348 x0 x)). Qed.
Lemma lem1548351 (x0 : real) : (term111 x0) = (term111 x0).
Proof. exact (fun_ext (fun x : real => @lem1548350 x0 x)). Qed.
Lemma lem1548352 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548353 (x0 : real) : (term112 x0) = (term112 x0).
Proof. exact (MK_COMB (@lem1548352) (@lem1548351 x0)). Qed.
Lemma lem1548354 : term113 = term113.
Proof. exact (fun_ext (fun x0 : real => @lem1548353 x0)). Qed.
Lemma lem1548355 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1548356 : term114 = term114.
Proof. exact (MK_COMB (@lem1548355) (@lem1548354)). Qed.
Lemma lem1548357 : term32 = term114.
Proof. exact (TRANS (@lem1548325) (@lem1548356)). Qed.
Lemma lem1548359 (x0 : real) (y0 : real) (x : real) (y : real) : (term115 y0 y x x0) = (term106 x0 y0 x y).
Proof. exact (eq_refl (term115 y0 y x x0)). Qed.
Lemma lem1548360 (y0 : real) (y : real) (x : real) (x0 : real) : (term106 x0 y0 x y) = (term115 y0 y x x0).
Proof. exact (SYM (@lem1548359 x0 y0 x y)). Qed.
Lemma lem1548361 (y0 : real) (y : real) (x : real) (x0 : real) : (term115 y0 y x x0) = (term116 y0 y x x0).
Proof. exact (@lem1482981 (term117 x0 y0 x y) (real_sub x x0)). Qed.
Lemma lem1548362 (y0 : real) (y : real) (x : real) (x0 : real) : (term106 x0 y0 x y) = (term116 y0 y x x0).
Proof. exact (TRANS (@lem1548360 y0 y x x0) (@lem1548361 y0 y x x0)). Qed.
Lemma lem1548363 (x0 : real) (y0 : real) (x : real) (y : real) : (term118 y0 y x x0) = (term119 x0 y0 x y).
Proof. exact (eq_refl (term118 y0 y x x0)). Qed.
Lemma lem1548364 (x : real) (x0 : real) : (term120 x x0) = (term120 x x0).
Proof. exact (eq_refl (term120 x x0)). Qed.
Lemma lem1548365 (x0 : real) (y0 : real) (x : real) (y : real) : (term121 y0 y x x0) = (term122 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548364 x x0) (@lem1548363 x0 y0 x y)). Qed.
Lemma lem1548366 (x0 : real) (y0 : real) (x : real) (y : real) : (term123 y0 y x x0) = (term124 x0 y0 x y).
Proof. exact (eq_refl (term123 y0 y x x0)). Qed.
Lemma lem1548367 (x : real) (x0 : real) : (term125 x x0) = (term125 x x0).
Proof. exact (eq_refl (term125 x x0)). Qed.
Lemma lem1548368 (x0 : real) (y0 : real) (x : real) (y : real) : (term126 y0 y x x0) = (term127 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548367 x x0) (@lem1548366 x0 y0 x y)). Qed.
Lemma lem1548369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1548370 (x0 : real) (y0 : real) (x : real) (y : real) : (term128 y0 y x x0) = (term129 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548369) (@lem1548368 x0 y0 x y)). Qed.
Lemma lem1548371 (x0 : real) (y0 : real) (x : real) (y : real) : (term116 y0 y x x0) = (term130 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548370 x0 y0 x y) (@lem1548365 x0 y0 x y)). Qed.
Lemma lem1548372 (x0 : real) (y0 : real) (x : real) (y : real) : (term131 x0 y0 x y) = (term131 x0 y0 x y).
Proof. exact (eq_refl (term131 x0 y0 x y)). Qed.
Lemma lem1548373 (x0 : real) (y0 : real) (x : real) (y : real) : ((term106 x0 y0 x y) = (term116 y0 y x x0)) = ((term106 x0 y0 x y) = (term130 x0 y0 x y)).
Proof. exact (MK_COMB (@lem1548372 x0 y0 x y) (@lem1548371 x0 y0 x y)). Qed.
Lemma lem1548374 (x0 : real) (y0 : real) (x : real) (y : real) : (term106 x0 y0 x y) = (term130 x0 y0 x y).
Proof. exact (EQ_MP (@lem1548373 x0 y0 x y) (@lem1548362 y0 y x x0)). Qed.
Lemma lem1548375 (x : real) (x0 : real) : (term100 x x0) = (term132 x x0).
Proof. exact (@lem1483527 (real_sub x x0) term47). Qed.
Lemma lem1548376 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548389 (x : real) (x0 : real) : (real_sub x x0) = (term42 x x0).
Proof. exact (@lem1483519 x x0). Qed.
Lemma lem1548390 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548391 (x : real) (x0 : real) : (term52 x x0) = (term133 x x0).
Proof. exact (MK_COMB (@lem1548390) (@lem1548389 x x0)). Qed.
Lemma lem1548392 (x : real) (x0 : real) : (term134 x x0) = (term135 x x0).
Proof. exact (MK_COMB (@lem1548391 x x0) (@lem1548376)). Qed.
Lemma lem1548393 (x : real) (x0 : real) : (term135 x x0) = (term136 x x0).
Proof. exact (@lem1483519 (term42 x x0) term47). Qed.
Lemma lem1548395 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548396 : term138 = term47.
Proof. exact (@lem1548395 term66). Qed.
Lemma lem1548397 (x : real) (x0 : real) : (term139 x x0) = (term139 x x0).
Proof. exact (eq_refl (term139 x x0)). Qed.
Lemma lem1548398 (x : real) (x0 : real) : (term136 x x0) = (term140 x x0).
Proof. exact (MK_COMB (@lem1548397 x x0) (@lem1548396)). Qed.
Lemma lem1548399 (x : real) (x0 : real) : (term140 x x0) = (term42 x x0).
Proof. exact (@lem1483450 (term42 x x0)). Qed.
Lemma lem1548400 (x : real) (x0 : real) : (term136 x x0) = (term42 x x0).
Proof. exact (TRANS (@lem1548398 x x0) (@lem1548399 x x0)). Qed.
Lemma lem1548401 (x : real) (x0 : real) : (term135 x x0) = (term42 x x0).
Proof. exact (TRANS (@lem1548393 x x0) (@lem1548400 x x0)). Qed.
Lemma lem1548402 (x : real) (x0 : real) : (term134 x x0) = (term42 x x0).
Proof. exact (TRANS (@lem1548392 x x0) (@lem1548401 x x0)). Qed.
Lemma lem1548403 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1548404 (x : real) (x0 : real) : (term141 x x0) = (term102 x x0).
Proof. exact (MK_COMB (@lem1548403) (@lem1548402 x x0)). Qed.
Lemma lem1548405 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548406 (x : real) (x0 : real) : (term132 x x0) = (term103 x x0).
Proof. exact (MK_COMB (@lem1548404 x x0) (@lem1548405)). Qed.
Lemma lem1548407 (x : real) (x0 : real) : (term100 x x0) = (term103 x x0).
Proof. exact (TRANS (@lem1548375 x x0) (@lem1548406 x x0)). Qed.
Lemma lem1548408 (x0 : real) (y0 : real) : (term48 x0 y0) = (term142 x0 y0).
Proof. exact (@lem1483525 (term43 x0 y0) term47). Qed.
Lemma lem1548426 (x0 : real) (y0 : real) : (term143 x0 y0) = (term144 x0 y0).
Proof. exact (@lem1483519 (term43 x0 y0) term47). Qed.
Lemma lem1548428 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548429 : term138 = term47.
Proof. exact (@lem1548428 term66). Qed.
Lemma lem1548430 (x0 : real) (y0 : real) : (term76 x0 y0) = (term76 x0 y0).
Proof. exact (eq_refl (term76 x0 y0)). Qed.
Lemma lem1548431 (x0 : real) (y0 : real) : (term144 x0 y0) = (term145 x0 y0).
Proof. exact (MK_COMB (@lem1548430 x0 y0) (@lem1548429)). Qed.
Lemma lem1548432 (x0 : real) (y0 : real) : (term145 x0 y0) = (term43 x0 y0).
Proof. exact (@lem1483450 (term43 x0 y0)). Qed.
Lemma lem1548433 (x0 : real) (y0 : real) : (term144 x0 y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1548431 x0 y0) (@lem1548432 x0 y0)). Qed.
Lemma lem1548435 (x0 : real) (y0 : real) : (term143 x0 y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1548426 x0 y0) (@lem1548433 x0 y0)). Qed.
Lemma lem1548436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548437 (x0 : real) (y0 : real) : (term146 x0 y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1548436) (@lem1548435 x0 y0)). Qed.
Lemma lem1548438 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548439 (x0 : real) (y0 : real) : (term142 x0 y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1548437 x0 y0) (@lem1548438)). Qed.
Lemma lem1548440 (x0 : real) (y0 : real) : (term48 x0 y0) = (term48 x0 y0).
Proof. exact (TRANS (@lem1548408 x0 y0) (@lem1548439 x0 y0)). Qed.
Lemma lem1548441 (y0 : real) (x : real) (x0 : real) : (term147 y0 x x0) = (term148 y0 x x0).
Proof. exact (@lem1483525 (term149 y0 x x0) term47). Qed.
Lemma lem1548442 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548455 (x : real) (x0 : real) : (real_sub x x0) = (term42 x x0).
Proof. exact (@lem1483519 x x0). Qed.
Lemma lem1548458 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1548459 (x : real) (x0 : real) : (term150 x x0) = (term151 x x0).
Proof. exact (MK_COMB (@lem1548458) (@lem1548455 x x0)). Qed.
Lemma lem1548460 (x : real) (x0 : real) : (term151 x x0) = (term152 x x0).
Proof. exact (@lem1483508 x term72 (term44 x0)). Qed.
Lemma lem1548461 (x0 : real) : (term153 x0) = (term154 x0).
Proof. exact (@lem1483476 term72 term59 x0). Qed.
Lemma lem1548463 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1548464 : term157 = term158.
Proof. exact (@lem1548463 term67 term66). Qed.
Lemma lem1548465 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1548466 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1548467 : term160 = term67.
Proof. exact (EQ_MP (@lem1548466) (@lem1548465)). Qed.
Lemma lem1548468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548469 : term158 = term60.
Proof. exact (MK_COMB (@lem1548468) (@lem1548467)). Qed.
Lemma lem1548470 : term157 = term60.
Proof. exact (TRANS (@lem1548464) (@lem1548469)). Qed.
Lemma lem1548471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548472 : term161 = term162.
Proof. exact (MK_COMB (@lem1548471) (@lem1548470)). Qed.
Lemma lem1548473 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1548474 (x0 : real) : (term154 x0) = (term163 x0).
Proof. exact (MK_COMB (@lem1548472) (@lem1548473 x0)). Qed.
Lemma lem1548475 (x0 : real) : (term153 x0) = (term163 x0).
Proof. exact (TRANS (@lem1548461 x0) (@lem1548474 x0)). Qed.
Lemma lem1548478 (x : real) : (term164 x) = (term164 x).
Proof. exact (eq_refl (term164 x)). Qed.
Lemma lem1548479 (x : real) (x0 : real) : (term152 x x0) = (term165 x x0).
Proof. exact (MK_COMB (@lem1548478 x) (@lem1548475 x0)). Qed.
Lemma lem1548480 (x : real) (x0 : real) : (term151 x x0) = (term165 x x0).
Proof. exact (TRANS (@lem1548460 x x0) (@lem1548479 x x0)). Qed.
Lemma lem1548481 (x : real) (x0 : real) : (term150 x x0) = (term165 x x0).
Proof. exact (TRANS (@lem1548459 x x0) (@lem1548480 x x0)). Qed.
Lemma lem1548484 (y0 : real) : (real_add y0) = (real_add y0).
Proof. exact (eq_refl (real_add y0)). Qed.
Lemma lem1548485 (y0 : real) (x : real) (x0 : real) : (term166 y0 x x0) = (term167 y0 x x0).
Proof. exact (MK_COMB (@lem1548484 y0) (@lem1548481 x x0)). Qed.
Lemma lem1548486 (x : real) (y0 : real) (x0 : real) : (term167 y0 x x0) = (term168 x y0 x0).
Proof. exact (@lem1483484 (term169 x) y0 (term163 x0)). Qed.
Lemma lem1548487 (x0 : real) (y0 : real) : (term170 y0 x0) = (term171 x0 y0).
Proof. exact (@lem1483488 (term163 x0) y0). Qed.
Lemma lem1548488 (x : real) : (term164 x) = (term164 x).
Proof. exact (eq_refl (term164 x)). Qed.
Lemma lem1548489 (x : real) (x0 : real) (y0 : real) : (term168 x y0 x0) = (term172 x x0 y0).
Proof. exact (MK_COMB (@lem1548488 x) (@lem1548487 x0 y0)). Qed.
Lemma lem1548490 (x : real) (x0 : real) (y0 : real) : (term167 y0 x x0) = (term172 x x0 y0).
Proof. exact (TRANS (@lem1548486 x y0 x0) (@lem1548489 x x0 y0)). Qed.
Lemma lem1548491 (x : real) (x0 : real) (y0 : real) : (term166 y0 x x0) = (term172 x x0 y0).
Proof. exact (TRANS (@lem1548485 y0 x x0) (@lem1548490 x x0 y0)). Qed.
Lemma lem1548500 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1548501 (x : real) (x0 : real) (y0 : real) : (term149 y0 x x0) = (term174 x x0 y0).
Proof. exact (MK_COMB (@lem1548500 x0) (@lem1548491 x x0 y0)). Qed.
Lemma lem1548502 (x : real) (x0 : real) (y0 : real) : (term174 x x0 y0) = (term175 x x0 y0).
Proof. exact (@lem1483484 (term169 x) (term44 x0) (term171 x0 y0)). Qed.
Lemma lem1548503 (x0 : real) (y0 : real) : (term176 x0 y0) = (term177 x0 y0).
Proof. exact (@lem1483490 (term44 x0) (term163 x0) y0). Qed.
Lemma lem1548504 (x0 : real) : (term178 x0) = (term179 x0).
Proof. exact (@lem1483438 term59 term60 x0). Qed.
Lemma lem1548507 : term180 = term181.
Proof. exact (@lem1367765 term66 term66). Qed.
Lemma lem1548508 : term182 = term69.
Proof. exact (@lem706885). Qed.
Lemma lem1548509 : (term182 = term69) = (term183 = term67).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term69). Qed.
Lemma lem1548510 : term183 = term67.
Proof. exact (EQ_MP (@lem1548509) (@lem1548508)). Qed.
Lemma lem1548511 : term67 = term183.
Proof. exact (SYM (@lem1548510)). Qed.
Lemma lem1548512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548513 : term60 = term184.
Proof. exact (MK_COMB (@lem1548512) (@lem1548511)). Qed.
Lemma lem1548514 : term185 = term185.
Proof. exact (eq_refl term185). Qed.
Lemma lem1548515 : term186 = term180.
Proof. exact (MK_COMB (@lem1548514) (@lem1548513)). Qed.
Lemma lem1548516 : term186 = term181.
Proof. exact (TRANS (@lem1548515) (@lem1548507)). Qed.
Lemma lem1548517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548518 : term187 = term188.
Proof. exact (MK_COMB (@lem1548517) (@lem1548516)). Qed.
Lemma lem1548519 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1548520 (x0 : real) : (term179 x0) = (term189 x0).
Proof. exact (MK_COMB (@lem1548518) (@lem1548519 x0)). Qed.
Lemma lem1548521 (x0 : real) : (term178 x0) = (term189 x0).
Proof. exact (TRANS (@lem1548504 x0) (@lem1548520 x0)). Qed.
Lemma lem1548522 (x0 : real) : (term189 x0) = x0.
Proof. exact (@lem1483436 x0). Qed.
Lemma lem1548523 (x0 : real) : (term178 x0) = x0.
Proof. exact (TRANS (@lem1548521 x0) (@lem1548522 x0)). Qed.
Lemma lem1548524 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1548525 (x0 : real) : (term190 x0) = (real_add x0).
Proof. exact (MK_COMB (@lem1548524) (@lem1548523 x0)). Qed.
Lemma lem1548526 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1548527 (x0 : real) (y0 : real) : (term177 x0 y0) = (real_add x0 y0).
Proof. exact (MK_COMB (@lem1548525 x0) (@lem1548526 y0)). Qed.
Lemma lem1548528 (x0 : real) (y0 : real) : (term176 x0 y0) = (real_add x0 y0).
Proof. exact (TRANS (@lem1548503 x0 y0) (@lem1548527 x0 y0)). Qed.
Lemma lem1548529 (x : real) : (term164 x) = (term164 x).
Proof. exact (eq_refl (term164 x)). Qed.
Lemma lem1548530 (x : real) (x0 : real) (y0 : real) : (term175 x x0 y0) = (term191 x x0 y0).
Proof. exact (MK_COMB (@lem1548529 x) (@lem1548528 x0 y0)). Qed.
Lemma lem1548531 (x : real) (x0 : real) (y0 : real) : (term174 x x0 y0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1548502 x x0 y0) (@lem1548530 x x0 y0)). Qed.
Lemma lem1548532 (x : real) (x0 : real) (y0 : real) : (term149 y0 x x0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1548501 x x0 y0) (@lem1548531 x x0 y0)). Qed.
Lemma lem1548533 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548534 (x : real) (x0 : real) (y0 : real) : (term192 y0 x x0) = (term193 x x0 y0).
Proof. exact (MK_COMB (@lem1548533) (@lem1548532 x x0 y0)). Qed.
Lemma lem1548535 (x : real) (x0 : real) (y0 : real) : (term194 y0 x x0) = (term195 x x0 y0).
Proof. exact (MK_COMB (@lem1548534 x x0 y0) (@lem1548442)). Qed.
Lemma lem1548536 (x : real) (x0 : real) (y0 : real) : (term195 x x0 y0) = (term196 x x0 y0).
Proof. exact (@lem1483519 (term191 x x0 y0) term47). Qed.
Lemma lem1548538 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548539 : term138 = term47.
Proof. exact (@lem1548538 term66). Qed.
Lemma lem1548540 (x : real) (x0 : real) (y0 : real) : (term197 x x0 y0) = (term197 x x0 y0).
Proof. exact (eq_refl (term197 x x0 y0)). Qed.
Lemma lem1548541 (x : real) (x0 : real) (y0 : real) : (term196 x x0 y0) = (term198 x x0 y0).
Proof. exact (MK_COMB (@lem1548540 x x0 y0) (@lem1548539)). Qed.
Lemma lem1548542 (x : real) (x0 : real) (y0 : real) : (term198 x x0 y0) = (term191 x x0 y0).
Proof. exact (@lem1483450 (term191 x x0 y0)). Qed.
Lemma lem1548543 (x : real) (x0 : real) (y0 : real) : (term196 x x0 y0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1548541 x x0 y0) (@lem1548542 x x0 y0)). Qed.
Lemma lem1548544 (x : real) (x0 : real) (y0 : real) : (term195 x x0 y0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1548536 x x0 y0) (@lem1548543 x x0 y0)). Qed.
Lemma lem1548545 (x : real) (x0 : real) (y0 : real) : (term194 y0 x x0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1548535 x x0 y0) (@lem1548544 x x0 y0)). Qed.
Lemma lem1548546 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548547 (x : real) (x0 : real) (y0 : real) : (term199 y0 x x0) = (term200 x x0 y0).
Proof. exact (MK_COMB (@lem1548546) (@lem1548545 x x0 y0)). Qed.
Lemma lem1548548 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548549 (x : real) (x0 : real) (y0 : real) : (term148 y0 x x0) = (term201 x x0 y0).
Proof. exact (MK_COMB (@lem1548547 x x0 y0) (@lem1548548)). Qed.
Lemma lem1548550 (x : real) (x0 : real) (y0 : real) : (term147 y0 x x0) = (term201 x x0 y0).
Proof. exact (TRANS (@lem1548441 y0 x x0) (@lem1548549 x x0 y0)). Qed.
Lemma lem1548551 (x0 : real) (y : real) (y0 : real) : (term91 x0 y y0) = (term202 x0 y y0).
Proof. exact (@lem1483525 (term88 x0 y y0) term47). Qed.
Lemma lem1548581 (x0 : real) (y : real) (y0 : real) : (term203 x0 y y0) = (term204 x0 y y0).
Proof. exact (@lem1483519 (term88 x0 y y0) term47). Qed.
Lemma lem1548583 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548584 : term138 = term47.
Proof. exact (@lem1548583 term66). Qed.
Lemma lem1548585 (x0 : real) (y : real) (y0 : real) : (term205 x0 y y0) = (term205 x0 y y0).
Proof. exact (eq_refl (term205 x0 y y0)). Qed.
Lemma lem1548586 (x0 : real) (y : real) (y0 : real) : (term204 x0 y y0) = (term206 x0 y y0).
Proof. exact (MK_COMB (@lem1548585 x0 y y0) (@lem1548584)). Qed.
Lemma lem1548587 (x0 : real) (y : real) (y0 : real) : (term206 x0 y y0) = (term88 x0 y y0).
Proof. exact (@lem1483450 (term88 x0 y y0)). Qed.
Lemma lem1548588 (x0 : real) (y : real) (y0 : real) : (term204 x0 y y0) = (term88 x0 y y0).
Proof. exact (TRANS (@lem1548586 x0 y y0) (@lem1548587 x0 y y0)). Qed.
Lemma lem1548590 (x0 : real) (y : real) (y0 : real) : (term203 x0 y y0) = (term88 x0 y y0).
Proof. exact (TRANS (@lem1548581 x0 y y0) (@lem1548588 x0 y y0)). Qed.
Lemma lem1548591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548592 (x0 : real) (y : real) (y0 : real) : (term207 x0 y y0) = (term90 x0 y y0).
Proof. exact (MK_COMB (@lem1548591) (@lem1548590 x0 y y0)). Qed.
Lemma lem1548593 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548594 (x0 : real) (y : real) (y0 : real) : (term202 x0 y y0) = (term91 x0 y y0).
Proof. exact (MK_COMB (@lem1548592 x0 y y0) (@lem1548593)). Qed.
Lemma lem1548595 (x0 : real) (y : real) (y0 : real) : (term91 x0 y y0) = (term91 x0 y y0).
Proof. exact (TRANS (@lem1548551 x0 y y0) (@lem1548594 x0 y y0)). Qed.
Lemma lem1548596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548597 (x : real) (x0 : real) (y0 : real) : (term208 y0 x x0) = (term209 x x0 y0).
Proof. exact (MK_COMB (@lem1548596) (@lem1548550 x x0 y0)). Qed.
Lemma lem1548598 (x : real) (x0 : real) (y : real) (y0 : real) : (term210 x x0 y y0) = (term211 x x0 y y0).
Proof. exact (MK_COMB (@lem1548597 x x0 y0) (@lem1548595 x0 y y0)). Qed.
Lemma lem1548599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548600 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1548599) (@lem1548440 x0 y0)). Qed.
Lemma lem1548601 (x : real) (x0 : real) (y : real) (y0 : real) : (term212 x x0 y y0) = (term213 x x0 y y0).
Proof. exact (MK_COMB (@lem1548600 x0 y0) (@lem1548598 x x0 y y0)). Qed.
Lemma lem1548602 (x : real) (y : real) : (term103 x y) = (term214 x y).
Proof. exact (@lem1483527 (term42 x y) term47). Qed.
Lemma lem1548620 (x : real) (y : real) : (term135 x y) = (term136 x y).
Proof. exact (@lem1483519 (term42 x y) term47). Qed.
Lemma lem1548622 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548623 : term138 = term47.
Proof. exact (@lem1548622 term66). Qed.
Lemma lem1548624 (x : real) (y : real) : (term139 x y) = (term139 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1548625 (x : real) (y : real) : (term136 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem1548624 x y) (@lem1548623)). Qed.
Lemma lem1548626 (x : real) (y : real) : (term140 x y) = (term42 x y).
Proof. exact (@lem1483450 (term42 x y)). Qed.
Lemma lem1548627 (x : real) (y : real) : (term136 x y) = (term42 x y).
Proof. exact (TRANS (@lem1548625 x y) (@lem1548626 x y)). Qed.
Lemma lem1548629 (x : real) (y : real) : (term135 x y) = (term42 x y).
Proof. exact (TRANS (@lem1548620 x y) (@lem1548627 x y)). Qed.
Lemma lem1548630 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1548631 (x : real) (y : real) : (term215 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1548630) (@lem1548629 x y)). Qed.
Lemma lem1548632 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548633 (x : real) (y : real) : (term214 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1548631 x y) (@lem1548632)). Qed.
Lemma lem1548634 (x : real) (y : real) : (term103 x y) = (term103 x y).
Proof. exact (TRANS (@lem1548602 x y) (@lem1548633 x y)). Qed.
Lemma lem1548635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548636 (x : real) (x0 : real) (y : real) (y0 : real) : (term216 x x0 y y0) = (term217 x x0 y y0).
Proof. exact (MK_COMB (@lem1548635) (@lem1548601 x x0 y y0)). Qed.
Lemma lem1548637 (x0 : real) (y0 : real) (x : real) (y : real) : (term124 x0 y0 x y) = (term218 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548636 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1548638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548639 (x : real) (x0 : real) : (term125 x x0) = (term219 x x0).
Proof. exact (MK_COMB (@lem1548638) (@lem1548407 x x0)). Qed.
Lemma lem1548640 (x0 : real) (y0 : real) (x : real) (y : real) : (term127 x0 y0 x y) = (term220 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548639 x x0) (@lem1548637 x0 y0 x y)). Qed.
Lemma lem1548641 (x : real) (x0 : real) : (term221 x x0) = (term222 x x0).
Proof. exact (@lem1483525 term47 (real_sub x x0)). Qed.
Lemma lem1548654 (x : real) (x0 : real) : (real_sub x x0) = (term42 x x0).
Proof. exact (@lem1483519 x x0). Qed.
Lemma lem1548657 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem1548658 (x : real) (x0 : real) : (term224 x x0) = (term225 x x0).
Proof. exact (MK_COMB (@lem1548657) (@lem1548654 x x0)). Qed.
Lemma lem1548659 (x : real) (x0 : real) : (term225 x x0) = (term226 x x0).
Proof. exact (@lem1483519 term47 (term42 x x0)). Qed.
Lemma lem1548660 (x : real) (x0 : real) : (term227 x x0) = (term228 x x0).
Proof. exact (@lem1483508 x term59 (term44 x0)). Qed.
Lemma lem1548661 (x0 : real) : (term229 x0) = (term230 x0).
Proof. exact (@lem1483476 term59 term59 x0). Qed.
Lemma lem1548663 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1548664 : term231 = term232.
Proof. exact (@lem1548663 term66 term66). Qed.
Lemma lem1548665 : (term233 = (BIT1 0)) = (term234 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1548666 : term234 = term66.
Proof. exact (EQ_MP (@lem1548665) (@lem940073)). Qed.
Lemma lem1548667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548668 : term232 = term181.
Proof. exact (MK_COMB (@lem1548667) (@lem1548666)). Qed.
Lemma lem1548669 : term231 = term181.
Proof. exact (TRANS (@lem1548664) (@lem1548668)). Qed.
Lemma lem1548670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548671 : term235 = term188.
Proof. exact (MK_COMB (@lem1548670) (@lem1548669)). Qed.
Lemma lem1548672 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1548673 (x0 : real) : (term230 x0) = (term189 x0).
Proof. exact (MK_COMB (@lem1548671) (@lem1548672 x0)). Qed.
Lemma lem1548674 (x0 : real) : (term229 x0) = (term189 x0).
Proof. exact (TRANS (@lem1548661 x0) (@lem1548673 x0)). Qed.
Lemma lem1548675 (x0 : real) : (term189 x0) = x0.
Proof. exact (@lem1483436 x0). Qed.
Lemma lem1548676 (x0 : real) : (term229 x0) = x0.
Proof. exact (TRANS (@lem1548674 x0) (@lem1548675 x0)). Qed.
Lemma lem1548679 (x : real) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem1548680 (x : real) (x0 : real) : (term228 x x0) = (term43 x x0).
Proof. exact (MK_COMB (@lem1548679 x) (@lem1548676 x0)). Qed.
Lemma lem1548681 (x : real) (x0 : real) : (term227 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548660 x x0) (@lem1548680 x x0)). Qed.
Lemma lem1548682 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem1548683 (x : real) (x0 : real) : (term226 x x0) = (term237 x x0).
Proof. exact (MK_COMB (@lem1548682) (@lem1548681 x x0)). Qed.
Lemma lem1548684 (x : real) (x0 : real) : (term237 x x0) = (term43 x x0).
Proof. exact (@lem1483448 (term43 x x0)). Qed.
Lemma lem1548685 (x : real) (x0 : real) : (term226 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548683 x x0) (@lem1548684 x x0)). Qed.
Lemma lem1548686 (x : real) (x0 : real) : (term225 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548659 x x0) (@lem1548685 x x0)). Qed.
Lemma lem1548687 (x : real) (x0 : real) : (term224 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548658 x x0) (@lem1548686 x x0)). Qed.
Lemma lem1548688 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548689 (x : real) (x0 : real) : (term238 x x0) = (term46 x x0).
Proof. exact (MK_COMB (@lem1548688) (@lem1548687 x x0)). Qed.
Lemma lem1548690 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548691 (x : real) (x0 : real) : (term222 x x0) = (term48 x x0).
Proof. exact (MK_COMB (@lem1548689 x x0) (@lem1548690)). Qed.
Lemma lem1548692 (x : real) (x0 : real) : (term221 x x0) = (term48 x x0).
Proof. exact (TRANS (@lem1548641 x x0) (@lem1548691 x x0)). Qed.
Lemma lem1548693 (y0 : real) (x : real) (x0 : real) : (term239 y0 x x0) = (term240 y0 x x0).
Proof. exact (@lem1483525 (term241 y0 x x0) term47). Qed.
Lemma lem1548694 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548707 (x : real) (x0 : real) : (real_sub x x0) = (term42 x x0).
Proof. exact (@lem1483519 x x0). Qed.
Lemma lem1548708 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1548709 (x : real) (x0 : real) : (term242 x x0) = (term243 x x0).
Proof. exact (MK_COMB (@lem1548708) (@lem1548707 x x0)). Qed.
Lemma lem1548710 (x : real) (x0 : real) : (term243 x x0) = (term227 x x0).
Proof. exact (@lem1483512 (term42 x x0)). Qed.
Lemma lem1548711 (x : real) (x0 : real) : (term227 x x0) = (term228 x x0).
Proof. exact (@lem1483508 x term59 (term44 x0)). Qed.
Lemma lem1548712 (x0 : real) : (term229 x0) = (term230 x0).
Proof. exact (@lem1483476 term59 term59 x0). Qed.
Lemma lem1548714 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1548715 : term231 = term232.
Proof. exact (@lem1548714 term66 term66). Qed.
Lemma lem1548716 : (term233 = (BIT1 0)) = (term234 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1548717 : term234 = term66.
Proof. exact (EQ_MP (@lem1548716) (@lem940073)). Qed.
Lemma lem1548718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548719 : term232 = term181.
Proof. exact (MK_COMB (@lem1548718) (@lem1548717)). Qed.
Lemma lem1548720 : term231 = term181.
Proof. exact (TRANS (@lem1548715) (@lem1548719)). Qed.
Lemma lem1548721 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548722 : term235 = term188.
Proof. exact (MK_COMB (@lem1548721) (@lem1548720)). Qed.
Lemma lem1548723 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1548724 (x0 : real) : (term230 x0) = (term189 x0).
Proof. exact (MK_COMB (@lem1548722) (@lem1548723 x0)). Qed.
Lemma lem1548725 (x0 : real) : (term229 x0) = (term189 x0).
Proof. exact (TRANS (@lem1548712 x0) (@lem1548724 x0)). Qed.
Lemma lem1548726 (x0 : real) : (term189 x0) = x0.
Proof. exact (@lem1483436 x0). Qed.
Lemma lem1548727 (x0 : real) : (term229 x0) = x0.
Proof. exact (TRANS (@lem1548725 x0) (@lem1548726 x0)). Qed.
Lemma lem1548730 (x : real) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem1548731 (x : real) (x0 : real) : (term228 x x0) = (term43 x x0).
Proof. exact (MK_COMB (@lem1548730 x) (@lem1548727 x0)). Qed.
Lemma lem1548732 (x : real) (x0 : real) : (term227 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548711 x x0) (@lem1548731 x x0)). Qed.
Lemma lem1548733 (x : real) (x0 : real) : (term243 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548710 x x0) (@lem1548732 x x0)). Qed.
Lemma lem1548734 (x : real) (x0 : real) : (term242 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548709 x x0) (@lem1548733 x x0)). Qed.
Lemma lem1548737 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1548738 (x : real) (x0 : real) : (term244 x x0) = (term245 x x0).
Proof. exact (MK_COMB (@lem1548737) (@lem1548734 x x0)). Qed.
Lemma lem1548739 (x : real) (x0 : real) : (term245 x x0) = (term246 x x0).
Proof. exact (@lem1483508 (term44 x) term72 x0). Qed.
Lemma lem1548740 (x0 : real) : (term169 x0) = (term169 x0).
Proof. exact (eq_refl (term169 x0)). Qed.
Lemma lem1548741 (x : real) : (term153 x) = (term154 x).
Proof. exact (@lem1483476 term72 term59 x). Qed.
Lemma lem1548743 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1548744 : term157 = term158.
Proof. exact (@lem1548743 term67 term66). Qed.
Lemma lem1548745 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1548746 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1548747 : term160 = term67.
Proof. exact (EQ_MP (@lem1548746) (@lem1548745)). Qed.
Lemma lem1548748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548749 : term158 = term60.
Proof. exact (MK_COMB (@lem1548748) (@lem1548747)). Qed.
Lemma lem1548750 : term157 = term60.
Proof. exact (TRANS (@lem1548744) (@lem1548749)). Qed.
Lemma lem1548751 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548752 : term161 = term162.
Proof. exact (MK_COMB (@lem1548751) (@lem1548750)). Qed.
Lemma lem1548753 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1548754 (x : real) : (term154 x) = (term163 x).
Proof. exact (MK_COMB (@lem1548752) (@lem1548753 x)). Qed.
Lemma lem1548755 (x : real) : (term153 x) = (term163 x).
Proof. exact (TRANS (@lem1548741 x) (@lem1548754 x)). Qed.
Lemma lem1548756 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1548757 (x : real) : (term247 x) = (term248 x).
Proof. exact (MK_COMB (@lem1548756) (@lem1548755 x)). Qed.
Lemma lem1548758 (x : real) (x0 : real) : (term246 x x0) = (term249 x x0).
Proof. exact (MK_COMB (@lem1548757 x) (@lem1548740 x0)). Qed.
Lemma lem1548759 (x : real) (x0 : real) : (term245 x x0) = (term249 x x0).
Proof. exact (TRANS (@lem1548739 x x0) (@lem1548758 x x0)). Qed.
Lemma lem1548760 (x : real) (x0 : real) : (term244 x x0) = (term249 x x0).
Proof. exact (TRANS (@lem1548738 x x0) (@lem1548759 x x0)). Qed.
Lemma lem1548763 (y0 : real) : (real_add y0) = (real_add y0).
Proof. exact (eq_refl (real_add y0)). Qed.
Lemma lem1548764 (y0 : real) (x : real) (x0 : real) : (term250 y0 x x0) = (term251 y0 x x0).
Proof. exact (MK_COMB (@lem1548763 y0) (@lem1548760 x x0)). Qed.
Lemma lem1548765 (x : real) (y0 : real) (x0 : real) : (term251 y0 x x0) = (term252 x y0 x0).
Proof. exact (@lem1483484 (term163 x) y0 (term169 x0)). Qed.
Lemma lem1548766 (x0 : real) (y0 : real) : (term253 y0 x0) = (term254 x0 y0).
Proof. exact (@lem1483488 (term169 x0) y0). Qed.
Lemma lem1548767 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1548768 (x : real) (x0 : real) (y0 : real) : (term252 x y0 x0) = (term255 x x0 y0).
Proof. exact (MK_COMB (@lem1548767 x) (@lem1548766 x0 y0)). Qed.
Lemma lem1548769 (x : real) (x0 : real) (y0 : real) : (term251 y0 x x0) = (term255 x x0 y0).
Proof. exact (TRANS (@lem1548765 x y0 x0) (@lem1548768 x x0 y0)). Qed.
Lemma lem1548770 (x : real) (x0 : real) (y0 : real) : (term250 y0 x x0) = (term255 x x0 y0).
Proof. exact (TRANS (@lem1548764 y0 x x0) (@lem1548769 x x0 y0)). Qed.
Lemma lem1548779 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1548780 (x : real) (x0 : real) (y0 : real) : (term241 y0 x x0) = (term256 x x0 y0).
Proof. exact (MK_COMB (@lem1548779 x0) (@lem1548770 x x0 y0)). Qed.
Lemma lem1548781 (x : real) (x0 : real) (y0 : real) : (term256 x x0 y0) = (term257 x x0 y0).
Proof. exact (@lem1483484 (term163 x) (term44 x0) (term254 x0 y0)). Qed.
Lemma lem1548782 (x0 : real) (y0 : real) : (term258 x0 y0) = (term259 x0 y0).
Proof. exact (@lem1483490 (term44 x0) (term169 x0) y0). Qed.
Lemma lem1548783 (x0 : real) : (term260 x0) = (term261 x0).
Proof. exact (@lem1483438 term59 term72 x0). Qed.
Lemma lem1548784 : term262 = term263.
Proof. exact (@lem1367763 term66 term67). Qed.
Lemma lem1548785 : term264 = term265.
Proof. exact (@lem706887). Qed.
Lemma lem1548786 : (term264 = term265) = (term266 = term267).
Proof. exact (@lem1006570 (BIT1 0) term69 term265). Qed.
Lemma lem1548787 : term266 = term267.
Proof. exact (EQ_MP (@lem1548786) (@lem1548785)). Qed.
Lemma lem1548788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548789 : term268 = term269.
Proof. exact (MK_COMB (@lem1548788) (@lem1548787)). Qed.
Lemma lem1548790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1548791 : term263 = term270.
Proof. exact (MK_COMB (@lem1548790) (@lem1548789)). Qed.
Lemma lem1548792 : term262 = term270.
Proof. exact (TRANS (@lem1548784) (@lem1548791)). Qed.
Lemma lem1548793 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1548794 : term271 = term272.
Proof. exact (MK_COMB (@lem1548793) (@lem1548792)). Qed.
Lemma lem1548795 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1548796 (x0 : real) : (term261 x0) = (term273 x0).
Proof. exact (MK_COMB (@lem1548794) (@lem1548795 x0)). Qed.
Lemma lem1548797 (x0 : real) : (term260 x0) = (term273 x0).
Proof. exact (TRANS (@lem1548783 x0) (@lem1548796 x0)). Qed.
Lemma lem1548798 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1548799 (x0 : real) : (term274 x0) = (term275 x0).
Proof. exact (MK_COMB (@lem1548798) (@lem1548797 x0)). Qed.
Lemma lem1548800 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1548801 (x0 : real) (y0 : real) : (term259 x0 y0) = (term276 x0 y0).
Proof. exact (MK_COMB (@lem1548799 x0) (@lem1548800 y0)). Qed.
Lemma lem1548802 (x0 : real) (y0 : real) : (term258 x0 y0) = (term276 x0 y0).
Proof. exact (TRANS (@lem1548782 x0 y0) (@lem1548801 x0 y0)). Qed.
Lemma lem1548803 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1548804 (x : real) (x0 : real) (y0 : real) : (term257 x x0 y0) = (term277 x x0 y0).
Proof. exact (MK_COMB (@lem1548803 x) (@lem1548802 x0 y0)). Qed.
Lemma lem1548805 (x : real) (x0 : real) (y0 : real) : (term256 x x0 y0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548781 x x0 y0) (@lem1548804 x x0 y0)). Qed.
Lemma lem1548806 (x : real) (x0 : real) (y0 : real) : (term241 y0 x x0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548780 x x0 y0) (@lem1548805 x x0 y0)). Qed.
Lemma lem1548807 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548808 (x : real) (x0 : real) (y0 : real) : (term278 y0 x x0) = (term279 x x0 y0).
Proof. exact (MK_COMB (@lem1548807) (@lem1548806 x x0 y0)). Qed.
Lemma lem1548809 (x : real) (x0 : real) (y0 : real) : (term280 y0 x x0) = (term281 x x0 y0).
Proof. exact (MK_COMB (@lem1548808 x x0 y0) (@lem1548694)). Qed.
Lemma lem1548810 (x : real) (x0 : real) (y0 : real) : (term281 x x0 y0) = (term282 x x0 y0).
Proof. exact (@lem1483519 (term277 x x0 y0) term47). Qed.
Lemma lem1548812 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548813 : term138 = term47.
Proof. exact (@lem1548812 term66). Qed.
Lemma lem1548814 (x : real) (x0 : real) (y0 : real) : (term283 x x0 y0) = (term283 x x0 y0).
Proof. exact (eq_refl (term283 x x0 y0)). Qed.
Lemma lem1548815 (x : real) (x0 : real) (y0 : real) : (term282 x x0 y0) = (term284 x x0 y0).
Proof. exact (MK_COMB (@lem1548814 x x0 y0) (@lem1548813)). Qed.
Lemma lem1548816 (x : real) (x0 : real) (y0 : real) : (term284 x x0 y0) = (term277 x x0 y0).
Proof. exact (@lem1483450 (term277 x x0 y0)). Qed.
Lemma lem1548817 (x : real) (x0 : real) (y0 : real) : (term282 x x0 y0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548815 x x0 y0) (@lem1548816 x x0 y0)). Qed.
Lemma lem1548818 (x : real) (x0 : real) (y0 : real) : (term281 x x0 y0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548810 x x0 y0) (@lem1548817 x x0 y0)). Qed.
Lemma lem1548819 (x : real) (x0 : real) (y0 : real) : (term280 y0 x x0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548809 x x0 y0) (@lem1548818 x x0 y0)). Qed.
Lemma lem1548820 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548821 (x : real) (x0 : real) (y0 : real) : (term285 y0 x x0) = (term286 x x0 y0).
Proof. exact (MK_COMB (@lem1548820) (@lem1548819 x x0 y0)). Qed.
Lemma lem1548822 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548823 (x : real) (x0 : real) (y0 : real) : (term240 y0 x x0) = (term287 x x0 y0).
Proof. exact (MK_COMB (@lem1548821 x x0 y0) (@lem1548822)). Qed.
Lemma lem1548824 (x : real) (x0 : real) (y0 : real) : (term239 y0 x x0) = (term287 x x0 y0).
Proof. exact (TRANS (@lem1548693 y0 x x0) (@lem1548823 x x0 y0)). Qed.
Lemma lem1548825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548826 (x : real) (x0 : real) (y0 : real) : (term288 y0 x x0) = (term289 x x0 y0).
Proof. exact (MK_COMB (@lem1548825) (@lem1548824 x x0 y0)). Qed.
Lemma lem1548827 (x : real) (x0 : real) (y : real) (y0 : real) : (term290 x x0 y y0) = (term291 x x0 y y0).
Proof. exact (MK_COMB (@lem1548826 x x0 y0) (@lem1548595 x0 y y0)). Qed.
Lemma lem1548828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548829 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1548828) (@lem1548440 x0 y0)). Qed.
Lemma lem1548830 (x : real) (x0 : real) (y : real) (y0 : real) : (term292 x x0 y y0) = (term293 x x0 y y0).
Proof. exact (MK_COMB (@lem1548829 x0 y0) (@lem1548827 x x0 y y0)). Qed.
Lemma lem1548831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548832 (x : real) (x0 : real) (y : real) (y0 : real) : (term294 x x0 y y0) = (term295 x x0 y y0).
Proof. exact (MK_COMB (@lem1548831) (@lem1548830 x x0 y y0)). Qed.
Lemma lem1548833 (x0 : real) (y0 : real) (x : real) (y : real) : (term119 x0 y0 x y) = (term296 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548832 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1548834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1548835 (x : real) (x0 : real) : (term120 x x0) = (term97 x x0).
Proof. exact (MK_COMB (@lem1548834) (@lem1548692 x x0)). Qed.
Lemma lem1548836 (x0 : real) (y0 : real) (x : real) (y : real) : (term122 x0 y0 x y) = (term297 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548835 x x0) (@lem1548833 x0 y0 x y)). Qed.
Lemma lem1548837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1548838 (x0 : real) (y0 : real) (x : real) (y : real) : (term129 x0 y0 x y) = (term298 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548837) (@lem1548640 x0 y0 x y)). Qed.
Lemma lem1548839 (x0 : real) (y0 : real) (x : real) (y : real) : (term130 x0 y0 x y) = (term299 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548838 x0 y0 x y) (@lem1548836 x0 y0 x y)). Qed.
Lemma lem1548840 (x0 : real) (y0 : real) (x : real) (y : real) : (term106 x0 y0 x y) = (term299 x0 y0 x y).
Proof. exact (TRANS (@lem1548374 x0 y0 x y) (@lem1548839 x0 y0 x y)). Qed.
Lemma lem1548842 (x0 : real) (y0 : real) (x : real) (y : real) : (term300 x0 x y y0) = (term297 x0 y0 x y).
Proof. exact (eq_refl (term300 x0 x y y0)). Qed.
Lemma lem1548843 (x0 : real) (x : real) (y : real) (y0 : real) : (term297 x0 y0 x y) = (term300 x0 x y y0).
Proof. exact (SYM (@lem1548842 x0 y0 x y)). Qed.
Lemma lem1548844 (x0 : real) (x : real) (y : real) (y0 : real) : (term300 x0 x y y0) = (term301 x0 x y y0).
Proof. exact (@lem1482981 (term302 x0 y0 x y) (real_sub y y0)). Qed.
Lemma lem1548845 (x0 : real) (x : real) (y : real) (y0 : real) : (term297 x0 y0 x y) = (term301 x0 x y y0).
Proof. exact (TRANS (@lem1548843 x0 x y y0) (@lem1548844 x0 x y y0)). Qed.
Lemma lem1548846 (x0 : real) (y0 : real) (x : real) (y : real) : (term303 x0 x y y0) = (term304 x0 y0 x y).
Proof. exact (eq_refl (term303 x0 x y y0)). Qed.
Lemma lem1548847 (y : real) (y0 : real) : (term120 y y0) = (term120 y y0).
Proof. exact (eq_refl (term120 y y0)). Qed.
Lemma lem1548848 (x0 : real) (y0 : real) (x : real) (y : real) : (term305 x0 x y y0) = (term306 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548847 y y0) (@lem1548846 x0 y0 x y)). Qed.
Lemma lem1548849 (x0 : real) (y0 : real) (x : real) (y : real) : (term307 x0 x y y0) = (term308 x0 y0 x y).
Proof. exact (eq_refl (term307 x0 x y y0)). Qed.
Lemma lem1548850 (y : real) (y0 : real) : (term125 y y0) = (term125 y y0).
Proof. exact (eq_refl (term125 y y0)). Qed.
Lemma lem1548851 (x0 : real) (y0 : real) (x : real) (y : real) : (term309 x0 x y y0) = (term310 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548850 y y0) (@lem1548849 x0 y0 x y)). Qed.
Lemma lem1548852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1548853 (x0 : real) (y0 : real) (x : real) (y : real) : (term311 x0 x y y0) = (term312 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548852) (@lem1548851 x0 y0 x y)). Qed.
Lemma lem1548854 (x0 : real) (y0 : real) (x : real) (y : real) : (term301 x0 x y y0) = (term313 x0 y0 x y).
Proof. exact (MK_COMB (@lem1548853 x0 y0 x y) (@lem1548848 x0 y0 x y)). Qed.
Lemma lem1548855 (x0 : real) (y0 : real) (x : real) (y : real) : (term314 x0 y0 x y) = (term314 x0 y0 x y).
Proof. exact (eq_refl (term314 x0 y0 x y)). Qed.
Lemma lem1548856 (x0 : real) (y0 : real) (x : real) (y : real) : ((term297 x0 y0 x y) = (term301 x0 x y y0)) = ((term297 x0 y0 x y) = (term313 x0 y0 x y)).
Proof. exact (MK_COMB (@lem1548855 x0 y0 x y) (@lem1548854 x0 y0 x y)). Qed.
Lemma lem1548857 (x0 : real) (y0 : real) (x : real) (y : real) : (term297 x0 y0 x y) = (term313 x0 y0 x y).
Proof. exact (EQ_MP (@lem1548856 x0 y0 x y) (@lem1548845 x0 x y y0)). Qed.
Lemma lem1548858 (y : real) (y0 : real) : (term100 y y0) = (term132 y y0).
Proof. exact (@lem1483527 (real_sub y y0) term47). Qed.
Lemma lem1548859 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548872 (y : real) (y0 : real) : (real_sub y y0) = (term42 y y0).
Proof. exact (@lem1483519 y y0). Qed.
Lemma lem1548873 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1548874 (y : real) (y0 : real) : (term52 y y0) = (term133 y y0).
Proof. exact (MK_COMB (@lem1548873) (@lem1548872 y y0)). Qed.
Lemma lem1548875 (y : real) (y0 : real) : (term134 y y0) = (term135 y y0).
Proof. exact (MK_COMB (@lem1548874 y y0) (@lem1548859)). Qed.
Lemma lem1548876 (y : real) (y0 : real) : (term135 y y0) = (term136 y y0).
Proof. exact (@lem1483519 (term42 y y0) term47). Qed.
Lemma lem1548878 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548879 : term138 = term47.
Proof. exact (@lem1548878 term66). Qed.
Lemma lem1548880 (y : real) (y0 : real) : (term139 y y0) = (term139 y y0).
Proof. exact (eq_refl (term139 y y0)). Qed.
Lemma lem1548881 (y : real) (y0 : real) : (term136 y y0) = (term140 y y0).
Proof. exact (MK_COMB (@lem1548880 y y0) (@lem1548879)). Qed.
Lemma lem1548882 (y : real) (y0 : real) : (term140 y y0) = (term42 y y0).
Proof. exact (@lem1483450 (term42 y y0)). Qed.
Lemma lem1548883 (y : real) (y0 : real) : (term136 y y0) = (term42 y y0).
Proof. exact (TRANS (@lem1548881 y y0) (@lem1548882 y y0)). Qed.
Lemma lem1548884 (y : real) (y0 : real) : (term135 y y0) = (term42 y y0).
Proof. exact (TRANS (@lem1548876 y y0) (@lem1548883 y y0)). Qed.
Lemma lem1548885 (y : real) (y0 : real) : (term134 y y0) = (term42 y y0).
Proof. exact (TRANS (@lem1548875 y y0) (@lem1548884 y y0)). Qed.
Lemma lem1548886 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1548887 (y : real) (y0 : real) : (term141 y y0) = (term102 y y0).
Proof. exact (MK_COMB (@lem1548886) (@lem1548885 y y0)). Qed.
Lemma lem1548888 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548889 (y : real) (y0 : real) : (term132 y y0) = (term103 y y0).
Proof. exact (MK_COMB (@lem1548887 y y0) (@lem1548888)). Qed.
Lemma lem1548890 (y : real) (y0 : real) : (term100 y y0) = (term103 y y0).
Proof. exact (TRANS (@lem1548858 y y0) (@lem1548889 y y0)). Qed.
Lemma lem1548891 (x : real) (x0 : real) : (term48 x x0) = (term142 x x0).
Proof. exact (@lem1483525 (term43 x x0) term47). Qed.
Lemma lem1548909 (x : real) (x0 : real) : (term143 x x0) = (term144 x x0).
Proof. exact (@lem1483519 (term43 x x0) term47). Qed.
Lemma lem1548911 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548912 : term138 = term47.
Proof. exact (@lem1548911 term66). Qed.
Lemma lem1548913 (x : real) (x0 : real) : (term76 x x0) = (term76 x x0).
Proof. exact (eq_refl (term76 x x0)). Qed.
Lemma lem1548914 (x : real) (x0 : real) : (term144 x x0) = (term145 x x0).
Proof. exact (MK_COMB (@lem1548913 x x0) (@lem1548912)). Qed.
Lemma lem1548915 (x : real) (x0 : real) : (term145 x x0) = (term43 x x0).
Proof. exact (@lem1483450 (term43 x x0)). Qed.
Lemma lem1548916 (x : real) (x0 : real) : (term144 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548914 x x0) (@lem1548915 x x0)). Qed.
Lemma lem1548918 (x : real) (x0 : real) : (term143 x x0) = (term43 x x0).
Proof. exact (TRANS (@lem1548909 x x0) (@lem1548916 x x0)). Qed.
Lemma lem1548919 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548920 (x : real) (x0 : real) : (term146 x x0) = (term46 x x0).
Proof. exact (MK_COMB (@lem1548919) (@lem1548918 x x0)). Qed.
Lemma lem1548921 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548922 (x : real) (x0 : real) : (term142 x x0) = (term48 x x0).
Proof. exact (MK_COMB (@lem1548920 x x0) (@lem1548921)). Qed.
Lemma lem1548923 (x : real) (x0 : real) : (term48 x x0) = (term48 x x0).
Proof. exact (TRANS (@lem1548891 x x0) (@lem1548922 x x0)). Qed.
Lemma lem1548924 (x : real) (x0 : real) (y0 : real) : (term287 x x0 y0) = (term315 x x0 y0).
Proof. exact (@lem1483525 (term277 x x0 y0) term47). Qed.
Lemma lem1548954 (x : real) (x0 : real) (y0 : real) : (term281 x x0 y0) = (term282 x x0 y0).
Proof. exact (@lem1483519 (term277 x x0 y0) term47). Qed.
Lemma lem1548956 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1548957 : term138 = term47.
Proof. exact (@lem1548956 term66). Qed.
Lemma lem1548958 (x : real) (x0 : real) (y0 : real) : (term283 x x0 y0) = (term283 x x0 y0).
Proof. exact (eq_refl (term283 x x0 y0)). Qed.
Lemma lem1548959 (x : real) (x0 : real) (y0 : real) : (term282 x x0 y0) = (term284 x x0 y0).
Proof. exact (MK_COMB (@lem1548958 x x0 y0) (@lem1548957)). Qed.
Lemma lem1548960 (x : real) (x0 : real) (y0 : real) : (term284 x x0 y0) = (term277 x x0 y0).
Proof. exact (@lem1483450 (term277 x x0 y0)). Qed.
Lemma lem1548961 (x : real) (x0 : real) (y0 : real) : (term282 x x0 y0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548959 x x0 y0) (@lem1548960 x x0 y0)). Qed.
Lemma lem1548963 (x : real) (x0 : real) (y0 : real) : (term281 x x0 y0) = (term277 x x0 y0).
Proof. exact (TRANS (@lem1548954 x x0 y0) (@lem1548961 x x0 y0)). Qed.
Lemma lem1548964 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1548965 (x : real) (x0 : real) (y0 : real) : (term316 x x0 y0) = (term286 x x0 y0).
Proof. exact (MK_COMB (@lem1548964) (@lem1548963 x x0 y0)). Qed.
Lemma lem1548966 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548967 (x : real) (x0 : real) (y0 : real) : (term315 x x0 y0) = (term287 x x0 y0).
Proof. exact (MK_COMB (@lem1548965 x x0 y0) (@lem1548966)). Qed.
Lemma lem1548968 (x : real) (x0 : real) (y0 : real) : (term287 x x0 y0) = (term287 x x0 y0).
Proof. exact (TRANS (@lem1548924 x x0 y0) (@lem1548967 x x0 y0)). Qed.
Lemma lem1548969 (x0 : real) (y : real) (y0 : real) : (term317 x0 y y0) = (term318 x0 y y0).
Proof. exact (@lem1483525 (term319 x0 y y0) term47). Qed.
Lemma lem1548970 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1548983 (y : real) (y0 : real) : (real_sub y y0) = (term42 y y0).
Proof. exact (@lem1483519 y y0). Qed.
Lemma lem1548986 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1548987 (y : real) (y0 : real) : (term150 y y0) = (term151 y y0).
Proof. exact (MK_COMB (@lem1548986) (@lem1548983 y y0)). Qed.
Lemma lem1548988 (y : real) (y0 : real) : (term151 y y0) = (term152 y y0).
Proof. exact (@lem1483508 y term72 (term44 y0)). Qed.
Lemma lem1548989 (y0 : real) : (term153 y0) = (term154 y0).
Proof. exact (@lem1483476 term72 term59 y0). Qed.
Lemma lem1548991 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1548992 : term157 = term158.
Proof. exact (@lem1548991 term67 term66). Qed.
Lemma lem1548993 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1548994 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1548995 : term160 = term67.
Proof. exact (EQ_MP (@lem1548994) (@lem1548993)). Qed.
Lemma lem1548996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1548997 : term158 = term60.
Proof. exact (MK_COMB (@lem1548996) (@lem1548995)). Qed.
Lemma lem1548998 : term157 = term60.
Proof. exact (TRANS (@lem1548992) (@lem1548997)). Qed.
Lemma lem1548999 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549000 : term161 = term162.
Proof. exact (MK_COMB (@lem1548999) (@lem1548998)). Qed.
Lemma lem1549001 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549002 (y0 : real) : (term154 y0) = (term163 y0).
Proof. exact (MK_COMB (@lem1549000) (@lem1549001 y0)). Qed.
Lemma lem1549003 (y0 : real) : (term153 y0) = (term163 y0).
Proof. exact (TRANS (@lem1548989 y0) (@lem1549002 y0)). Qed.
Lemma lem1549006 (y : real) : (term164 y) = (term164 y).
Proof. exact (eq_refl (term164 y)). Qed.
Lemma lem1549007 (y : real) (y0 : real) : (term152 y y0) = (term165 y y0).
Proof. exact (MK_COMB (@lem1549006 y) (@lem1549003 y0)). Qed.
Lemma lem1549008 (y : real) (y0 : real) : (term151 y y0) = (term165 y y0).
Proof. exact (TRANS (@lem1548988 y y0) (@lem1549007 y y0)). Qed.
Lemma lem1549009 (y : real) (y0 : real) : (term150 y y0) = (term165 y y0).
Proof. exact (TRANS (@lem1548987 y y0) (@lem1549008 y y0)). Qed.
Lemma lem1549012 (y0 : real) : (real_add y0) = (real_add y0).
Proof. exact (eq_refl (real_add y0)). Qed.
Lemma lem1549013 (y : real) (y0 : real) : (term320 y y0) = (term321 y y0).
Proof. exact (MK_COMB (@lem1549012 y0) (@lem1549009 y y0)). Qed.
Lemma lem1549014 (y : real) (y0 : real) : (term321 y y0) = (term322 y y0).
Proof. exact (@lem1483484 (term169 y) y0 (term163 y0)). Qed.
Lemma lem1549015 (y0 : real) : (term323 y0) = (term324 y0).
Proof. exact (@lem1483442 term60 y0). Qed.
Lemma lem1549016 : term325 = term326.
Proof. exact (@lem1367770 term67 term66). Qed.
Lemma lem1549017 : term327 = term265.
Proof. exact (@lem706949). Qed.
Lemma lem1549018 : (term327 = term265) = (term328 = term267).
Proof. exact (@lem1006570 term69 (BIT1 0) term265). Qed.
Lemma lem1549019 : term328 = term267.
Proof. exact (EQ_MP (@lem1549018) (@lem1549017)). Qed.
Lemma lem1549020 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549021 : term326 = term269.
Proof. exact (MK_COMB (@lem1549020) (@lem1549019)). Qed.
Lemma lem1549022 : term325 = term269.
Proof. exact (TRANS (@lem1549016) (@lem1549021)). Qed.
Lemma lem1549023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549024 : term329 = term330.
Proof. exact (MK_COMB (@lem1549023) (@lem1549022)). Qed.
Lemma lem1549025 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549026 (y0 : real) : (term324 y0) = (term331 y0).
Proof. exact (MK_COMB (@lem1549024) (@lem1549025 y0)). Qed.
Lemma lem1549027 (y0 : real) : (term323 y0) = (term331 y0).
Proof. exact (TRANS (@lem1549015 y0) (@lem1549026 y0)). Qed.
Lemma lem1549028 (y : real) : (term164 y) = (term164 y).
Proof. exact (eq_refl (term164 y)). Qed.
Lemma lem1549029 (y : real) (y0 : real) : (term322 y y0) = (term332 y y0).
Proof. exact (MK_COMB (@lem1549028 y) (@lem1549027 y0)). Qed.
Lemma lem1549030 (y : real) (y0 : real) : (term321 y y0) = (term332 y y0).
Proof. exact (TRANS (@lem1549014 y y0) (@lem1549029 y y0)). Qed.
Lemma lem1549031 (y : real) (y0 : real) : (term320 y y0) = (term332 y y0).
Proof. exact (TRANS (@lem1549013 y y0) (@lem1549030 y y0)). Qed.
Lemma lem1549040 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1549043 (x0 : real) (y : real) (y0 : real) : (term319 x0 y y0) = (term333 x0 y y0).
Proof. exact (MK_COMB (@lem1549040 x0) (@lem1549031 y y0)). Qed.
Lemma lem1549044 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1549045 (x0 : real) (y : real) (y0 : real) : (term334 x0 y y0) = (term335 x0 y y0).
Proof. exact (MK_COMB (@lem1549044) (@lem1549043 x0 y y0)). Qed.
Lemma lem1549046 (x0 : real) (y : real) (y0 : real) : (term336 x0 y y0) = (term337 x0 y y0).
Proof. exact (MK_COMB (@lem1549045 x0 y y0) (@lem1548970)). Qed.
Lemma lem1549047 (x0 : real) (y : real) (y0 : real) : (term337 x0 y y0) = (term338 x0 y y0).
Proof. exact (@lem1483519 (term333 x0 y y0) term47). Qed.
Lemma lem1549049 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1549050 : term138 = term47.
Proof. exact (@lem1549049 term66). Qed.
Lemma lem1549051 (x0 : real) (y : real) (y0 : real) : (term339 x0 y y0) = (term339 x0 y y0).
Proof. exact (eq_refl (term339 x0 y y0)). Qed.
Lemma lem1549052 (x0 : real) (y : real) (y0 : real) : (term338 x0 y y0) = (term340 x0 y y0).
Proof. exact (MK_COMB (@lem1549051 x0 y y0) (@lem1549050)). Qed.
Lemma lem1549053 (x0 : real) (y : real) (y0 : real) : (term340 x0 y y0) = (term333 x0 y y0).
Proof. exact (@lem1483450 (term333 x0 y y0)). Qed.
Lemma lem1549054 (x0 : real) (y : real) (y0 : real) : (term338 x0 y y0) = (term333 x0 y y0).
Proof. exact (TRANS (@lem1549052 x0 y y0) (@lem1549053 x0 y y0)). Qed.
Lemma lem1549055 (x0 : real) (y : real) (y0 : real) : (term337 x0 y y0) = (term333 x0 y y0).
Proof. exact (TRANS (@lem1549047 x0 y y0) (@lem1549054 x0 y y0)). Qed.
Lemma lem1549056 (x0 : real) (y : real) (y0 : real) : (term336 x0 y y0) = (term333 x0 y y0).
Proof. exact (TRANS (@lem1549046 x0 y y0) (@lem1549055 x0 y y0)). Qed.
Lemma lem1549057 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549058 (x0 : real) (y : real) (y0 : real) : (term341 x0 y y0) = (term342 x0 y y0).
Proof. exact (MK_COMB (@lem1549057) (@lem1549056 x0 y y0)). Qed.
Lemma lem1549059 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549060 (x0 : real) (y : real) (y0 : real) : (term318 x0 y y0) = (term343 x0 y y0).
Proof. exact (MK_COMB (@lem1549058 x0 y y0) (@lem1549059)). Qed.
Lemma lem1549061 (x0 : real) (y : real) (y0 : real) : (term317 x0 y y0) = (term343 x0 y y0).
Proof. exact (TRANS (@lem1548969 x0 y y0) (@lem1549060 x0 y y0)). Qed.
Lemma lem1549062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549063 (x : real) (x0 : real) (y0 : real) : (term289 x x0 y0) = (term289 x x0 y0).
Proof. exact (MK_COMB (@lem1549062) (@lem1548968 x x0 y0)). Qed.
Lemma lem1549064 (x : real) (x0 : real) (y : real) (y0 : real) : (term344 x x0 y y0) = (term345 x x0 y y0).
Proof. exact (MK_COMB (@lem1549063 x x0 y0) (@lem1549061 x0 y y0)). Qed.
Lemma lem1549065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549066 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1549065) (@lem1548440 x0 y0)). Qed.
Lemma lem1549067 (x : real) (x0 : real) (y : real) (y0 : real) : (term346 x x0 y y0) = (term347 x x0 y y0).
Proof. exact (MK_COMB (@lem1549066 x0 y0) (@lem1549064 x x0 y y0)). Qed.
Lemma lem1549068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549069 (x : real) (x0 : real) (y : real) (y0 : real) : (term348 x x0 y y0) = (term349 x x0 y y0).
Proof. exact (MK_COMB (@lem1549068) (@lem1549067 x x0 y y0)). Qed.
Lemma lem1549070 (x0 : real) (y0 : real) (x : real) (y : real) : (term350 x0 y0 x y) = (term351 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549069 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1549071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549072 (x : real) (x0 : real) : (term97 x x0) = (term97 x x0).
Proof. exact (MK_COMB (@lem1549071) (@lem1548923 x x0)). Qed.
Lemma lem1549073 (x0 : real) (y0 : real) (x : real) (y : real) : (term308 x0 y0 x y) = (term352 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549072 x x0) (@lem1549070 x0 y0 x y)). Qed.
Lemma lem1549074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549075 (y : real) (y0 : real) : (term125 y y0) = (term219 y y0).
Proof. exact (MK_COMB (@lem1549074) (@lem1548890 y y0)). Qed.
Lemma lem1549076 (x0 : real) (y0 : real) (x : real) (y : real) : (term310 x0 y0 x y) = (term353 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549075 y y0) (@lem1549073 x0 y0 x y)). Qed.
Lemma lem1549077 (y : real) (y0 : real) : (term221 y y0) = (term222 y y0).
Proof. exact (@lem1483525 term47 (real_sub y y0)). Qed.
Lemma lem1549090 (y : real) (y0 : real) : (real_sub y y0) = (term42 y y0).
Proof. exact (@lem1483519 y y0). Qed.
Lemma lem1549093 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem1549094 (y : real) (y0 : real) : (term224 y y0) = (term225 y y0).
Proof. exact (MK_COMB (@lem1549093) (@lem1549090 y y0)). Qed.
Lemma lem1549095 (y : real) (y0 : real) : (term225 y y0) = (term226 y y0).
Proof. exact (@lem1483519 term47 (term42 y y0)). Qed.
Lemma lem1549096 (y : real) (y0 : real) : (term227 y y0) = (term228 y y0).
Proof. exact (@lem1483508 y term59 (term44 y0)). Qed.
Lemma lem1549097 (y0 : real) : (term229 y0) = (term230 y0).
Proof. exact (@lem1483476 term59 term59 y0). Qed.
Lemma lem1549099 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1549100 : term231 = term232.
Proof. exact (@lem1549099 term66 term66). Qed.
Lemma lem1549101 : (term233 = (BIT1 0)) = (term234 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1549102 : term234 = term66.
Proof. exact (EQ_MP (@lem1549101) (@lem940073)). Qed.
Lemma lem1549103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549104 : term232 = term181.
Proof. exact (MK_COMB (@lem1549103) (@lem1549102)). Qed.
Lemma lem1549105 : term231 = term181.
Proof. exact (TRANS (@lem1549100) (@lem1549104)). Qed.
Lemma lem1549106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549107 : term235 = term188.
Proof. exact (MK_COMB (@lem1549106) (@lem1549105)). Qed.
Lemma lem1549108 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549109 (y0 : real) : (term230 y0) = (term189 y0).
Proof. exact (MK_COMB (@lem1549107) (@lem1549108 y0)). Qed.
Lemma lem1549110 (y0 : real) : (term229 y0) = (term189 y0).
Proof. exact (TRANS (@lem1549097 y0) (@lem1549109 y0)). Qed.
Lemma lem1549111 (y0 : real) : (term189 y0) = y0.
Proof. exact (@lem1483436 y0). Qed.
Lemma lem1549112 (y0 : real) : (term229 y0) = y0.
Proof. exact (TRANS (@lem1549110 y0) (@lem1549111 y0)). Qed.
Lemma lem1549115 (y : real) : (term173 y) = (term173 y).
Proof. exact (eq_refl (term173 y)). Qed.
Lemma lem1549116 (y : real) (y0 : real) : (term228 y y0) = (term43 y y0).
Proof. exact (MK_COMB (@lem1549115 y) (@lem1549112 y0)). Qed.
Lemma lem1549117 (y : real) (y0 : real) : (term227 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549096 y y0) (@lem1549116 y y0)). Qed.
Lemma lem1549118 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem1549119 (y : real) (y0 : real) : (term226 y y0) = (term237 y y0).
Proof. exact (MK_COMB (@lem1549118) (@lem1549117 y y0)). Qed.
Lemma lem1549120 (y : real) (y0 : real) : (term237 y y0) = (term43 y y0).
Proof. exact (@lem1483448 (term43 y y0)). Qed.
Lemma lem1549121 (y : real) (y0 : real) : (term226 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549119 y y0) (@lem1549120 y y0)). Qed.
Lemma lem1549122 (y : real) (y0 : real) : (term225 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549095 y y0) (@lem1549121 y y0)). Qed.
Lemma lem1549123 (y : real) (y0 : real) : (term224 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549094 y y0) (@lem1549122 y y0)). Qed.
Lemma lem1549124 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549125 (y : real) (y0 : real) : (term238 y y0) = (term46 y y0).
Proof. exact (MK_COMB (@lem1549124) (@lem1549123 y y0)). Qed.
Lemma lem1549126 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549127 (y : real) (y0 : real) : (term222 y y0) = (term48 y y0).
Proof. exact (MK_COMB (@lem1549125 y y0) (@lem1549126)). Qed.
Lemma lem1549128 (y : real) (y0 : real) : (term221 y y0) = (term48 y y0).
Proof. exact (TRANS (@lem1549077 y y0) (@lem1549127 y y0)). Qed.
Lemma lem1549129 (x0 : real) (y : real) (y0 : real) : (term354 x0 y y0) = (term355 x0 y y0).
Proof. exact (@lem1483525 (term356 x0 y y0) term47). Qed.
Lemma lem1549130 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549143 (y : real) (y0 : real) : (real_sub y y0) = (term42 y y0).
Proof. exact (@lem1483519 y y0). Qed.
Lemma lem1549144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549145 (y : real) (y0 : real) : (term242 y y0) = (term243 y y0).
Proof. exact (MK_COMB (@lem1549144) (@lem1549143 y y0)). Qed.
Lemma lem1549146 (y : real) (y0 : real) : (term243 y y0) = (term227 y y0).
Proof. exact (@lem1483512 (term42 y y0)). Qed.
Lemma lem1549147 (y : real) (y0 : real) : (term227 y y0) = (term228 y y0).
Proof. exact (@lem1483508 y term59 (term44 y0)). Qed.
Lemma lem1549148 (y0 : real) : (term229 y0) = (term230 y0).
Proof. exact (@lem1483476 term59 term59 y0). Qed.
Lemma lem1549150 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1549151 : term231 = term232.
Proof. exact (@lem1549150 term66 term66). Qed.
Lemma lem1549152 : (term233 = (BIT1 0)) = (term234 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1549153 : term234 = term66.
Proof. exact (EQ_MP (@lem1549152) (@lem940073)). Qed.
Lemma lem1549154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549155 : term232 = term181.
Proof. exact (MK_COMB (@lem1549154) (@lem1549153)). Qed.
Lemma lem1549156 : term231 = term181.
Proof. exact (TRANS (@lem1549151) (@lem1549155)). Qed.
Lemma lem1549157 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549158 : term235 = term188.
Proof. exact (MK_COMB (@lem1549157) (@lem1549156)). Qed.
Lemma lem1549159 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549160 (y0 : real) : (term230 y0) = (term189 y0).
Proof. exact (MK_COMB (@lem1549158) (@lem1549159 y0)). Qed.
Lemma lem1549161 (y0 : real) : (term229 y0) = (term189 y0).
Proof. exact (TRANS (@lem1549148 y0) (@lem1549160 y0)). Qed.
Lemma lem1549162 (y0 : real) : (term189 y0) = y0.
Proof. exact (@lem1483436 y0). Qed.
Lemma lem1549163 (y0 : real) : (term229 y0) = y0.
Proof. exact (TRANS (@lem1549161 y0) (@lem1549162 y0)). Qed.
Lemma lem1549166 (y : real) : (term173 y) = (term173 y).
Proof. exact (eq_refl (term173 y)). Qed.
Lemma lem1549167 (y : real) (y0 : real) : (term228 y y0) = (term43 y y0).
Proof. exact (MK_COMB (@lem1549166 y) (@lem1549163 y0)). Qed.
Lemma lem1549168 (y : real) (y0 : real) : (term227 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549147 y y0) (@lem1549167 y y0)). Qed.
Lemma lem1549169 (y : real) (y0 : real) : (term243 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549146 y y0) (@lem1549168 y y0)). Qed.
Lemma lem1549170 (y : real) (y0 : real) : (term242 y y0) = (term43 y y0).
Proof. exact (TRANS (@lem1549145 y y0) (@lem1549169 y y0)). Qed.
Lemma lem1549173 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1549174 (y : real) (y0 : real) : (term244 y y0) = (term245 y y0).
Proof. exact (MK_COMB (@lem1549173) (@lem1549170 y y0)). Qed.
Lemma lem1549175 (y : real) (y0 : real) : (term245 y y0) = (term246 y y0).
Proof. exact (@lem1483508 (term44 y) term72 y0). Qed.
Lemma lem1549176 (y0 : real) : (term169 y0) = (term169 y0).
Proof. exact (eq_refl (term169 y0)). Qed.
Lemma lem1549177 (y : real) : (term153 y) = (term154 y).
Proof. exact (@lem1483476 term72 term59 y). Qed.
Lemma lem1549179 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1549180 : term157 = term158.
Proof. exact (@lem1549179 term67 term66). Qed.
Lemma lem1549181 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549182 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549183 : term160 = term67.
Proof. exact (EQ_MP (@lem1549182) (@lem1549181)). Qed.
Lemma lem1549184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549185 : term158 = term60.
Proof. exact (MK_COMB (@lem1549184) (@lem1549183)). Qed.
Lemma lem1549186 : term157 = term60.
Proof. exact (TRANS (@lem1549180) (@lem1549185)). Qed.
Lemma lem1549187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549188 : term161 = term162.
Proof. exact (MK_COMB (@lem1549187) (@lem1549186)). Qed.
Lemma lem1549189 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549190 (y : real) : (term154 y) = (term163 y).
Proof. exact (MK_COMB (@lem1549188) (@lem1549189 y)). Qed.
Lemma lem1549191 (y : real) : (term153 y) = (term163 y).
Proof. exact (TRANS (@lem1549177 y) (@lem1549190 y)). Qed.
Lemma lem1549192 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549193 (y : real) : (term247 y) = (term248 y).
Proof. exact (MK_COMB (@lem1549192) (@lem1549191 y)). Qed.
Lemma lem1549194 (y : real) (y0 : real) : (term246 y y0) = (term249 y y0).
Proof. exact (MK_COMB (@lem1549193 y) (@lem1549176 y0)). Qed.
Lemma lem1549195 (y : real) (y0 : real) : (term245 y y0) = (term249 y y0).
Proof. exact (TRANS (@lem1549175 y y0) (@lem1549194 y y0)). Qed.
Lemma lem1549196 (y : real) (y0 : real) : (term244 y y0) = (term249 y y0).
Proof. exact (TRANS (@lem1549174 y y0) (@lem1549195 y y0)). Qed.
Lemma lem1549199 (y0 : real) : (real_add y0) = (real_add y0).
Proof. exact (eq_refl (real_add y0)). Qed.
Lemma lem1549200 (y : real) (y0 : real) : (term357 y y0) = (term358 y y0).
Proof. exact (MK_COMB (@lem1549199 y0) (@lem1549196 y y0)). Qed.
Lemma lem1549201 (y : real) (y0 : real) : (term358 y y0) = (term359 y y0).
Proof. exact (@lem1483484 (term163 y) y0 (term169 y0)). Qed.
Lemma lem1549202 (y0 : real) : (term360 y0) = (term361 y0).
Proof. exact (@lem1483442 term72 y0). Qed.
Lemma lem1549205 : term362 = term59.
Proof. exact (@lem1367767 term66 term66). Qed.
Lemma lem1549206 : term182 = term69.
Proof. exact (@lem706885). Qed.
Lemma lem1549207 : (term182 = term69) = (term183 = term67).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term69). Qed.
Lemma lem1549208 : term183 = term67.
Proof. exact (EQ_MP (@lem1549207) (@lem1549206)). Qed.
Lemma lem1549209 : term67 = term183.
Proof. exact (SYM (@lem1549208)). Qed.
Lemma lem1549210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549211 : term60 = term184.
Proof. exact (MK_COMB (@lem1549210) (@lem1549209)). Qed.
Lemma lem1549212 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549213 : term72 = term363.
Proof. exact (MK_COMB (@lem1549212) (@lem1549211)). Qed.
Lemma lem1549214 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549215 : term364 = term365.
Proof. exact (MK_COMB (@lem1549214) (@lem1549213)). Qed.
Lemma lem1549216 : term181 = term181.
Proof. exact (eq_refl term181). Qed.
Lemma lem1549217 : term366 = term362.
Proof. exact (MK_COMB (@lem1549215) (@lem1549216)). Qed.
Lemma lem1549218 : term366 = term59.
Proof. exact (TRANS (@lem1549217) (@lem1549205)). Qed.
Lemma lem1549219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549220 : term367 = term368.
Proof. exact (MK_COMB (@lem1549219) (@lem1549218)). Qed.
Lemma lem1549221 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549222 (y0 : real) : (term361 y0) = (term44 y0).
Proof. exact (MK_COMB (@lem1549220) (@lem1549221 y0)). Qed.
Lemma lem1549223 (y0 : real) : (term360 y0) = (term44 y0).
Proof. exact (TRANS (@lem1549202 y0) (@lem1549222 y0)). Qed.
Lemma lem1549224 (y : real) : (term248 y) = (term248 y).
Proof. exact (eq_refl (term248 y)). Qed.
Lemma lem1549225 (y : real) (y0 : real) : (term359 y y0) = (term369 y y0).
Proof. exact (MK_COMB (@lem1549224 y) (@lem1549223 y0)). Qed.
Lemma lem1549226 (y : real) (y0 : real) : (term358 y y0) = (term369 y y0).
Proof. exact (TRANS (@lem1549201 y y0) (@lem1549225 y y0)). Qed.
Lemma lem1549227 (y : real) (y0 : real) : (term357 y y0) = (term369 y y0).
Proof. exact (TRANS (@lem1549200 y y0) (@lem1549226 y y0)). Qed.
Lemma lem1549236 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1549239 (x0 : real) (y : real) (y0 : real) : (term356 x0 y y0) = (term370 x0 y y0).
Proof. exact (MK_COMB (@lem1549236 x0) (@lem1549227 y y0)). Qed.
Lemma lem1549240 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1549241 (x0 : real) (y : real) (y0 : real) : (term371 x0 y y0) = (term372 x0 y y0).
Proof. exact (MK_COMB (@lem1549240) (@lem1549239 x0 y y0)). Qed.
Lemma lem1549242 (x0 : real) (y : real) (y0 : real) : (term373 x0 y y0) = (term374 x0 y y0).
Proof. exact (MK_COMB (@lem1549241 x0 y y0) (@lem1549130)). Qed.
Lemma lem1549243 (x0 : real) (y : real) (y0 : real) : (term374 x0 y y0) = (term375 x0 y y0).
Proof. exact (@lem1483519 (term370 x0 y y0) term47). Qed.
Lemma lem1549245 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1549246 : term138 = term47.
Proof. exact (@lem1549245 term66). Qed.
Lemma lem1549247 (x0 : real) (y : real) (y0 : real) : (term376 x0 y y0) = (term376 x0 y y0).
Proof. exact (eq_refl (term376 x0 y y0)). Qed.
Lemma lem1549248 (x0 : real) (y : real) (y0 : real) : (term375 x0 y y0) = (term377 x0 y y0).
Proof. exact (MK_COMB (@lem1549247 x0 y y0) (@lem1549246)). Qed.
Lemma lem1549249 (x0 : real) (y : real) (y0 : real) : (term377 x0 y y0) = (term370 x0 y y0).
Proof. exact (@lem1483450 (term370 x0 y y0)). Qed.
Lemma lem1549250 (x0 : real) (y : real) (y0 : real) : (term375 x0 y y0) = (term370 x0 y y0).
Proof. exact (TRANS (@lem1549248 x0 y y0) (@lem1549249 x0 y y0)). Qed.
Lemma lem1549251 (x0 : real) (y : real) (y0 : real) : (term374 x0 y y0) = (term370 x0 y y0).
Proof. exact (TRANS (@lem1549243 x0 y y0) (@lem1549250 x0 y y0)). Qed.
Lemma lem1549252 (x0 : real) (y : real) (y0 : real) : (term373 x0 y y0) = (term370 x0 y y0).
Proof. exact (TRANS (@lem1549242 x0 y y0) (@lem1549251 x0 y y0)). Qed.
Lemma lem1549253 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549254 (x0 : real) (y : real) (y0 : real) : (term378 x0 y y0) = (term379 x0 y y0).
Proof. exact (MK_COMB (@lem1549253) (@lem1549252 x0 y y0)). Qed.
Lemma lem1549255 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549256 (x0 : real) (y : real) (y0 : real) : (term355 x0 y y0) = (term380 x0 y y0).
Proof. exact (MK_COMB (@lem1549254 x0 y y0) (@lem1549255)). Qed.
Lemma lem1549257 (x0 : real) (y : real) (y0 : real) : (term354 x0 y y0) = (term380 x0 y y0).
Proof. exact (TRANS (@lem1549129 x0 y y0) (@lem1549256 x0 y y0)). Qed.
Lemma lem1549258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549259 (x : real) (x0 : real) (y0 : real) : (term289 x x0 y0) = (term289 x x0 y0).
Proof. exact (MK_COMB (@lem1549258) (@lem1548968 x x0 y0)). Qed.
Lemma lem1549260 (x : real) (x0 : real) (y : real) (y0 : real) : (term381 x x0 y y0) = (term382 x x0 y y0).
Proof. exact (MK_COMB (@lem1549259 x x0 y0) (@lem1549257 x0 y y0)). Qed.
Lemma lem1549261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549262 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1549261) (@lem1548440 x0 y0)). Qed.
Lemma lem1549263 (x : real) (x0 : real) (y : real) (y0 : real) : (term383 x x0 y y0) = (term384 x x0 y y0).
Proof. exact (MK_COMB (@lem1549262 x0 y0) (@lem1549260 x x0 y y0)). Qed.
Lemma lem1549264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549265 (x : real) (x0 : real) (y : real) (y0 : real) : (term385 x x0 y y0) = (term386 x x0 y y0).
Proof. exact (MK_COMB (@lem1549264) (@lem1549263 x x0 y y0)). Qed.
Lemma lem1549266 (x0 : real) (y0 : real) (x : real) (y : real) : (term387 x0 y0 x y) = (term388 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549265 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1549267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549268 (x : real) (x0 : real) : (term97 x x0) = (term97 x x0).
Proof. exact (MK_COMB (@lem1549267) (@lem1548923 x x0)). Qed.
Lemma lem1549269 (x0 : real) (y0 : real) (x : real) (y : real) : (term304 x0 y0 x y) = (term389 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549268 x x0) (@lem1549266 x0 y0 x y)). Qed.
Lemma lem1549270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549271 (y : real) (y0 : real) : (term120 y y0) = (term97 y y0).
Proof. exact (MK_COMB (@lem1549270) (@lem1549128 y y0)). Qed.
Lemma lem1549272 (x0 : real) (y0 : real) (x : real) (y : real) : (term306 x0 y0 x y) = (term390 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549271 y y0) (@lem1549269 x0 y0 x y)). Qed.
Lemma lem1549273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1549274 (x0 : real) (y0 : real) (x : real) (y : real) : (term312 x0 y0 x y) = (term391 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549273) (@lem1549076 x0 y0 x y)). Qed.
Lemma lem1549275 (x0 : real) (y0 : real) (x : real) (y : real) : (term313 x0 y0 x y) = (term392 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549274 x0 y0 x y) (@lem1549272 x0 y0 x y)). Qed.
Lemma lem1549287 (x0 : real) (y0 : real) (x : real) (y : real) : (term297 x0 y0 x y) = (term392 x0 y0 x y).
Proof. exact (TRANS (@lem1548857 x0 y0 x y) (@lem1549275 x0 y0 x y)). Qed.
Lemma lem1549289 (x0 : real) (y0 : real) (x : real) (y : real) : (term393 x0 x y y0) = (term220 x0 y0 x y).
Proof. exact (eq_refl (term393 x0 x y y0)). Qed.
Lemma lem1549290 (x0 : real) (x : real) (y : real) (y0 : real) : (term220 x0 y0 x y) = (term393 x0 x y y0).
Proof. exact (SYM (@lem1549289 x0 y0 x y)). Qed.
Lemma lem1549291 (x0 : real) (x : real) (y : real) (y0 : real) : (term393 x0 x y y0) = (term394 x0 x y y0).
Proof. exact (@lem1482981 (term395 x0 y0 x y) (real_sub y y0)). Qed.
Lemma lem1549292 (x0 : real) (x : real) (y : real) (y0 : real) : (term220 x0 y0 x y) = (term394 x0 x y y0).
Proof. exact (TRANS (@lem1549290 x0 x y y0) (@lem1549291 x0 x y y0)). Qed.
Lemma lem1549293 (x0 : real) (y0 : real) (x : real) (y : real) : (term396 x0 x y y0) = (term397 x0 y0 x y).
Proof. exact (eq_refl (term396 x0 x y y0)). Qed.
Lemma lem1549294 (y : real) (y0 : real) : (term120 y y0) = (term120 y y0).
Proof. exact (eq_refl (term120 y y0)). Qed.
Lemma lem1549295 (x0 : real) (y0 : real) (x : real) (y : real) : (term398 x0 x y y0) = (term399 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549294 y y0) (@lem1549293 x0 y0 x y)). Qed.
Lemma lem1549296 (x0 : real) (y0 : real) (x : real) (y : real) : (term400 x0 x y y0) = (term401 x0 y0 x y).
Proof. exact (eq_refl (term400 x0 x y y0)). Qed.
Lemma lem1549297 (y : real) (y0 : real) : (term125 y y0) = (term125 y y0).
Proof. exact (eq_refl (term125 y y0)). Qed.
Lemma lem1549298 (x0 : real) (y0 : real) (x : real) (y : real) : (term402 x0 x y y0) = (term403 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549297 y y0) (@lem1549296 x0 y0 x y)). Qed.
Lemma lem1549299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1549300 (x0 : real) (y0 : real) (x : real) (y : real) : (term404 x0 x y y0) = (term405 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549299) (@lem1549298 x0 y0 x y)). Qed.
Lemma lem1549301 (x0 : real) (y0 : real) (x : real) (y : real) : (term394 x0 x y y0) = (term406 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549300 x0 y0 x y) (@lem1549295 x0 y0 x y)). Qed.
Lemma lem1549302 (x0 : real) (y0 : real) (x : real) (y : real) : (term407 x0 y0 x y) = (term407 x0 y0 x y).
Proof. exact (eq_refl (term407 x0 y0 x y)). Qed.
Lemma lem1549303 (x0 : real) (y0 : real) (x : real) (y : real) : ((term220 x0 y0 x y) = (term394 x0 x y y0)) = ((term220 x0 y0 x y) = (term406 x0 y0 x y)).
Proof. exact (MK_COMB (@lem1549302 x0 y0 x y) (@lem1549301 x0 y0 x y)). Qed.
Lemma lem1549304 (x0 : real) (y0 : real) (x : real) (y : real) : (term220 x0 y0 x y) = (term406 x0 y0 x y).
Proof. exact (EQ_MP (@lem1549303 x0 y0 x y) (@lem1549292 x0 x y y0)). Qed.
Lemma lem1549305 (x : real) (x0 : real) : (term103 x x0) = (term214 x x0).
Proof. exact (@lem1483527 (term42 x x0) term47). Qed.
Lemma lem1549323 (x : real) (x0 : real) : (term135 x x0) = (term136 x x0).
Proof. exact (@lem1483519 (term42 x x0) term47). Qed.
Lemma lem1549325 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1549326 : term138 = term47.
Proof. exact (@lem1549325 term66). Qed.
Lemma lem1549327 (x : real) (x0 : real) : (term139 x x0) = (term139 x x0).
Proof. exact (eq_refl (term139 x x0)). Qed.
Lemma lem1549328 (x : real) (x0 : real) : (term136 x x0) = (term140 x x0).
Proof. exact (MK_COMB (@lem1549327 x x0) (@lem1549326)). Qed.
Lemma lem1549329 (x : real) (x0 : real) : (term140 x x0) = (term42 x x0).
Proof. exact (@lem1483450 (term42 x x0)). Qed.
Lemma lem1549330 (x : real) (x0 : real) : (term136 x x0) = (term42 x x0).
Proof. exact (TRANS (@lem1549328 x x0) (@lem1549329 x x0)). Qed.
Lemma lem1549332 (x : real) (x0 : real) : (term135 x x0) = (term42 x x0).
Proof. exact (TRANS (@lem1549323 x x0) (@lem1549330 x x0)). Qed.
Lemma lem1549333 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1549334 (x : real) (x0 : real) : (term215 x x0) = (term102 x x0).
Proof. exact (MK_COMB (@lem1549333) (@lem1549332 x x0)). Qed.
Lemma lem1549335 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549336 (x : real) (x0 : real) : (term214 x x0) = (term103 x x0).
Proof. exact (MK_COMB (@lem1549334 x x0) (@lem1549335)). Qed.
Lemma lem1549337 (x : real) (x0 : real) : (term103 x x0) = (term103 x x0).
Proof. exact (TRANS (@lem1549305 x x0) (@lem1549336 x x0)). Qed.
Lemma lem1549338 (x : real) (x0 : real) (y0 : real) : (term201 x x0 y0) = (term408 x x0 y0).
Proof. exact (@lem1483525 (term191 x x0 y0) term47). Qed.
Lemma lem1549362 (x : real) (x0 : real) (y0 : real) : (term195 x x0 y0) = (term196 x x0 y0).
Proof. exact (@lem1483519 (term191 x x0 y0) term47). Qed.
Lemma lem1549364 (x : nat) : (term137 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1549365 : term138 = term47.
Proof. exact (@lem1549364 term66). Qed.
Lemma lem1549366 (x : real) (x0 : real) (y0 : real) : (term197 x x0 y0) = (term197 x x0 y0).
Proof. exact (eq_refl (term197 x x0 y0)). Qed.
Lemma lem1549367 (x : real) (x0 : real) (y0 : real) : (term196 x x0 y0) = (term198 x x0 y0).
Proof. exact (MK_COMB (@lem1549366 x x0 y0) (@lem1549365)). Qed.
Lemma lem1549368 (x : real) (x0 : real) (y0 : real) : (term198 x x0 y0) = (term191 x x0 y0).
Proof. exact (@lem1483450 (term191 x x0 y0)). Qed.
Lemma lem1549369 (x : real) (x0 : real) (y0 : real) : (term196 x x0 y0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1549367 x x0 y0) (@lem1549368 x x0 y0)). Qed.
Lemma lem1549371 (x : real) (x0 : real) (y0 : real) : (term195 x x0 y0) = (term191 x x0 y0).
Proof. exact (TRANS (@lem1549362 x x0 y0) (@lem1549369 x x0 y0)). Qed.
Lemma lem1549372 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549373 (x : real) (x0 : real) (y0 : real) : (term409 x x0 y0) = (term200 x x0 y0).
Proof. exact (MK_COMB (@lem1549372) (@lem1549371 x x0 y0)). Qed.
Lemma lem1549374 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549375 (x : real) (x0 : real) (y0 : real) : (term408 x x0 y0) = (term201 x x0 y0).
Proof. exact (MK_COMB (@lem1549373 x x0 y0) (@lem1549374)). Qed.
Lemma lem1549376 (x : real) (x0 : real) (y0 : real) : (term201 x x0 y0) = (term201 x x0 y0).
Proof. exact (TRANS (@lem1549338 x x0 y0) (@lem1549375 x x0 y0)). Qed.
Lemma lem1549377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549378 (x : real) (x0 : real) (y0 : real) : (term209 x x0 y0) = (term209 x x0 y0).
Proof. exact (MK_COMB (@lem1549377) (@lem1549376 x x0 y0)). Qed.
Lemma lem1549379 (x : real) (x0 : real) (y : real) (y0 : real) : (term410 x x0 y y0) = (term411 x x0 y y0).
Proof. exact (MK_COMB (@lem1549378 x x0 y0) (@lem1549061 x0 y y0)). Qed.
Lemma lem1549380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549381 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1549380) (@lem1548440 x0 y0)). Qed.
Lemma lem1549382 (x : real) (x0 : real) (y : real) (y0 : real) : (term412 x x0 y y0) = (term413 x x0 y y0).
Proof. exact (MK_COMB (@lem1549381 x0 y0) (@lem1549379 x x0 y y0)). Qed.
Lemma lem1549383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549384 (x : real) (x0 : real) (y : real) (y0 : real) : (term414 x x0 y y0) = (term415 x x0 y y0).
Proof. exact (MK_COMB (@lem1549383) (@lem1549382 x x0 y y0)). Qed.
Lemma lem1549385 (x0 : real) (y0 : real) (x : real) (y : real) : (term416 x0 y0 x y) = (term417 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549384 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1549386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549387 (x : real) (x0 : real) : (term219 x x0) = (term219 x x0).
Proof. exact (MK_COMB (@lem1549386) (@lem1549337 x x0)). Qed.
Lemma lem1549388 (x0 : real) (y0 : real) (x : real) (y : real) : (term401 x0 y0 x y) = (term418 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549387 x x0) (@lem1549385 x0 y0 x y)). Qed.
Lemma lem1549389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549390 (y : real) (y0 : real) : (term125 y y0) = (term219 y y0).
Proof. exact (MK_COMB (@lem1549389) (@lem1548890 y y0)). Qed.
Lemma lem1549391 (x0 : real) (y0 : real) (x : real) (y : real) : (term403 x0 y0 x y) = (term419 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549390 y y0) (@lem1549388 x0 y0 x y)). Qed.
Lemma lem1549392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549393 (x : real) (x0 : real) (y0 : real) : (term209 x x0 y0) = (term209 x x0 y0).
Proof. exact (MK_COMB (@lem1549392) (@lem1549376 x x0 y0)). Qed.
Lemma lem1549394 (x : real) (x0 : real) (y : real) (y0 : real) : (term420 x x0 y y0) = (term421 x x0 y y0).
Proof. exact (MK_COMB (@lem1549393 x x0 y0) (@lem1549257 x0 y y0)). Qed.
Lemma lem1549395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549396 (x0 : real) (y0 : real) : (term97 x0 y0) = (term97 x0 y0).
Proof. exact (MK_COMB (@lem1549395) (@lem1548440 x0 y0)). Qed.
Lemma lem1549397 (x : real) (x0 : real) (y : real) (y0 : real) : (term422 x x0 y y0) = (term423 x x0 y y0).
Proof. exact (MK_COMB (@lem1549396 x0 y0) (@lem1549394 x x0 y y0)). Qed.
Lemma lem1549398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549399 (x : real) (x0 : real) (y : real) (y0 : real) : (term424 x x0 y y0) = (term425 x x0 y y0).
Proof. exact (MK_COMB (@lem1549398) (@lem1549397 x x0 y y0)). Qed.
Lemma lem1549400 (x0 : real) (y0 : real) (x : real) (y : real) : (term426 x0 y0 x y) = (term427 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549399 x x0 y y0) (@lem1548634 x y)). Qed.
Lemma lem1549401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549402 (x : real) (x0 : real) : (term219 x x0) = (term219 x x0).
Proof. exact (MK_COMB (@lem1549401) (@lem1549337 x x0)). Qed.
Lemma lem1549403 (x0 : real) (y0 : real) (x : real) (y : real) : (term397 x0 y0 x y) = (term428 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549402 x x0) (@lem1549400 x0 y0 x y)). Qed.
Lemma lem1549404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1549405 (y : real) (y0 : real) : (term120 y y0) = (term97 y y0).
Proof. exact (MK_COMB (@lem1549404) (@lem1549128 y y0)). Qed.
Lemma lem1549406 (x0 : real) (y0 : real) (x : real) (y : real) : (term399 x0 y0 x y) = (term429 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549405 y y0) (@lem1549403 x0 y0 x y)). Qed.
Lemma lem1549407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1549408 (x0 : real) (y0 : real) (x : real) (y : real) : (term405 x0 y0 x y) = (term430 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549407) (@lem1549391 x0 y0 x y)). Qed.
Lemma lem1549409 (x0 : real) (y0 : real) (x : real) (y : real) : (term406 x0 y0 x y) = (term431 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549408 x0 y0 x y) (@lem1549406 x0 y0 x y)). Qed.
Lemma lem1549421 (x0 : real) (y0 : real) (x : real) (y : real) : (term220 x0 y0 x y) = (term431 x0 y0 x y).
Proof. exact (TRANS (@lem1549304 x0 y0 x y) (@lem1549409 x0 y0 x y)). Qed.
Lemma lem1549422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1549423 (x0 : real) (y0 : real) (x : real) (y : real) : (term298 x0 y0 x y) = (term432 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549422) (@lem1549421 x0 y0 x y)). Qed.
Lemma lem1549424 (x0 : real) (y0 : real) (x : real) (y : real) : (term299 x0 y0 x y) = (term433 x0 y0 x y).
Proof. exact (MK_COMB (@lem1549423 x0 y0 x y) (@lem1549287 x0 y0 x y)). Qed.
Lemma lem1549426 (x0 : real) (y0 : real) (x : real) (y : real) : (term106 x0 y0 x y) = (term433 x0 y0 x y).
Proof. exact (TRANS (@lem1548840 x0 y0 x y) (@lem1549424 x0 y0 x y)). Qed.
Lemma lem1549427 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term433 x0 y0 x y) : term433 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1549428 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term431 x0 y0 x y) : term431 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1549429 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term419 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1549430 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term418 x0 y0 x y.
Proof. exact (proj2 (@lem1549429 x0 y0 x y h1)). Qed.
Lemma lem1549431 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term103 y y0.
Proof. exact (proj1 (@lem1549429 x0 y0 x y h1)). Qed.
Lemma lem1549432 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term417 x0 y0 x y.
Proof. exact (proj2 (@lem1549430 x0 y0 x y h1)). Qed.
Lemma lem1549434 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term103 x y.
Proof. exact (proj2 (@lem1549432 x0 y0 x y h1)). Qed.
Lemma lem1549435 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term413 x x0 y y0.
Proof. exact (proj1 (@lem1549432 x0 y0 x y h1)). Qed.
Lemma lem1549436 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term411 x x0 y y0.
Proof. exact (proj2 (@lem1549435 x0 y0 x y h1)). Qed.
Lemma lem1549438 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term343 x0 y y0.
Proof. exact (proj2 (@lem1549436 x0 y0 x y h1)). Qed.
Lemma lem1549439 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term201 x x0 y0.
Proof. exact (proj1 (@lem1549436 x0 y0 x y h1)). Qed.
Lemma lem1549441 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549442 : term435 = term436.
Proof. exact (@lem1549441 (NUMERAL 0) term67). Qed.
Lemma lem1549443 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1549444 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1549445 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1549444 h1) (fun h1 : term436 = True => @lem1549443)). Qed.
Lemma lem1549446 : term436 = True.
Proof. exact (EQ_MP (@lem1549445) (@lem1549443)). Qed.
Lemma lem1549447 : term435 = True.
Proof. exact (TRANS (@lem1549442) (@lem1549446)). Qed.
Lemma lem1549448 : True = term435.
Proof. exact (SYM (@lem1549447)). Qed.
Lemma lem1549449 : term435.
Proof. exact (EQ_MP (@lem1549448) (@lem0)). Qed.
Lemma lem1549450 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term438 y y0.
Proof. exact (conj (@lem1549449) (@lem1549431 x0 y0 x y h1)). Qed.
Lemma lem1549452 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1549453 (y : real) (y0 : real) : term440 y y0.
Proof. exact (@lem1549452 term60 (term42 y y0)). Qed.
Lemma lem1549454 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term441 y y0.
Proof. exact (@lem1549453 y y0 (@lem1549450 x0 y0 x y h1)). Qed.
Lemma lem1549455 (y : real) (y0 : real) : (term442 y y0) = (term443 y y0).
Proof. exact (@lem1483508 y term60 (term44 y0)). Qed.
Lemma lem1549456 (y0 : real) : (term444 y0) = (term445 y0).
Proof. exact (@lem1483476 term60 term59 y0). Qed.
Lemma lem1549458 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1549459 : term447 = term448.
Proof. exact (@lem1549458 term67 term66). Qed.
Lemma lem1549460 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549461 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549462 : term160 = term67.
Proof. exact (EQ_MP (@lem1549461) (@lem1549460)). Qed.
Lemma lem1549463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549464 : term158 = term60.
Proof. exact (MK_COMB (@lem1549463) (@lem1549462)). Qed.
Lemma lem1549465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549466 : term448 = term72.
Proof. exact (MK_COMB (@lem1549465) (@lem1549464)). Qed.
Lemma lem1549467 : term447 = term72.
Proof. exact (TRANS (@lem1549459) (@lem1549466)). Qed.
Lemma lem1549468 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549469 : term449 = term74.
Proof. exact (MK_COMB (@lem1549468) (@lem1549467)). Qed.
Lemma lem1549470 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549471 (y0 : real) : (term445 y0) = (term169 y0).
Proof. exact (MK_COMB (@lem1549469) (@lem1549470 y0)). Qed.
Lemma lem1549472 (y0 : real) : (term444 y0) = (term169 y0).
Proof. exact (TRANS (@lem1549456 y0) (@lem1549471 y0)). Qed.
Lemma lem1549475 (y : real) : (term248 y) = (term248 y).
Proof. exact (eq_refl (term248 y)). Qed.
Lemma lem1549476 (y : real) (y0 : real) : (term443 y y0) = (term249 y y0).
Proof. exact (MK_COMB (@lem1549475 y) (@lem1549472 y0)). Qed.
Lemma lem1549477 (y : real) (y0 : real) : (term442 y y0) = (term249 y y0).
Proof. exact (TRANS (@lem1549455 y y0) (@lem1549476 y y0)). Qed.
Lemma lem1549478 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1549479 (y : real) (y0 : real) : (term450 y y0) = (term451 y y0).
Proof. exact (MK_COMB (@lem1549478) (@lem1549477 y y0)). Qed.
Lemma lem1549480 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549481 (y : real) (y0 : real) : (term441 y y0) = (term452 y y0).
Proof. exact (MK_COMB (@lem1549479 y y0) (@lem1549480)). Qed.
Lemma lem1549482 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term452 y y0.
Proof. exact (EQ_MP (@lem1549481 y y0) (@lem1549454 x0 y0 x y h1)). Qed.
Lemma lem1549484 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549485 : term453 = term454.
Proof. exact (@lem1549484 (NUMERAL 0) term66). Qed.
Lemma lem1549486 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549487 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549488 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549487 h1) (fun h1 : term454 = True => @lem1549486)). Qed.
Lemma lem1549489 : term454 = True.
Proof. exact (EQ_MP (@lem1549488) (@lem1549486)). Qed.
Lemma lem1549490 : term453 = True.
Proof. exact (TRANS (@lem1549485) (@lem1549489)). Qed.
Lemma lem1549491 : True = term453.
Proof. exact (SYM (@lem1549490)). Qed.
Lemma lem1549492 : term453.
Proof. exact (EQ_MP (@lem1549491) (@lem0)). Qed.
Lemma lem1549493 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term456 x0 y y0.
Proof. exact (conj (@lem1549492) (@lem1549438 x0 y0 x y h1)). Qed.
Lemma lem1549495 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549496 (x0 : real) (y : real) (y0 : real) : term458 x0 y y0.
Proof. exact (@lem1549495 term181 (term333 x0 y y0)). Qed.
Lemma lem1549497 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term459 x0 y y0.
Proof. exact (@lem1549496 x0 y y0 (@lem1549493 x0 y0 x y h1)). Qed.
Lemma lem1549498 (x0 : real) (y : real) (y0 : real) : (term460 x0 y y0) = (term333 x0 y y0).
Proof. exact (@lem1483460 (term333 x0 y y0)). Qed.
Lemma lem1549499 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549500 (x0 : real) (y : real) (y0 : real) : (term461 x0 y y0) = (term342 x0 y y0).
Proof. exact (MK_COMB (@lem1549499) (@lem1549498 x0 y y0)). Qed.
Lemma lem1549501 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549502 (x0 : real) (y : real) (y0 : real) : (term459 x0 y y0) = (term343 x0 y y0).
Proof. exact (MK_COMB (@lem1549500 x0 y y0) (@lem1549501)). Qed.
Lemma lem1549503 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term343 x0 y y0.
Proof. exact (EQ_MP (@lem1549502 x0 y y0) (@lem1549497 x0 y0 x y h1)). Qed.
Lemma lem1549504 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term462 x0 y y0.
Proof. exact (conj (@lem1549503 x0 y0 x y h1) (@lem1549482 x0 y0 x y h1)). Qed.
Lemma lem1549506 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1549507 (x0 : real) (y : real) (y0 : real) : term464 x0 y y0.
Proof. exact (@lem1549506 (term333 x0 y y0) (term249 y y0)). Qed.
Lemma lem1549508 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term465 x0 y y0.
Proof. exact (@lem1549507 x0 y y0 (@lem1549504 x0 y0 x y h1)). Qed.
Lemma lem1549509 (x0 : real) (y : real) (y0 : real) : (term466 x0 y y0) = (term467 x0 y y0).
Proof. exact (@lem1483482 (term44 x0) (term332 y y0) (term249 y y0)). Qed.
Lemma lem1549510 (y : real) (y0 : real) : (term468 y y0) = (term469 y y0).
Proof. exact (@lem1483480 (term169 y) (term163 y) (term331 y0) (term169 y0)). Qed.
Lemma lem1549511 (y : real) : (term470 y) = (term471 y).
Proof. exact (@lem1483438 term72 term60 y). Qed.
Lemma lem1549513 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1549514 : term473 = term47.
Proof. exact (@lem1549513 term67). Qed.
Lemma lem1549515 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549516 : term474 = term475.
Proof. exact (MK_COMB (@lem1549515) (@lem1549514)). Qed.
Lemma lem1549517 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549518 (y : real) : (term471 y) = (term476 y).
Proof. exact (MK_COMB (@lem1549516) (@lem1549517 y)). Qed.
Lemma lem1549519 (y : real) : (term470 y) = (term476 y).
Proof. exact (TRANS (@lem1549511 y) (@lem1549518 y)). Qed.
Lemma lem1549520 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1549521 (y : real) : (term470 y) = term47.
Proof. exact (TRANS (@lem1549519 y) (@lem1549520 y)). Qed.
Lemma lem1549522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549523 (y : real) : (term477 y) = term236.
Proof. exact (MK_COMB (@lem1549522) (@lem1549521 y)). Qed.
Lemma lem1549524 (y0 : real) : (term478 y0) = (term479 y0).
Proof. exact (@lem1483438 term269 term72 y0). Qed.
Lemma lem1549527 : term480 = term181.
Proof. exact (@lem1367769 term67 term66). Qed.
Lemma lem1549528 : term327 = term265.
Proof. exact (@lem706949). Qed.
Lemma lem1549529 : (term327 = term265) = (term328 = term267).
Proof. exact (@lem1006570 term69 (BIT1 0) term265). Qed.
Lemma lem1549530 : term328 = term267.
Proof. exact (EQ_MP (@lem1549529) (@lem1549528)). Qed.
Lemma lem1549531 : term267 = term328.
Proof. exact (SYM (@lem1549530)). Qed.
Lemma lem1549532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549533 : term269 = term326.
Proof. exact (MK_COMB (@lem1549532) (@lem1549531)). Qed.
Lemma lem1549534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549535 : term481 = term482.
Proof. exact (MK_COMB (@lem1549534) (@lem1549533)). Qed.
Lemma lem1549536 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem1549537 : term483 = term480.
Proof. exact (MK_COMB (@lem1549535) (@lem1549536)). Qed.
Lemma lem1549538 : term483 = term181.
Proof. exact (TRANS (@lem1549537) (@lem1549527)). Qed.
Lemma lem1549539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549540 : term484 = term188.
Proof. exact (MK_COMB (@lem1549539) (@lem1549538)). Qed.
Lemma lem1549541 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549542 (y0 : real) : (term479 y0) = (term189 y0).
Proof. exact (MK_COMB (@lem1549540) (@lem1549541 y0)). Qed.
Lemma lem1549543 (y0 : real) : (term478 y0) = (term189 y0).
Proof. exact (TRANS (@lem1549524 y0) (@lem1549542 y0)). Qed.
Lemma lem1549544 (y0 : real) : (term189 y0) = y0.
Proof. exact (@lem1483436 y0). Qed.
Lemma lem1549545 (y0 : real) : (term478 y0) = y0.
Proof. exact (TRANS (@lem1549543 y0) (@lem1549544 y0)). Qed.
Lemma lem1549546 (y : real) (y0 : real) : (term469 y y0) = (term485 y0).
Proof. exact (MK_COMB (@lem1549523 y) (@lem1549545 y0)). Qed.
Lemma lem1549547 (y : real) (y0 : real) : (term468 y y0) = (term485 y0).
Proof. exact (TRANS (@lem1549510 y y0) (@lem1549546 y y0)). Qed.
Lemma lem1549548 (y0 : real) : (term485 y0) = y0.
Proof. exact (@lem1483448 y0). Qed.
Lemma lem1549549 (y : real) (y0 : real) : (term468 y y0) = y0.
Proof. exact (TRANS (@lem1549547 y y0) (@lem1549548 y0)). Qed.
Lemma lem1549550 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1549551 (y : real) (x0 : real) (y0 : real) : (term467 x0 y y0) = (term43 x0 y0).
Proof. exact (MK_COMB (@lem1549550 x0) (@lem1549549 y y0)). Qed.
Lemma lem1549552 (y : real) (x0 : real) (y0 : real) : (term466 x0 y y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1549509 x0 y y0) (@lem1549551 y x0 y0)). Qed.
Lemma lem1549553 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549554 (y : real) (x0 : real) (y0 : real) : (term486 x0 y y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1549553) (@lem1549552 y x0 y0)). Qed.
Lemma lem1549555 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549556 (y : real) (x0 : real) (y0 : real) : (term465 x0 y y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1549554 y x0 y0) (@lem1549555)). Qed.
Lemma lem1549557 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1549556 y x0 y0) (@lem1549508 x0 y0 x y h1)). Qed.
Lemma lem1549559 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549560 : term453 = term454.
Proof. exact (@lem1549559 (NUMERAL 0) term66). Qed.
Lemma lem1549561 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549562 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549563 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549562 h1) (fun h1 : term454 = True => @lem1549561)). Qed.
Lemma lem1549564 : term454 = True.
Proof. exact (EQ_MP (@lem1549563) (@lem1549561)). Qed.
Lemma lem1549565 : term453 = True.
Proof. exact (TRANS (@lem1549560) (@lem1549564)). Qed.
Lemma lem1549566 : True = term453.
Proof. exact (SYM (@lem1549565)). Qed.
Lemma lem1549567 : term453.
Proof. exact (EQ_MP (@lem1549566) (@lem0)). Qed.
Lemma lem1549568 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term487 x0 y0.
Proof. exact (conj (@lem1549567) (@lem1549557 x0 y0 x y h1)). Qed.
Lemma lem1549570 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549571 (x0 : real) (y0 : real) : term488 x0 y0.
Proof. exact (@lem1549570 term181 (term43 x0 y0)). Qed.
Lemma lem1549572 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term489 x0 y0.
Proof. exact (@lem1549571 x0 y0 (@lem1549568 x0 y0 x y h1)). Qed.
Lemma lem1549573 (x0 : real) (y0 : real) : (term490 x0 y0) = (term43 x0 y0).
Proof. exact (@lem1483460 (term43 x0 y0)). Qed.
Lemma lem1549574 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549575 (x0 : real) (y0 : real) : (term491 x0 y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1549574) (@lem1549573 x0 y0)). Qed.
Lemma lem1549576 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549577 (x0 : real) (y0 : real) : (term489 x0 y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1549575 x0 y0) (@lem1549576)). Qed.
Lemma lem1549578 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1549577 x0 y0) (@lem1549572 x0 y0 x y h1)). Qed.
Lemma lem1549580 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549581 : term435 = term436.
Proof. exact (@lem1549580 (NUMERAL 0) term67). Qed.
Lemma lem1549582 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1549583 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1549584 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1549583 h1) (fun h1 : term436 = True => @lem1549582)). Qed.
Lemma lem1549585 : term436 = True.
Proof. exact (EQ_MP (@lem1549584) (@lem1549582)). Qed.
Lemma lem1549586 : term435 = True.
Proof. exact (TRANS (@lem1549581) (@lem1549585)). Qed.
Lemma lem1549587 : True = term435.
Proof. exact (SYM (@lem1549586)). Qed.
Lemma lem1549588 : term435.
Proof. exact (EQ_MP (@lem1549587) (@lem0)). Qed.
Lemma lem1549589 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term438 y y0.
Proof. exact (conj (@lem1549588) (@lem1549431 x0 y0 x y h1)). Qed.
Lemma lem1549591 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1549592 (y : real) (y0 : real) : term440 y y0.
Proof. exact (@lem1549591 term60 (term42 y y0)). Qed.
Lemma lem1549593 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term441 y y0.
Proof. exact (@lem1549592 y y0 (@lem1549589 x0 y0 x y h1)). Qed.
Lemma lem1549594 (y : real) (y0 : real) : (term442 y y0) = (term443 y y0).
Proof. exact (@lem1483508 y term60 (term44 y0)). Qed.
Lemma lem1549595 (y0 : real) : (term444 y0) = (term445 y0).
Proof. exact (@lem1483476 term60 term59 y0). Qed.
Lemma lem1549597 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1549598 : term447 = term448.
Proof. exact (@lem1549597 term67 term66). Qed.
Lemma lem1549599 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549600 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549601 : term160 = term67.
Proof. exact (EQ_MP (@lem1549600) (@lem1549599)). Qed.
Lemma lem1549602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549603 : term158 = term60.
Proof. exact (MK_COMB (@lem1549602) (@lem1549601)). Qed.
Lemma lem1549604 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549605 : term448 = term72.
Proof. exact (MK_COMB (@lem1549604) (@lem1549603)). Qed.
Lemma lem1549606 : term447 = term72.
Proof. exact (TRANS (@lem1549598) (@lem1549605)). Qed.
Lemma lem1549607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549608 : term449 = term74.
Proof. exact (MK_COMB (@lem1549607) (@lem1549606)). Qed.
Lemma lem1549609 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549610 (y0 : real) : (term445 y0) = (term169 y0).
Proof. exact (MK_COMB (@lem1549608) (@lem1549609 y0)). Qed.
Lemma lem1549611 (y0 : real) : (term444 y0) = (term169 y0).
Proof. exact (TRANS (@lem1549595 y0) (@lem1549610 y0)). Qed.
Lemma lem1549614 (y : real) : (term248 y) = (term248 y).
Proof. exact (eq_refl (term248 y)). Qed.
Lemma lem1549615 (y : real) (y0 : real) : (term443 y y0) = (term249 y y0).
Proof. exact (MK_COMB (@lem1549614 y) (@lem1549611 y0)). Qed.
Lemma lem1549616 (y : real) (y0 : real) : (term442 y y0) = (term249 y y0).
Proof. exact (TRANS (@lem1549594 y y0) (@lem1549615 y y0)). Qed.
Lemma lem1549617 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1549618 (y : real) (y0 : real) : (term450 y y0) = (term451 y y0).
Proof. exact (MK_COMB (@lem1549617) (@lem1549616 y y0)). Qed.
Lemma lem1549619 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549620 (y : real) (y0 : real) : (term441 y y0) = (term452 y y0).
Proof. exact (MK_COMB (@lem1549618 y y0) (@lem1549619)). Qed.
Lemma lem1549621 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term452 y y0.
Proof. exact (EQ_MP (@lem1549620 y y0) (@lem1549593 x0 y0 x y h1)). Qed.
Lemma lem1549623 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549624 : term435 = term436.
Proof. exact (@lem1549623 (NUMERAL 0) term67). Qed.
Lemma lem1549625 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1549626 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1549627 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1549626 h1) (fun h1 : term436 = True => @lem1549625)). Qed.
Lemma lem1549628 : term436 = True.
Proof. exact (EQ_MP (@lem1549627) (@lem1549625)). Qed.
Lemma lem1549629 : term435 = True.
Proof. exact (TRANS (@lem1549624) (@lem1549628)). Qed.
Lemma lem1549630 : True = term435.
Proof. exact (SYM (@lem1549629)). Qed.
Lemma lem1549631 : term435.
Proof. exact (EQ_MP (@lem1549630) (@lem0)). Qed.
Lemma lem1549632 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term438 x y.
Proof. exact (conj (@lem1549631) (@lem1549434 x0 y0 x y h1)). Qed.
Lemma lem1549634 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1549635 (x : real) (y : real) : term440 x y.
Proof. exact (@lem1549634 term60 (term42 x y)). Qed.
Lemma lem1549636 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term441 x y.
Proof. exact (@lem1549635 x y (@lem1549632 x0 y0 x y h1)). Qed.
Lemma lem1549637 (x : real) (y : real) : (term442 x y) = (term443 x y).
Proof. exact (@lem1483508 x term60 (term44 y)). Qed.
Lemma lem1549638 (y : real) : (term444 y) = (term445 y).
Proof. exact (@lem1483476 term60 term59 y). Qed.
Lemma lem1549640 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1549641 : term447 = term448.
Proof. exact (@lem1549640 term67 term66). Qed.
Lemma lem1549642 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549643 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549644 : term160 = term67.
Proof. exact (EQ_MP (@lem1549643) (@lem1549642)). Qed.
Lemma lem1549645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549646 : term158 = term60.
Proof. exact (MK_COMB (@lem1549645) (@lem1549644)). Qed.
Lemma lem1549647 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549648 : term448 = term72.
Proof. exact (MK_COMB (@lem1549647) (@lem1549646)). Qed.
Lemma lem1549649 : term447 = term72.
Proof. exact (TRANS (@lem1549641) (@lem1549648)). Qed.
Lemma lem1549650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549651 : term449 = term74.
Proof. exact (MK_COMB (@lem1549650) (@lem1549649)). Qed.
Lemma lem1549652 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549653 (y : real) : (term445 y) = (term169 y).
Proof. exact (MK_COMB (@lem1549651) (@lem1549652 y)). Qed.
Lemma lem1549654 (y : real) : (term444 y) = (term169 y).
Proof. exact (TRANS (@lem1549638 y) (@lem1549653 y)). Qed.
Lemma lem1549657 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1549658 (x : real) (y : real) : (term443 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1549657 x) (@lem1549654 y)). Qed.
Lemma lem1549659 (x : real) (y : real) : (term442 x y) = (term249 x y).
Proof. exact (TRANS (@lem1549637 x y) (@lem1549658 x y)). Qed.
Lemma lem1549660 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1549661 (x : real) (y : real) : (term450 x y) = (term451 x y).
Proof. exact (MK_COMB (@lem1549660) (@lem1549659 x y)). Qed.
Lemma lem1549662 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549663 (x : real) (y : real) : (term441 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1549661 x y) (@lem1549662)). Qed.
Lemma lem1549664 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term452 x y.
Proof. exact (EQ_MP (@lem1549663 x y) (@lem1549636 x0 y0 x y h1)). Qed.
Lemma lem1549666 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549667 : term453 = term454.
Proof. exact (@lem1549666 (NUMERAL 0) term66). Qed.
Lemma lem1549668 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549669 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549670 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549669 h1) (fun h1 : term454 = True => @lem1549668)). Qed.
Lemma lem1549671 : term454 = True.
Proof. exact (EQ_MP (@lem1549670) (@lem1549668)). Qed.
Lemma lem1549672 : term453 = True.
Proof. exact (TRANS (@lem1549667) (@lem1549671)). Qed.
Lemma lem1549673 : True = term453.
Proof. exact (SYM (@lem1549672)). Qed.
Lemma lem1549674 : term453.
Proof. exact (EQ_MP (@lem1549673) (@lem0)). Qed.
Lemma lem1549675 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term492 x x0 y0.
Proof. exact (conj (@lem1549674) (@lem1549439 x0 y0 x y h1)). Qed.
Lemma lem1549677 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549678 (x : real) (x0 : real) (y0 : real) : term493 x x0 y0.
Proof. exact (@lem1549677 term181 (term191 x x0 y0)). Qed.
Lemma lem1549679 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term494 x x0 y0.
Proof. exact (@lem1549678 x x0 y0 (@lem1549675 x0 y0 x y h1)). Qed.
Lemma lem1549680 (x : real) (x0 : real) (y0 : real) : (term495 x x0 y0) = (term191 x x0 y0).
Proof. exact (@lem1483460 (term191 x x0 y0)). Qed.
Lemma lem1549681 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549682 (x : real) (x0 : real) (y0 : real) : (term496 x x0 y0) = (term200 x x0 y0).
Proof. exact (MK_COMB (@lem1549681) (@lem1549680 x x0 y0)). Qed.
Lemma lem1549683 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549684 (x : real) (x0 : real) (y0 : real) : (term494 x x0 y0) = (term201 x x0 y0).
Proof. exact (MK_COMB (@lem1549682 x x0 y0) (@lem1549683)). Qed.
Lemma lem1549685 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term201 x x0 y0.
Proof. exact (EQ_MP (@lem1549684 x x0 y0) (@lem1549679 x0 y0 x y h1)). Qed.
Lemma lem1549686 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term497 x0 y0 x y.
Proof. exact (conj (@lem1549685 x0 y0 x y h1) (@lem1549664 x0 y0 x y h1)). Qed.
Lemma lem1549688 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1549689 (x0 : real) (y0 : real) (x : real) (y : real) : term498 x0 y0 x y.
Proof. exact (@lem1549688 (term191 x x0 y0) (term249 x y)). Qed.
Lemma lem1549690 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term499 x0 y0 x y.
Proof. exact (@lem1549689 x0 y0 x y (@lem1549686 x0 y0 x y h1)). Qed.
Lemma lem1549691 (x : real) (x0 : real) (y0 : real) (y : real) : (term500 x0 y0 x y) = (term501 x x0 y0 y).
Proof. exact (@lem1483480 (term169 x) (term163 x) (real_add x0 y0) (term169 y)). Qed.
Lemma lem1549692 (x : real) : (term470 x) = (term471 x).
Proof. exact (@lem1483438 term72 term60 x). Qed.
Lemma lem1549694 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1549695 : term473 = term47.
Proof. exact (@lem1549694 term67). Qed.
Lemma lem1549696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549697 : term474 = term475.
Proof. exact (MK_COMB (@lem1549696) (@lem1549695)). Qed.
Lemma lem1549698 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1549699 (x : real) : (term471 x) = (term476 x).
Proof. exact (MK_COMB (@lem1549697) (@lem1549698 x)). Qed.
Lemma lem1549700 (x : real) : (term470 x) = (term476 x).
Proof. exact (TRANS (@lem1549692 x) (@lem1549699 x)). Qed.
Lemma lem1549701 (x : real) : (term476 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1549702 (x : real) : (term470 x) = term47.
Proof. exact (TRANS (@lem1549700 x) (@lem1549701 x)). Qed.
Lemma lem1549703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549704 (x : real) : (term477 x) = term236.
Proof. exact (MK_COMB (@lem1549703) (@lem1549702 x)). Qed.
Lemma lem1549705 (x0 : real) (y0 : real) (y : real) : (term502 x0 y0 y) = (term503 x0 y0 y).
Proof. exact (@lem1483482 x0 y0 (term169 y)). Qed.
Lemma lem1549706 (y : real) (y0 : real) : (term253 y0 y) = (term254 y y0).
Proof. exact (@lem1483488 (term169 y) y0). Qed.
Lemma lem1549707 (x0 : real) : (real_add x0) = (real_add x0).
Proof. exact (eq_refl (real_add x0)). Qed.
Lemma lem1549708 (x0 : real) (y : real) (y0 : real) : (term503 x0 y0 y) = (term504 x0 y y0).
Proof. exact (MK_COMB (@lem1549707 x0) (@lem1549706 y y0)). Qed.
Lemma lem1549709 (x0 : real) (y : real) (y0 : real) : (term502 x0 y0 y) = (term504 x0 y y0).
Proof. exact (TRANS (@lem1549705 x0 y0 y) (@lem1549708 x0 y y0)). Qed.
Lemma lem1549710 (x : real) (x0 : real) (y : real) (y0 : real) : (term501 x x0 y0 y) = (term505 x0 y y0).
Proof. exact (MK_COMB (@lem1549704 x) (@lem1549709 x0 y y0)). Qed.
Lemma lem1549711 (x : real) (x0 : real) (y : real) (y0 : real) : (term500 x0 y0 x y) = (term505 x0 y y0).
Proof. exact (TRANS (@lem1549691 x x0 y0 y) (@lem1549710 x x0 y y0)). Qed.
Lemma lem1549712 (x0 : real) (y : real) (y0 : real) : (term505 x0 y y0) = (term504 x0 y y0).
Proof. exact (@lem1483448 (term504 x0 y y0)). Qed.
Lemma lem1549713 (x : real) (x0 : real) (y : real) (y0 : real) : (term500 x0 y0 x y) = (term504 x0 y y0).
Proof. exact (TRANS (@lem1549711 x x0 y y0) (@lem1549712 x0 y y0)). Qed.
Lemma lem1549714 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549715 (x : real) (x0 : real) (y : real) (y0 : real) : (term506 x0 y0 x y) = (term507 x0 y y0).
Proof. exact (MK_COMB (@lem1549714) (@lem1549713 x x0 y y0)). Qed.
Lemma lem1549716 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549717 (x : real) (x0 : real) (y : real) (y0 : real) : (term499 x0 y0 x y) = (term508 x0 y y0).
Proof. exact (MK_COMB (@lem1549715 x x0 y y0) (@lem1549716)). Qed.
Lemma lem1549718 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term508 x0 y y0.
Proof. exact (EQ_MP (@lem1549717 x x0 y y0) (@lem1549690 x0 y0 x y h1)). Qed.
Lemma lem1549720 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549721 : term453 = term454.
Proof. exact (@lem1549720 (NUMERAL 0) term66). Qed.
Lemma lem1549722 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549723 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549724 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549723 h1) (fun h1 : term454 = True => @lem1549722)). Qed.
Lemma lem1549725 : term454 = True.
Proof. exact (EQ_MP (@lem1549724) (@lem1549722)). Qed.
Lemma lem1549726 : term453 = True.
Proof. exact (TRANS (@lem1549721) (@lem1549725)). Qed.
Lemma lem1549727 : True = term453.
Proof. exact (SYM (@lem1549726)). Qed.
Lemma lem1549728 : term453.
Proof. exact (EQ_MP (@lem1549727) (@lem0)). Qed.
Lemma lem1549729 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term509 x0 y y0.
Proof. exact (conj (@lem1549728) (@lem1549718 x0 y0 x y h1)). Qed.
Lemma lem1549731 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549732 (x0 : real) (y : real) (y0 : real) : term510 x0 y y0.
Proof. exact (@lem1549731 term181 (term504 x0 y y0)). Qed.
Lemma lem1549733 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term511 x0 y y0.
Proof. exact (@lem1549732 x0 y y0 (@lem1549729 x0 y0 x y h1)). Qed.
Lemma lem1549734 (x0 : real) (y : real) (y0 : real) : (term512 x0 y y0) = (term504 x0 y y0).
Proof. exact (@lem1483460 (term504 x0 y y0)). Qed.
Lemma lem1549735 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549736 (x0 : real) (y : real) (y0 : real) : (term513 x0 y y0) = (term507 x0 y y0).
Proof. exact (MK_COMB (@lem1549735) (@lem1549734 x0 y y0)). Qed.
Lemma lem1549737 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549738 (x0 : real) (y : real) (y0 : real) : (term511 x0 y y0) = (term508 x0 y y0).
Proof. exact (MK_COMB (@lem1549736 x0 y y0) (@lem1549737)). Qed.
Lemma lem1549739 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term508 x0 y y0.
Proof. exact (EQ_MP (@lem1549738 x0 y y0) (@lem1549733 x0 y0 x y h1)). Qed.
Lemma lem1549740 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term514 x0 y y0.
Proof. exact (conj (@lem1549739 x0 y0 x y h1) (@lem1549621 x0 y0 x y h1)). Qed.
Lemma lem1549742 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1549743 (x0 : real) (y : real) (y0 : real) : term515 x0 y y0.
Proof. exact (@lem1549742 (term504 x0 y y0) (term249 y y0)). Qed.
Lemma lem1549744 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term516 x0 y y0.
Proof. exact (@lem1549743 x0 y y0 (@lem1549740 x0 y0 x y h1)). Qed.
Lemma lem1549745 (x0 : real) (y : real) (y0 : real) : (term517 x0 y y0) = (term518 x0 y y0).
Proof. exact (@lem1483482 x0 (term254 y y0) (term249 y y0)). Qed.
Lemma lem1549746 (y : real) (y0 : real) : (term519 y y0) = (term520 y y0).
Proof. exact (@lem1483480 (term169 y) (term163 y) y0 (term169 y0)). Qed.
Lemma lem1549747 (y : real) : (term470 y) = (term471 y).
Proof. exact (@lem1483438 term72 term60 y). Qed.
Lemma lem1549749 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1549750 : term473 = term47.
Proof. exact (@lem1549749 term67). Qed.
Lemma lem1549751 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549752 : term474 = term475.
Proof. exact (MK_COMB (@lem1549751) (@lem1549750)). Qed.
Lemma lem1549753 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549754 (y : real) : (term471 y) = (term476 y).
Proof. exact (MK_COMB (@lem1549752) (@lem1549753 y)). Qed.
Lemma lem1549755 (y : real) : (term470 y) = (term476 y).
Proof. exact (TRANS (@lem1549747 y) (@lem1549754 y)). Qed.
Lemma lem1549756 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1549757 (y : real) : (term470 y) = term47.
Proof. exact (TRANS (@lem1549755 y) (@lem1549756 y)). Qed.
Lemma lem1549758 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549759 (y : real) : (term477 y) = term236.
Proof. exact (MK_COMB (@lem1549758) (@lem1549757 y)). Qed.
Lemma lem1549760 (y0 : real) : (term360 y0) = (term361 y0).
Proof. exact (@lem1483442 term72 y0). Qed.
Lemma lem1549763 : term362 = term59.
Proof. exact (@lem1367767 term66 term66). Qed.
Lemma lem1549764 : term182 = term69.
Proof. exact (@lem706885). Qed.
Lemma lem1549765 : (term182 = term69) = (term183 = term67).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term69). Qed.
Lemma lem1549766 : term183 = term67.
Proof. exact (EQ_MP (@lem1549765) (@lem1549764)). Qed.
Lemma lem1549767 : term67 = term183.
Proof. exact (SYM (@lem1549766)). Qed.
Lemma lem1549768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549769 : term60 = term184.
Proof. exact (MK_COMB (@lem1549768) (@lem1549767)). Qed.
Lemma lem1549770 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549771 : term72 = term363.
Proof. exact (MK_COMB (@lem1549770) (@lem1549769)). Qed.
Lemma lem1549772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549773 : term364 = term365.
Proof. exact (MK_COMB (@lem1549772) (@lem1549771)). Qed.
Lemma lem1549774 : term181 = term181.
Proof. exact (eq_refl term181). Qed.
Lemma lem1549775 : term366 = term362.
Proof. exact (MK_COMB (@lem1549773) (@lem1549774)). Qed.
Lemma lem1549776 : term366 = term59.
Proof. exact (TRANS (@lem1549775) (@lem1549763)). Qed.
Lemma lem1549777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549778 : term367 = term368.
Proof. exact (MK_COMB (@lem1549777) (@lem1549776)). Qed.
Lemma lem1549779 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549780 (y0 : real) : (term361 y0) = (term44 y0).
Proof. exact (MK_COMB (@lem1549778) (@lem1549779 y0)). Qed.
Lemma lem1549781 (y0 : real) : (term360 y0) = (term44 y0).
Proof. exact (TRANS (@lem1549760 y0) (@lem1549780 y0)). Qed.
Lemma lem1549782 (y : real) (y0 : real) : (term520 y y0) = (term521 y0).
Proof. exact (MK_COMB (@lem1549759 y) (@lem1549781 y0)). Qed.
Lemma lem1549783 (y : real) (y0 : real) : (term519 y y0) = (term521 y0).
Proof. exact (TRANS (@lem1549746 y y0) (@lem1549782 y y0)). Qed.
Lemma lem1549784 (y0 : real) : (term521 y0) = (term44 y0).
Proof. exact (@lem1483448 (term44 y0)). Qed.
Lemma lem1549785 (y : real) (y0 : real) : (term519 y y0) = (term44 y0).
Proof. exact (TRANS (@lem1549783 y y0) (@lem1549784 y0)). Qed.
Lemma lem1549786 (x0 : real) : (real_add x0) = (real_add x0).
Proof. exact (eq_refl (real_add x0)). Qed.
Lemma lem1549787 (y : real) (x0 : real) (y0 : real) : (term518 x0 y y0) = (term42 x0 y0).
Proof. exact (MK_COMB (@lem1549786 x0) (@lem1549785 y y0)). Qed.
Lemma lem1549788 (y : real) (x0 : real) (y0 : real) : (term517 x0 y y0) = (term42 x0 y0).
Proof. exact (TRANS (@lem1549745 x0 y y0) (@lem1549787 y x0 y0)). Qed.
Lemma lem1549789 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549790 (y : real) (x0 : real) (y0 : real) : (term522 x0 y y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1549789) (@lem1549788 y x0 y0)). Qed.
Lemma lem1549791 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549792 (y : real) (x0 : real) (y0 : real) : (term516 x0 y y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1549790 y x0 y0) (@lem1549791)). Qed.
Lemma lem1549793 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1549792 y x0 y0) (@lem1549744 x0 y0 x y h1)). Qed.
Lemma lem1549795 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549796 : term453 = term454.
Proof. exact (@lem1549795 (NUMERAL 0) term66). Qed.
Lemma lem1549797 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549798 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549799 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549798 h1) (fun h1 : term454 = True => @lem1549797)). Qed.
Lemma lem1549800 : term454 = True.
Proof. exact (EQ_MP (@lem1549799) (@lem1549797)). Qed.
Lemma lem1549801 : term453 = True.
Proof. exact (TRANS (@lem1549796) (@lem1549800)). Qed.
Lemma lem1549802 : True = term453.
Proof. exact (SYM (@lem1549801)). Qed.
Lemma lem1549803 : term453.
Proof. exact (EQ_MP (@lem1549802) (@lem0)). Qed.
Lemma lem1549804 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term525 x0 y0.
Proof. exact (conj (@lem1549803) (@lem1549793 x0 y0 x y h1)). Qed.
Lemma lem1549806 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549807 (x0 : real) (y0 : real) : term526 x0 y0.
Proof. exact (@lem1549806 term181 (term42 x0 y0)). Qed.
Lemma lem1549808 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term527 x0 y0.
Proof. exact (@lem1549807 x0 y0 (@lem1549804 x0 y0 x y h1)). Qed.
Lemma lem1549809 (x0 : real) (y0 : real) : (term528 x0 y0) = (term42 x0 y0).
Proof. exact (@lem1483460 (term42 x0 y0)). Qed.
Lemma lem1549810 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549811 (x0 : real) (y0 : real) : (term529 x0 y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1549810) (@lem1549809 x0 y0)). Qed.
Lemma lem1549812 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549813 (x0 : real) (y0 : real) : (term527 x0 y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1549811 x0 y0) (@lem1549812)). Qed.
Lemma lem1549814 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1549813 x0 y0) (@lem1549808 x0 y0 x y h1)). Qed.
Lemma lem1549815 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term530 x0 y0.
Proof. exact (conj (@lem1549814 x0 y0 x y h1) (@lem1549578 x0 y0 x y h1)). Qed.
Lemma lem1549817 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1549818 (x0 : real) (y0 : real) : term532 x0 y0.
Proof. exact (@lem1549817 (term42 x0 y0) (term43 x0 y0)). Qed.
Lemma lem1549819 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term533 x0 y0.
Proof. exact (@lem1549818 x0 y0 (@lem1549815 x0 y0 x y h1)). Qed.
Lemma lem1549820 (x0 : real) (y0 : real) : (term534 x0 y0) = (term535 x0 y0).
Proof. exact (@lem1483480 x0 (term44 x0) (term44 y0) y0). Qed.
Lemma lem1549821 (x0 : real) : (term536 x0) = (term537 x0).
Proof. exact (@lem1483442 term59 x0). Qed.
Lemma lem1549823 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1549824 : term538 = term47.
Proof. exact (@lem1549823 term66). Qed.
Lemma lem1549825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549826 : term539 = term475.
Proof. exact (MK_COMB (@lem1549825) (@lem1549824)). Qed.
Lemma lem1549827 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1549828 (x0 : real) : (term537 x0) = (term476 x0).
Proof. exact (MK_COMB (@lem1549826) (@lem1549827 x0)). Qed.
Lemma lem1549829 (x0 : real) : (term536 x0) = (term476 x0).
Proof. exact (TRANS (@lem1549821 x0) (@lem1549828 x0)). Qed.
Lemma lem1549830 (x0 : real) : (term476 x0) = term47.
Proof. exact (@lem1483446 x0). Qed.
Lemma lem1549831 (x0 : real) : (term536 x0) = term47.
Proof. exact (TRANS (@lem1549829 x0) (@lem1549830 x0)). Qed.
Lemma lem1549832 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549833 (x0 : real) : (term540 x0) = term236.
Proof. exact (MK_COMB (@lem1549832) (@lem1549831 x0)). Qed.
Lemma lem1549834 (y0 : real) : (term541 y0) = (term537 y0).
Proof. exact (@lem1483440 term59 y0). Qed.
Lemma lem1549836 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1549837 : term538 = term47.
Proof. exact (@lem1549836 term66). Qed.
Lemma lem1549838 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549839 : term539 = term475.
Proof. exact (MK_COMB (@lem1549838) (@lem1549837)). Qed.
Lemma lem1549840 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1549841 (y0 : real) : (term537 y0) = (term476 y0).
Proof. exact (MK_COMB (@lem1549839) (@lem1549840 y0)). Qed.
Lemma lem1549842 (y0 : real) : (term541 y0) = (term476 y0).
Proof. exact (TRANS (@lem1549834 y0) (@lem1549841 y0)). Qed.
Lemma lem1549843 (y0 : real) : (term476 y0) = term47.
Proof. exact (@lem1483446 y0). Qed.
Lemma lem1549844 (y0 : real) : (term541 y0) = term47.
Proof. exact (TRANS (@lem1549842 y0) (@lem1549843 y0)). Qed.
Lemma lem1549845 (x0 : real) (y0 : real) : (term535 x0 y0) = term542.
Proof. exact (MK_COMB (@lem1549833 x0) (@lem1549844 y0)). Qed.
Lemma lem1549846 (x0 : real) (y0 : real) : (term534 x0 y0) = term542.
Proof. exact (TRANS (@lem1549820 x0 y0) (@lem1549845 x0 y0)). Qed.
Lemma lem1549847 : term542 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1549848 (x0 : real) (y0 : real) : (term534 x0 y0) = term47.
Proof. exact (TRANS (@lem1549846 x0 y0) (@lem1549847)). Qed.
Lemma lem1549849 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549850 (x0 : real) (y0 : real) : (term543 x0 y0) = term544.
Proof. exact (MK_COMB (@lem1549849) (@lem1549848 x0 y0)). Qed.
Lemma lem1549851 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549852 (x0 : real) (y0 : real) : (term533 x0 y0) = term545.
Proof. exact (MK_COMB (@lem1549850 x0 y0) (@lem1549851)). Qed.
Lemma lem1549853 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : term545.
Proof. exact (EQ_MP (@lem1549852 x0 y0) (@lem1549819 x0 y0 x y h1)). Qed.
Lemma lem1549855 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549856 : term545 = term546.
Proof. exact (@lem1549855 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1549857 : term546 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1549858 : term545 = False.
Proof. exact (TRANS (@lem1549856) (@lem1549857)). Qed.
Lemma lem1549859 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term419 x0 y0 x y) : False.
Proof. exact (EQ_MP (@lem1549858) (@lem1549853 x0 y0 x y h1)). Qed.
Lemma lem1549860 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term429 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1549861 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term428 x0 y0 x y.
Proof. exact (proj2 (@lem1549860 x0 y0 x y h1)). Qed.
Lemma lem1549863 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term427 x0 y0 x y.
Proof. exact (proj2 (@lem1549861 x0 y0 x y h1)). Qed.
Lemma lem1549865 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term103 x y.
Proof. exact (proj2 (@lem1549863 x0 y0 x y h1)). Qed.
Lemma lem1549866 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term423 x x0 y y0.
Proof. exact (proj1 (@lem1549863 x0 y0 x y h1)). Qed.
Lemma lem1549867 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term421 x x0 y y0.
Proof. exact (proj2 (@lem1549866 x0 y0 x y h1)). Qed.
Lemma lem1549869 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term380 x0 y y0.
Proof. exact (proj2 (@lem1549867 x0 y0 x y h1)). Qed.
Lemma lem1549870 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term201 x x0 y0.
Proof. exact (proj1 (@lem1549867 x0 y0 x y h1)). Qed.
Lemma lem1549872 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549873 : term435 = term436.
Proof. exact (@lem1549872 (NUMERAL 0) term67). Qed.
Lemma lem1549874 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1549875 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1549876 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1549875 h1) (fun h1 : term436 = True => @lem1549874)). Qed.
Lemma lem1549877 : term436 = True.
Proof. exact (EQ_MP (@lem1549876) (@lem1549874)). Qed.
Lemma lem1549878 : term435 = True.
Proof. exact (TRANS (@lem1549873) (@lem1549877)). Qed.
Lemma lem1549879 : True = term435.
Proof. exact (SYM (@lem1549878)). Qed.
Lemma lem1549880 : term435.
Proof. exact (EQ_MP (@lem1549879) (@lem0)). Qed.
Lemma lem1549881 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term438 x y.
Proof. exact (conj (@lem1549880) (@lem1549865 x0 y0 x y h1)). Qed.
Lemma lem1549883 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1549884 (x : real) (y : real) : term440 x y.
Proof. exact (@lem1549883 term60 (term42 x y)). Qed.
Lemma lem1549885 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term441 x y.
Proof. exact (@lem1549884 x y (@lem1549881 x0 y0 x y h1)). Qed.
Lemma lem1549886 (x : real) (y : real) : (term442 x y) = (term443 x y).
Proof. exact (@lem1483508 x term60 (term44 y)). Qed.
Lemma lem1549887 (y : real) : (term444 y) = (term445 y).
Proof. exact (@lem1483476 term60 term59 y). Qed.
Lemma lem1549889 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1549890 : term447 = term448.
Proof. exact (@lem1549889 term67 term66). Qed.
Lemma lem1549891 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549892 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549893 : term160 = term67.
Proof. exact (EQ_MP (@lem1549892) (@lem1549891)). Qed.
Lemma lem1549894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549895 : term158 = term60.
Proof. exact (MK_COMB (@lem1549894) (@lem1549893)). Qed.
Lemma lem1549896 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549897 : term448 = term72.
Proof. exact (MK_COMB (@lem1549896) (@lem1549895)). Qed.
Lemma lem1549898 : term447 = term72.
Proof. exact (TRANS (@lem1549890) (@lem1549897)). Qed.
Lemma lem1549899 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549900 : term449 = term74.
Proof. exact (MK_COMB (@lem1549899) (@lem1549898)). Qed.
Lemma lem1549901 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549902 (y : real) : (term445 y) = (term169 y).
Proof. exact (MK_COMB (@lem1549900) (@lem1549901 y)). Qed.
Lemma lem1549903 (y : real) : (term444 y) = (term169 y).
Proof. exact (TRANS (@lem1549887 y) (@lem1549902 y)). Qed.
Lemma lem1549906 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1549907 (x : real) (y : real) : (term443 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1549906 x) (@lem1549903 y)). Qed.
Lemma lem1549908 (x : real) (y : real) : (term442 x y) = (term249 x y).
Proof. exact (TRANS (@lem1549886 x y) (@lem1549907 x y)). Qed.
Lemma lem1549909 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1549910 (x : real) (y : real) : (term450 x y) = (term451 x y).
Proof. exact (MK_COMB (@lem1549909) (@lem1549908 x y)). Qed.
Lemma lem1549911 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549912 (x : real) (y : real) : (term441 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1549910 x y) (@lem1549911)). Qed.
Lemma lem1549913 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term452 x y.
Proof. exact (EQ_MP (@lem1549912 x y) (@lem1549885 x0 y0 x y h1)). Qed.
Lemma lem1549915 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549916 : term453 = term454.
Proof. exact (@lem1549915 (NUMERAL 0) term66). Qed.
Lemma lem1549917 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1549918 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1549919 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1549918 h1) (fun h1 : term454 = True => @lem1549917)). Qed.
Lemma lem1549920 : term454 = True.
Proof. exact (EQ_MP (@lem1549919) (@lem1549917)). Qed.
Lemma lem1549921 : term453 = True.
Proof. exact (TRANS (@lem1549916) (@lem1549920)). Qed.
Lemma lem1549922 : True = term453.
Proof. exact (SYM (@lem1549921)). Qed.
Lemma lem1549923 : term453.
Proof. exact (EQ_MP (@lem1549922) (@lem0)). Qed.
Lemma lem1549924 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term547 x0 y y0.
Proof. exact (conj (@lem1549923) (@lem1549869 x0 y0 x y h1)). Qed.
Lemma lem1549926 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549927 (x0 : real) (y : real) (y0 : real) : term548 x0 y y0.
Proof. exact (@lem1549926 term181 (term370 x0 y y0)). Qed.
Lemma lem1549928 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term549 x0 y y0.
Proof. exact (@lem1549927 x0 y y0 (@lem1549924 x0 y0 x y h1)). Qed.
Lemma lem1549929 (x0 : real) (y : real) (y0 : real) : (term550 x0 y y0) = (term370 x0 y y0).
Proof. exact (@lem1483460 (term370 x0 y y0)). Qed.
Lemma lem1549930 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549931 (x0 : real) (y : real) (y0 : real) : (term551 x0 y y0) = (term379 x0 y y0).
Proof. exact (MK_COMB (@lem1549930) (@lem1549929 x0 y y0)). Qed.
Lemma lem1549932 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549933 (x0 : real) (y : real) (y0 : real) : (term549 x0 y y0) = (term380 x0 y y0).
Proof. exact (MK_COMB (@lem1549931 x0 y y0) (@lem1549932)). Qed.
Lemma lem1549934 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term380 x0 y y0.
Proof. exact (EQ_MP (@lem1549933 x0 y y0) (@lem1549928 x0 y0 x y h1)). Qed.
Lemma lem1549935 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term552 x0 y0 x y.
Proof. exact (conj (@lem1549934 x0 y0 x y h1) (@lem1549913 x0 y0 x y h1)). Qed.
Lemma lem1549937 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1549938 (x0 : real) (y0 : real) (x : real) (y : real) : term553 x0 y0 x y.
Proof. exact (@lem1549937 (term370 x0 y y0) (term249 x y)). Qed.
Lemma lem1549939 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term554 x0 y0 x y.
Proof. exact (@lem1549938 x0 y0 x y (@lem1549935 x0 y0 x y h1)). Qed.
Lemma lem1549940 (x : real) (x0 : real) (y0 : real) (y : real) : (term555 x0 y0 x y) = (term556 x x0 y0 y).
Proof. exact (@lem1483484 (term163 x) (term370 x0 y y0) (term169 y)). Qed.
Lemma lem1549941 (x0 : real) (y0 : real) (y : real) : (term557 x0 y0 y) = (term558 x0 y0 y).
Proof. exact (@lem1483482 (term44 x0) (term369 y y0) (term169 y)). Qed.
Lemma lem1549942 (y : real) (y0 : real) : (term559 y0 y) = (term560 y y0).
Proof. exact (@lem1483486 (term163 y) (term169 y) (term44 y0)). Qed.
Lemma lem1549943 (y : real) : (term561 y) = (term562 y).
Proof. exact (@lem1483438 term60 term72 y). Qed.
Lemma lem1549945 (m : nat) : (term563 m) = term47.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1549946 : term564 = term47.
Proof. exact (@lem1549945 term67). Qed.
Lemma lem1549947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1549948 : term565 = term475.
Proof. exact (MK_COMB (@lem1549947) (@lem1549946)). Qed.
Lemma lem1549949 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1549950 (y : real) : (term562 y) = (term476 y).
Proof. exact (MK_COMB (@lem1549948) (@lem1549949 y)). Qed.
Lemma lem1549951 (y : real) : (term561 y) = (term476 y).
Proof. exact (TRANS (@lem1549943 y) (@lem1549950 y)). Qed.
Lemma lem1549952 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1549953 (y : real) : (term561 y) = term47.
Proof. exact (TRANS (@lem1549951 y) (@lem1549952 y)). Qed.
Lemma lem1549954 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1549955 (y : real) : (term566 y) = term236.
Proof. exact (MK_COMB (@lem1549954) (@lem1549953 y)). Qed.
Lemma lem1549956 (y0 : real) : (term44 y0) = (term44 y0).
Proof. exact (eq_refl (term44 y0)). Qed.
Lemma lem1549957 (y : real) (y0 : real) : (term560 y y0) = (term521 y0).
Proof. exact (MK_COMB (@lem1549955 y) (@lem1549956 y0)). Qed.
Lemma lem1549958 (y : real) (y0 : real) : (term559 y0 y) = (term521 y0).
Proof. exact (TRANS (@lem1549942 y y0) (@lem1549957 y y0)). Qed.
Lemma lem1549959 (y0 : real) : (term521 y0) = (term44 y0).
Proof. exact (@lem1483448 (term44 y0)). Qed.
Lemma lem1549960 (y : real) (y0 : real) : (term559 y0 y) = (term44 y0).
Proof. exact (TRANS (@lem1549958 y y0) (@lem1549959 y0)). Qed.
Lemma lem1549961 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1549962 (y : real) (x0 : real) (y0 : real) : (term558 x0 y0 y) = (term567 x0 y0).
Proof. exact (MK_COMB (@lem1549961 x0) (@lem1549960 y y0)). Qed.
Lemma lem1549963 (y : real) (x0 : real) (y0 : real) : (term557 x0 y0 y) = (term567 x0 y0).
Proof. exact (TRANS (@lem1549941 x0 y0 y) (@lem1549962 y x0 y0)). Qed.
Lemma lem1549964 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1549965 (y : real) (x : real) (x0 : real) (y0 : real) : (term556 x x0 y0 y) = (term568 x x0 y0).
Proof. exact (MK_COMB (@lem1549964 x) (@lem1549963 y x0 y0)). Qed.
Lemma lem1549966 (y : real) (x : real) (x0 : real) (y0 : real) : (term555 x0 y0 x y) = (term568 x x0 y0).
Proof. exact (TRANS (@lem1549940 x x0 y0 y) (@lem1549965 y x x0 y0)). Qed.
Lemma lem1549967 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1549968 (y : real) (x : real) (x0 : real) (y0 : real) : (term569 x0 y0 x y) = (term570 x x0 y0).
Proof. exact (MK_COMB (@lem1549967) (@lem1549966 y x x0 y0)). Qed.
Lemma lem1549969 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1549970 (y : real) (x : real) (x0 : real) (y0 : real) : (term554 x0 y0 x y) = (term571 x x0 y0).
Proof. exact (MK_COMB (@lem1549968 y x x0 y0) (@lem1549969)). Qed.
Lemma lem1549971 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term571 x x0 y0.
Proof. exact (EQ_MP (@lem1549970 y x x0 y0) (@lem1549939 x0 y0 x y h1)). Qed.
Lemma lem1549973 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1549974 : term435 = term436.
Proof. exact (@lem1549973 (NUMERAL 0) term67). Qed.
Lemma lem1549975 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1549976 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1549977 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1549976 h1) (fun h1 : term436 = True => @lem1549975)). Qed.
Lemma lem1549978 : term436 = True.
Proof. exact (EQ_MP (@lem1549977) (@lem1549975)). Qed.
Lemma lem1549979 : term435 = True.
Proof. exact (TRANS (@lem1549974) (@lem1549978)). Qed.
Lemma lem1549980 : True = term435.
Proof. exact (SYM (@lem1549979)). Qed.
Lemma lem1549981 : term435.
Proof. exact (EQ_MP (@lem1549980) (@lem0)). Qed.
Lemma lem1549982 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term572 x x0 y0.
Proof. exact (conj (@lem1549981) (@lem1549971 x0 y0 x y h1)). Qed.
Lemma lem1549984 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1549985 (x : real) (x0 : real) (y0 : real) : term573 x x0 y0.
Proof. exact (@lem1549984 term60 (term568 x x0 y0)). Qed.
Lemma lem1549986 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term574 x x0 y0.
Proof. exact (@lem1549985 x x0 y0 (@lem1549982 x0 y0 x y h1)). Qed.
Lemma lem1549987 (x : real) (x0 : real) (y0 : real) : (term575 x x0 y0) = (term576 x x0 y0).
Proof. exact (@lem1483508 (term163 x) term60 (term567 x0 y0)). Qed.
Lemma lem1549988 (x0 : real) (y0 : real) : (term577 x0 y0) = (term578 x0 y0).
Proof. exact (@lem1483508 (term44 x0) term60 (term44 y0)). Qed.
Lemma lem1549989 (y0 : real) : (term444 y0) = (term445 y0).
Proof. exact (@lem1483476 term60 term59 y0). Qed.
Lemma lem1549991 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1549992 : term447 = term448.
Proof. exact (@lem1549991 term67 term66). Qed.
Lemma lem1549993 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1549994 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1549995 : term160 = term67.
Proof. exact (EQ_MP (@lem1549994) (@lem1549993)). Qed.
Lemma lem1549996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1549997 : term158 = term60.
Proof. exact (MK_COMB (@lem1549996) (@lem1549995)). Qed.
Lemma lem1549998 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1549999 : term448 = term72.
Proof. exact (MK_COMB (@lem1549998) (@lem1549997)). Qed.
Lemma lem1550000 : term447 = term72.
Proof. exact (TRANS (@lem1549992) (@lem1549999)). Qed.
Lemma lem1550001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550002 : term449 = term74.
Proof. exact (MK_COMB (@lem1550001) (@lem1550000)). Qed.
Lemma lem1550003 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550004 (y0 : real) : (term445 y0) = (term169 y0).
Proof. exact (MK_COMB (@lem1550002) (@lem1550003 y0)). Qed.
Lemma lem1550005 (y0 : real) : (term444 y0) = (term169 y0).
Proof. exact (TRANS (@lem1549989 y0) (@lem1550004 y0)). Qed.
Lemma lem1550006 (x0 : real) : (term444 x0) = (term445 x0).
Proof. exact (@lem1483476 term60 term59 x0). Qed.
Lemma lem1550008 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550009 : term447 = term448.
Proof. exact (@lem1550008 term67 term66). Qed.
Lemma lem1550010 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1550011 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1550012 : term160 = term67.
Proof. exact (EQ_MP (@lem1550011) (@lem1550010)). Qed.
Lemma lem1550013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550014 : term158 = term60.
Proof. exact (MK_COMB (@lem1550013) (@lem1550012)). Qed.
Lemma lem1550015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550016 : term448 = term72.
Proof. exact (MK_COMB (@lem1550015) (@lem1550014)). Qed.
Lemma lem1550017 : term447 = term72.
Proof. exact (TRANS (@lem1550009) (@lem1550016)). Qed.
Lemma lem1550018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550019 : term449 = term74.
Proof. exact (MK_COMB (@lem1550018) (@lem1550017)). Qed.
Lemma lem1550020 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550021 (x0 : real) : (term445 x0) = (term169 x0).
Proof. exact (MK_COMB (@lem1550019) (@lem1550020 x0)). Qed.
Lemma lem1550022 (x0 : real) : (term444 x0) = (term169 x0).
Proof. exact (TRANS (@lem1550006 x0) (@lem1550021 x0)). Qed.
Lemma lem1550023 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550024 (x0 : real) : (term579 x0) = (term164 x0).
Proof. exact (MK_COMB (@lem1550023) (@lem1550022 x0)). Qed.
Lemma lem1550025 (x0 : real) (y0 : real) : (term578 x0 y0) = (term580 x0 y0).
Proof. exact (MK_COMB (@lem1550024 x0) (@lem1550005 y0)). Qed.
Lemma lem1550026 (x0 : real) (y0 : real) : (term577 x0 y0) = (term580 x0 y0).
Proof. exact (TRANS (@lem1549988 x0 y0) (@lem1550025 x0 y0)). Qed.
Lemma lem1550027 (x : real) : (term581 x) = (term582 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1550029 (m : nat) (n : nat) : (term583 m n) = (term156 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1550030 : term584 = term585.
Proof. exact (@lem1550029 term67 term67). Qed.
Lemma lem1550031 : (term233 = (BIT1 0)) = (term586 = term587).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1550032 : term586 = term587.
Proof. exact (EQ_MP (@lem1550031) (@lem940073)). Qed.
Lemma lem1550033 : (term586 = term587) = (term588 = term589).
Proof. exact (@lem1008952 term69 term587). Qed.
Lemma lem1550034 : term588 = term589.
Proof. exact (EQ_MP (@lem1550033) (@lem1550032)). Qed.
Lemma lem1550035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550036 : term585 = term590.
Proof. exact (MK_COMB (@lem1550035) (@lem1550034)). Qed.
Lemma lem1550037 : term584 = term590.
Proof. exact (TRANS (@lem1550030) (@lem1550036)). Qed.
Lemma lem1550038 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550039 : term591 = term592.
Proof. exact (MK_COMB (@lem1550038) (@lem1550037)). Qed.
Lemma lem1550040 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550041 (x : real) : (term582 x) = (term593 x).
Proof. exact (MK_COMB (@lem1550039) (@lem1550040 x)). Qed.
Lemma lem1550042 (x : real) : (term581 x) = (term593 x).
Proof. exact (TRANS (@lem1550027 x) (@lem1550041 x)). Qed.
Lemma lem1550043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550044 (x : real) : (term594 x) = (term595 x).
Proof. exact (MK_COMB (@lem1550043) (@lem1550042 x)). Qed.
Lemma lem1550045 (x : real) (x0 : real) (y0 : real) : (term576 x x0 y0) = (term596 x x0 y0).
Proof. exact (MK_COMB (@lem1550044 x) (@lem1550026 x0 y0)). Qed.
Lemma lem1550046 (x : real) (x0 : real) (y0 : real) : (term575 x x0 y0) = (term596 x x0 y0).
Proof. exact (TRANS (@lem1549987 x x0 y0) (@lem1550045 x x0 y0)). Qed.
Lemma lem1550047 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550048 (x : real) (x0 : real) (y0 : real) : (term597 x x0 y0) = (term598 x x0 y0).
Proof. exact (MK_COMB (@lem1550047) (@lem1550046 x x0 y0)). Qed.
Lemma lem1550049 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550050 (x : real) (x0 : real) (y0 : real) : (term574 x x0 y0) = (term599 x x0 y0).
Proof. exact (MK_COMB (@lem1550048 x x0 y0) (@lem1550049)). Qed.
Lemma lem1550051 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term599 x x0 y0.
Proof. exact (EQ_MP (@lem1550050 x x0 y0) (@lem1549986 x0 y0 x y h1)). Qed.
Lemma lem1550053 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550054 : term435 = term436.
Proof. exact (@lem1550053 (NUMERAL 0) term67). Qed.
Lemma lem1550055 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1550056 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1550057 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1550056 h1) (fun h1 : term436 = True => @lem1550055)). Qed.
Lemma lem1550058 : term436 = True.
Proof. exact (EQ_MP (@lem1550057) (@lem1550055)). Qed.
Lemma lem1550059 : term435 = True.
Proof. exact (TRANS (@lem1550054) (@lem1550058)). Qed.
Lemma lem1550060 : True = term435.
Proof. exact (SYM (@lem1550059)). Qed.
Lemma lem1550061 : term435.
Proof. exact (EQ_MP (@lem1550060) (@lem0)). Qed.
Lemma lem1550062 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term600 x x0 y0.
Proof. exact (conj (@lem1550061) (@lem1549870 x0 y0 x y h1)). Qed.
Lemma lem1550064 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550065 (x : real) (x0 : real) (y0 : real) : term601 x x0 y0.
Proof. exact (@lem1550064 term60 (term191 x x0 y0)). Qed.
Lemma lem1550066 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term602 x x0 y0.
Proof. exact (@lem1550065 x x0 y0 (@lem1550062 x0 y0 x y h1)). Qed.
Lemma lem1550067 (x : real) (x0 : real) (y0 : real) : (term603 x x0 y0) = (term604 x x0 y0).
Proof. exact (@lem1483508 (term169 x) term60 (real_add x0 y0)). Qed.
Lemma lem1550074 (x0 : real) (y0 : real) : (term605 x0 y0) = (term606 x0 y0).
Proof. exact (@lem1483508 x0 term60 y0). Qed.
Lemma lem1550075 (x : real) : (term607 x) = (term608 x).
Proof. exact (@lem1483476 term60 term72 x). Qed.
Lemma lem1550077 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550078 : term609 = term610.
Proof. exact (@lem1550077 term67 term67). Qed.
Lemma lem1550079 : (term233 = (BIT1 0)) = (term586 = term587).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1550080 : term586 = term587.
Proof. exact (EQ_MP (@lem1550079) (@lem940073)). Qed.
Lemma lem1550081 : (term586 = term587) = (term588 = term589).
Proof. exact (@lem1008952 term69 term587). Qed.
Lemma lem1550082 : term588 = term589.
Proof. exact (EQ_MP (@lem1550081) (@lem1550080)). Qed.
Lemma lem1550083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550084 : term585 = term590.
Proof. exact (MK_COMB (@lem1550083) (@lem1550082)). Qed.
Lemma lem1550085 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550086 : term610 = term611.
Proof. exact (MK_COMB (@lem1550085) (@lem1550084)). Qed.
Lemma lem1550087 : term609 = term611.
Proof. exact (TRANS (@lem1550078) (@lem1550086)). Qed.
Lemma lem1550088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550089 : term612 = term613.
Proof. exact (MK_COMB (@lem1550088) (@lem1550087)). Qed.
Lemma lem1550090 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550091 (x : real) : (term608 x) = (term614 x).
Proof. exact (MK_COMB (@lem1550089) (@lem1550090 x)). Qed.
Lemma lem1550092 (x : real) : (term607 x) = (term614 x).
Proof. exact (TRANS (@lem1550075 x) (@lem1550091 x)). Qed.
Lemma lem1550093 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550094 (x : real) : (term615 x) = (term616 x).
Proof. exact (MK_COMB (@lem1550093) (@lem1550092 x)). Qed.
Lemma lem1550095 (x : real) (x0 : real) (y0 : real) : (term604 x x0 y0) = (term617 x x0 y0).
Proof. exact (MK_COMB (@lem1550094 x) (@lem1550074 x0 y0)). Qed.
Lemma lem1550096 (x : real) (x0 : real) (y0 : real) : (term603 x x0 y0) = (term617 x x0 y0).
Proof. exact (TRANS (@lem1550067 x x0 y0) (@lem1550095 x x0 y0)). Qed.
Lemma lem1550097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550098 (x : real) (x0 : real) (y0 : real) : (term618 x x0 y0) = (term619 x x0 y0).
Proof. exact (MK_COMB (@lem1550097) (@lem1550096 x x0 y0)). Qed.
Lemma lem1550099 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550100 (x : real) (x0 : real) (y0 : real) : (term602 x x0 y0) = (term620 x x0 y0).
Proof. exact (MK_COMB (@lem1550098 x x0 y0) (@lem1550099)). Qed.
Lemma lem1550101 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term620 x x0 y0.
Proof. exact (EQ_MP (@lem1550100 x x0 y0) (@lem1550066 x0 y0 x y h1)). Qed.
Lemma lem1550102 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term621 x x0 y0.
Proof. exact (conj (@lem1550101 x0 y0 x y h1) (@lem1550051 x0 y0 x y h1)). Qed.
Lemma lem1550104 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1550105 (x : real) (x0 : real) (y0 : real) : term622 x x0 y0.
Proof. exact (@lem1550104 (term617 x x0 y0) (term596 x x0 y0)). Qed.
Lemma lem1550106 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term623 x x0 y0.
Proof. exact (@lem1550105 x x0 y0 (@lem1550102 x0 y0 x y h1)). Qed.
Lemma lem1550107 (x : real) (x0 : real) (y0 : real) : (term624 x x0 y0) = (term625 x x0 y0).
Proof. exact (@lem1483480 (term614 x) (term593 x) (term606 x0 y0) (term580 x0 y0)). Qed.
Lemma lem1550108 (x : real) : (term626 x) = (term627 x).
Proof. exact (@lem1483438 term611 term590 x). Qed.
Lemma lem1550110 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550111 : term628 = term47.
Proof. exact (@lem1550110 term589). Qed.
Lemma lem1550112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550113 : term629 = term475.
Proof. exact (MK_COMB (@lem1550112) (@lem1550111)). Qed.
Lemma lem1550114 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550115 (x : real) : (term627 x) = (term476 x).
Proof. exact (MK_COMB (@lem1550113) (@lem1550114 x)). Qed.
Lemma lem1550116 (x : real) : (term626 x) = (term476 x).
Proof. exact (TRANS (@lem1550108 x) (@lem1550115 x)). Qed.
Lemma lem1550117 (x : real) : (term476 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1550118 (x : real) : (term626 x) = term47.
Proof. exact (TRANS (@lem1550116 x) (@lem1550117 x)). Qed.
Lemma lem1550119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550120 (x : real) : (term630 x) = term236.
Proof. exact (MK_COMB (@lem1550119) (@lem1550118 x)). Qed.
Lemma lem1550121 (x0 : real) (y0 : real) : (term631 x0 y0) = (term632 x0 y0).
Proof. exact (@lem1483480 (term163 x0) (term169 x0) (term163 y0) (term169 y0)). Qed.
Lemma lem1550122 (x0 : real) : (term561 x0) = (term562 x0).
Proof. exact (@lem1483438 term60 term72 x0). Qed.
Lemma lem1550124 (m : nat) : (term563 m) = term47.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1550125 : term564 = term47.
Proof. exact (@lem1550124 term67). Qed.
Lemma lem1550126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550127 : term565 = term475.
Proof. exact (MK_COMB (@lem1550126) (@lem1550125)). Qed.
Lemma lem1550128 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550129 (x0 : real) : (term562 x0) = (term476 x0).
Proof. exact (MK_COMB (@lem1550127) (@lem1550128 x0)). Qed.
Lemma lem1550130 (x0 : real) : (term561 x0) = (term476 x0).
Proof. exact (TRANS (@lem1550122 x0) (@lem1550129 x0)). Qed.
Lemma lem1550131 (x0 : real) : (term476 x0) = term47.
Proof. exact (@lem1483446 x0). Qed.
Lemma lem1550132 (x0 : real) : (term561 x0) = term47.
Proof. exact (TRANS (@lem1550130 x0) (@lem1550131 x0)). Qed.
Lemma lem1550133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550134 (x0 : real) : (term566 x0) = term236.
Proof. exact (MK_COMB (@lem1550133) (@lem1550132 x0)). Qed.
Lemma lem1550135 (y0 : real) : (term561 y0) = (term562 y0).
Proof. exact (@lem1483438 term60 term72 y0). Qed.
Lemma lem1550137 (m : nat) : (term563 m) = term47.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1550138 : term564 = term47.
Proof. exact (@lem1550137 term67). Qed.
Lemma lem1550139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550140 : term565 = term475.
Proof. exact (MK_COMB (@lem1550139) (@lem1550138)). Qed.
Lemma lem1550141 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550142 (y0 : real) : (term562 y0) = (term476 y0).
Proof. exact (MK_COMB (@lem1550140) (@lem1550141 y0)). Qed.
Lemma lem1550143 (y0 : real) : (term561 y0) = (term476 y0).
Proof. exact (TRANS (@lem1550135 y0) (@lem1550142 y0)). Qed.
Lemma lem1550144 (y0 : real) : (term476 y0) = term47.
Proof. exact (@lem1483446 y0). Qed.
Lemma lem1550145 (y0 : real) : (term561 y0) = term47.
Proof. exact (TRANS (@lem1550143 y0) (@lem1550144 y0)). Qed.
Lemma lem1550146 (x0 : real) (y0 : real) : (term632 x0 y0) = term542.
Proof. exact (MK_COMB (@lem1550134 x0) (@lem1550145 y0)). Qed.
Lemma lem1550147 (x0 : real) (y0 : real) : (term631 x0 y0) = term542.
Proof. exact (TRANS (@lem1550121 x0 y0) (@lem1550146 x0 y0)). Qed.
Lemma lem1550148 : term542 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1550149 (x0 : real) (y0 : real) : (term631 x0 y0) = term47.
Proof. exact (TRANS (@lem1550147 x0 y0) (@lem1550148)). Qed.
Lemma lem1550150 (x : real) (x0 : real) (y0 : real) : (term625 x x0 y0) = term542.
Proof. exact (MK_COMB (@lem1550120 x) (@lem1550149 x0 y0)). Qed.
Lemma lem1550151 (x : real) (x0 : real) (y0 : real) : (term624 x x0 y0) = term542.
Proof. exact (TRANS (@lem1550107 x x0 y0) (@lem1550150 x x0 y0)). Qed.
Lemma lem1550152 : term542 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1550153 (x : real) (x0 : real) (y0 : real) : (term624 x x0 y0) = term47.
Proof. exact (TRANS (@lem1550151 x x0 y0) (@lem1550152)). Qed.
Lemma lem1550154 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550155 (x : real) (x0 : real) (y0 : real) : (term633 x x0 y0) = term544.
Proof. exact (MK_COMB (@lem1550154) (@lem1550153 x x0 y0)). Qed.
Lemma lem1550156 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550157 (x : real) (x0 : real) (y0 : real) : (term623 x x0 y0) = term545.
Proof. exact (MK_COMB (@lem1550155 x x0 y0) (@lem1550156)). Qed.
Lemma lem1550158 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : term545.
Proof. exact (EQ_MP (@lem1550157 x x0 y0) (@lem1550106 x0 y0 x y h1)). Qed.
Lemma lem1550160 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550161 : term545 = term546.
Proof. exact (@lem1550160 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1550162 : term546 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1550163 : term545 = False.
Proof. exact (TRANS (@lem1550161) (@lem1550162)). Qed.
Lemma lem1550164 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term429 x0 y0 x y) : False.
Proof. exact (EQ_MP (@lem1550163) (@lem1550158 x0 y0 x y h1)). Qed.
Lemma lem1550165 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term431 x0 y0 x y) : False.
Proof. exact (or_elim (@lem1549428 x0 y0 x y h1) (fun h0 : term419 x0 y0 x y => @lem1549859 x0 y0 x y h0) (fun h0 : term429 x0 y0 x y => @lem1550164 x0 y0 x y h0)). Qed.
Lemma lem1550166 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term392 x0 y0 x y) : term392 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1550167 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term353 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1550168 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term352 x0 y0 x y.
Proof. exact (proj2 (@lem1550167 x0 y0 x y h1)). Qed.
Lemma lem1550169 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term103 y y0.
Proof. exact (proj1 (@lem1550167 x0 y0 x y h1)). Qed.
Lemma lem1550170 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term351 x0 y0 x y.
Proof. exact (proj2 (@lem1550168 x0 y0 x y h1)). Qed.
Lemma lem1550171 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term48 x x0.
Proof. exact (proj1 (@lem1550168 x0 y0 x y h1)). Qed.
Lemma lem1550172 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term103 x y.
Proof. exact (proj2 (@lem1550170 x0 y0 x y h1)). Qed.
Lemma lem1550173 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term347 x x0 y y0.
Proof. exact (proj1 (@lem1550170 x0 y0 x y h1)). Qed.
Lemma lem1550174 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term345 x x0 y y0.
Proof. exact (proj2 (@lem1550173 x0 y0 x y h1)). Qed.
Lemma lem1550176 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term343 x0 y y0.
Proof. exact (proj2 (@lem1550174 x0 y0 x y h1)). Qed.
Lemma lem1550179 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550180 : term453 = term454.
Proof. exact (@lem1550179 (NUMERAL 0) term66). Qed.
Lemma lem1550181 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550182 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550183 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550182 h1) (fun h1 : term454 = True => @lem1550181)). Qed.
Lemma lem1550184 : term454 = True.
Proof. exact (EQ_MP (@lem1550183) (@lem1550181)). Qed.
Lemma lem1550185 : term453 = True.
Proof. exact (TRANS (@lem1550180) (@lem1550184)). Qed.
Lemma lem1550186 : True = term453.
Proof. exact (SYM (@lem1550185)). Qed.
Lemma lem1550187 : term453.
Proof. exact (EQ_MP (@lem1550186) (@lem0)). Qed.
Lemma lem1550188 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term634 y y0.
Proof. exact (conj (@lem1550187) (@lem1550169 x0 y0 x y h1)). Qed.
Lemma lem1550190 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1550191 (y : real) (y0 : real) : term635 y y0.
Proof. exact (@lem1550190 term181 (term42 y y0)). Qed.
Lemma lem1550192 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term636 y y0.
Proof. exact (@lem1550191 y y0 (@lem1550188 x0 y0 x y h1)). Qed.
Lemma lem1550193 (y : real) (y0 : real) : (term528 y y0) = (term42 y y0).
Proof. exact (@lem1483460 (term42 y y0)). Qed.
Lemma lem1550194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1550195 (y : real) (y0 : real) : (term637 y y0) = (term102 y y0).
Proof. exact (MK_COMB (@lem1550194) (@lem1550193 y y0)). Qed.
Lemma lem1550196 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550197 (y : real) (y0 : real) : (term636 y y0) = (term103 y y0).
Proof. exact (MK_COMB (@lem1550195 y y0) (@lem1550196)). Qed.
Lemma lem1550198 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term103 y y0.
Proof. exact (EQ_MP (@lem1550197 y y0) (@lem1550192 x0 y0 x y h1)). Qed.
Lemma lem1550200 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550201 : term453 = term454.
Proof. exact (@lem1550200 (NUMERAL 0) term66). Qed.
Lemma lem1550202 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550203 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550204 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550203 h1) (fun h1 : term454 = True => @lem1550202)). Qed.
Lemma lem1550205 : term454 = True.
Proof. exact (EQ_MP (@lem1550204) (@lem1550202)). Qed.
Lemma lem1550206 : term453 = True.
Proof. exact (TRANS (@lem1550201) (@lem1550205)). Qed.
Lemma lem1550207 : True = term453.
Proof. exact (SYM (@lem1550206)). Qed.
Lemma lem1550208 : term453.
Proof. exact (EQ_MP (@lem1550207) (@lem0)). Qed.
Lemma lem1550209 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term634 x y.
Proof. exact (conj (@lem1550208) (@lem1550172 x0 y0 x y h1)). Qed.
Lemma lem1550211 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1550212 (x : real) (y : real) : term635 x y.
Proof. exact (@lem1550211 term181 (term42 x y)). Qed.
Lemma lem1550213 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term636 x y.
Proof. exact (@lem1550212 x y (@lem1550209 x0 y0 x y h1)). Qed.
Lemma lem1550214 (x : real) (y : real) : (term528 x y) = (term42 x y).
Proof. exact (@lem1483460 (term42 x y)). Qed.
Lemma lem1550215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1550216 (x : real) (y : real) : (term637 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1550215) (@lem1550214 x y)). Qed.
Lemma lem1550217 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550218 (x : real) (y : real) : (term636 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1550216 x y) (@lem1550217)). Qed.
Lemma lem1550219 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term103 x y.
Proof. exact (EQ_MP (@lem1550218 x y) (@lem1550213 x0 y0 x y h1)). Qed.
Lemma lem1550221 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550222 : term453 = term454.
Proof. exact (@lem1550221 (NUMERAL 0) term66). Qed.
Lemma lem1550223 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550224 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550225 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550224 h1) (fun h1 : term454 = True => @lem1550223)). Qed.
Lemma lem1550226 : term454 = True.
Proof. exact (EQ_MP (@lem1550225) (@lem1550223)). Qed.
Lemma lem1550227 : term453 = True.
Proof. exact (TRANS (@lem1550222) (@lem1550226)). Qed.
Lemma lem1550228 : True = term453.
Proof. exact (SYM (@lem1550227)). Qed.
Lemma lem1550229 : term453.
Proof. exact (EQ_MP (@lem1550228) (@lem0)). Qed.
Lemma lem1550230 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term487 x x0.
Proof. exact (conj (@lem1550229) (@lem1550171 x0 y0 x y h1)). Qed.
Lemma lem1550232 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550233 (x : real) (x0 : real) : term488 x x0.
Proof. exact (@lem1550232 term181 (term43 x x0)). Qed.
Lemma lem1550234 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term489 x x0.
Proof. exact (@lem1550233 x x0 (@lem1550230 x0 y0 x y h1)). Qed.
Lemma lem1550235 (x : real) (x0 : real) : (term490 x x0) = (term43 x x0).
Proof. exact (@lem1483460 (term43 x x0)). Qed.
Lemma lem1550236 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550237 (x : real) (x0 : real) : (term491 x x0) = (term46 x x0).
Proof. exact (MK_COMB (@lem1550236) (@lem1550235 x x0)). Qed.
Lemma lem1550238 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550239 (x : real) (x0 : real) : (term489 x x0) = (term48 x x0).
Proof. exact (MK_COMB (@lem1550237 x x0) (@lem1550238)). Qed.
Lemma lem1550240 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term48 x x0.
Proof. exact (EQ_MP (@lem1550239 x x0) (@lem1550234 x0 y0 x y h1)). Qed.
Lemma lem1550241 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term638 x0 x y.
Proof. exact (conj (@lem1550240 x0 y0 x y h1) (@lem1550219 x0 y0 x y h1)). Qed.
Lemma lem1550243 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1550244 (x0 : real) (x : real) (y : real) : term639 x0 x y.
Proof. exact (@lem1550243 (term43 x x0) (term42 x y)). Qed.
Lemma lem1550245 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term640 x0 x y.
Proof. exact (@lem1550244 x0 x y (@lem1550241 x0 y0 x y h1)). Qed.
Lemma lem1550246 (x : real) (x0 : real) (y : real) : (term641 x0 x y) = (term642 x x0 y).
Proof. exact (@lem1483480 (term44 x) x x0 (term44 y)). Qed.
Lemma lem1550247 (x : real) : (term541 x) = (term537 x).
Proof. exact (@lem1483440 term59 x). Qed.
Lemma lem1550249 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550250 : term538 = term47.
Proof. exact (@lem1550249 term66). Qed.
Lemma lem1550251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550252 : term539 = term475.
Proof. exact (MK_COMB (@lem1550251) (@lem1550250)). Qed.
Lemma lem1550253 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550254 (x : real) : (term537 x) = (term476 x).
Proof. exact (MK_COMB (@lem1550252) (@lem1550253 x)). Qed.
Lemma lem1550255 (x : real) : (term541 x) = (term476 x).
Proof. exact (TRANS (@lem1550247 x) (@lem1550254 x)). Qed.
Lemma lem1550256 (x : real) : (term476 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1550257 (x : real) : (term541 x) = term47.
Proof. exact (TRANS (@lem1550255 x) (@lem1550256 x)). Qed.
Lemma lem1550258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550259 (x : real) : (term643 x) = term236.
Proof. exact (MK_COMB (@lem1550258) (@lem1550257 x)). Qed.
Lemma lem1550260 (x0 : real) (y : real) : (term42 x0 y) = (term42 x0 y).
Proof. exact (eq_refl (term42 x0 y)). Qed.
Lemma lem1550261 (x : real) (x0 : real) (y : real) : (term642 x x0 y) = (term644 x0 y).
Proof. exact (MK_COMB (@lem1550259 x) (@lem1550260 x0 y)). Qed.
Lemma lem1550262 (x : real) (x0 : real) (y : real) : (term641 x0 x y) = (term644 x0 y).
Proof. exact (TRANS (@lem1550246 x x0 y) (@lem1550261 x x0 y)). Qed.
Lemma lem1550263 (x0 : real) (y : real) : (term644 x0 y) = (term42 x0 y).
Proof. exact (@lem1483448 (term42 x0 y)). Qed.
Lemma lem1550264 (x : real) (x0 : real) (y : real) : (term641 x0 x y) = (term42 x0 y).
Proof. exact (TRANS (@lem1550262 x x0 y) (@lem1550263 x0 y)). Qed.
Lemma lem1550265 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550266 (x : real) (x0 : real) (y : real) : (term645 x0 x y) = (term523 x0 y).
Proof. exact (MK_COMB (@lem1550265) (@lem1550264 x x0 y)). Qed.
Lemma lem1550267 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550268 (x : real) (x0 : real) (y : real) : (term640 x0 x y) = (term524 x0 y).
Proof. exact (MK_COMB (@lem1550266 x x0 y) (@lem1550267)). Qed.
Lemma lem1550269 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term524 x0 y.
Proof. exact (EQ_MP (@lem1550268 x x0 y) (@lem1550245 x0 y0 x y h1)). Qed.
Lemma lem1550271 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550272 : term453 = term454.
Proof. exact (@lem1550271 (NUMERAL 0) term66). Qed.
Lemma lem1550273 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550274 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550275 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550274 h1) (fun h1 : term454 = True => @lem1550273)). Qed.
Lemma lem1550276 : term454 = True.
Proof. exact (EQ_MP (@lem1550275) (@lem1550273)). Qed.
Lemma lem1550277 : term453 = True.
Proof. exact (TRANS (@lem1550272) (@lem1550276)). Qed.
Lemma lem1550278 : True = term453.
Proof. exact (SYM (@lem1550277)). Qed.
Lemma lem1550279 : term453.
Proof. exact (EQ_MP (@lem1550278) (@lem0)). Qed.
Lemma lem1550280 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term525 x0 y.
Proof. exact (conj (@lem1550279) (@lem1550269 x0 y0 x y h1)). Qed.
Lemma lem1550282 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550283 (x0 : real) (y : real) : term526 x0 y.
Proof. exact (@lem1550282 term181 (term42 x0 y)). Qed.
Lemma lem1550284 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term527 x0 y.
Proof. exact (@lem1550283 x0 y (@lem1550280 x0 y0 x y h1)). Qed.
Lemma lem1550285 (x0 : real) (y : real) : (term528 x0 y) = (term42 x0 y).
Proof. exact (@lem1483460 (term42 x0 y)). Qed.
Lemma lem1550286 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550287 (x0 : real) (y : real) : (term529 x0 y) = (term523 x0 y).
Proof. exact (MK_COMB (@lem1550286) (@lem1550285 x0 y)). Qed.
Lemma lem1550288 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550289 (x0 : real) (y : real) : (term527 x0 y) = (term524 x0 y).
Proof. exact (MK_COMB (@lem1550287 x0 y) (@lem1550288)). Qed.
Lemma lem1550290 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term524 x0 y.
Proof. exact (EQ_MP (@lem1550289 x0 y) (@lem1550284 x0 y0 x y h1)). Qed.
Lemma lem1550291 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term646 x0 y y0.
Proof. exact (conj (@lem1550290 x0 y0 x y h1) (@lem1550198 x0 y0 x y h1)). Qed.
Lemma lem1550293 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1550294 (x0 : real) (y : real) (y0 : real) : term647 x0 y y0.
Proof. exact (@lem1550293 (term42 x0 y) (term42 y y0)). Qed.
Lemma lem1550295 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term648 x0 y y0.
Proof. exact (@lem1550294 x0 y y0 (@lem1550291 x0 y0 x y h1)). Qed.
Lemma lem1550296 (x0 : real) (y : real) (y0 : real) : (term649 x0 y y0) = (term650 x0 y y0).
Proof. exact (@lem1483482 x0 (term44 y) (term42 y y0)). Qed.
Lemma lem1550297 (y : real) (y0 : real) : (term651 y y0) = (term652 y y0).
Proof. exact (@lem1483490 (term44 y) y (term44 y0)). Qed.
Lemma lem1550298 (y : real) : (term541 y) = (term537 y).
Proof. exact (@lem1483440 term59 y). Qed.
Lemma lem1550300 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550301 : term538 = term47.
Proof. exact (@lem1550300 term66). Qed.
Lemma lem1550302 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550303 : term539 = term475.
Proof. exact (MK_COMB (@lem1550302) (@lem1550301)). Qed.
Lemma lem1550304 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1550305 (y : real) : (term537 y) = (term476 y).
Proof. exact (MK_COMB (@lem1550303) (@lem1550304 y)). Qed.
Lemma lem1550306 (y : real) : (term541 y) = (term476 y).
Proof. exact (TRANS (@lem1550298 y) (@lem1550305 y)). Qed.
Lemma lem1550307 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1550308 (y : real) : (term541 y) = term47.
Proof. exact (TRANS (@lem1550306 y) (@lem1550307 y)). Qed.
Lemma lem1550309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550310 (y : real) : (term643 y) = term236.
Proof. exact (MK_COMB (@lem1550309) (@lem1550308 y)). Qed.
Lemma lem1550311 (y0 : real) : (term44 y0) = (term44 y0).
Proof. exact (eq_refl (term44 y0)). Qed.
Lemma lem1550312 (y : real) (y0 : real) : (term652 y y0) = (term521 y0).
Proof. exact (MK_COMB (@lem1550310 y) (@lem1550311 y0)). Qed.
Lemma lem1550313 (y : real) (y0 : real) : (term651 y y0) = (term521 y0).
Proof. exact (TRANS (@lem1550297 y y0) (@lem1550312 y y0)). Qed.
Lemma lem1550314 (y0 : real) : (term521 y0) = (term44 y0).
Proof. exact (@lem1483448 (term44 y0)). Qed.
Lemma lem1550315 (y : real) (y0 : real) : (term651 y y0) = (term44 y0).
Proof. exact (TRANS (@lem1550313 y y0) (@lem1550314 y0)). Qed.
Lemma lem1550316 (x0 : real) : (real_add x0) = (real_add x0).
Proof. exact (eq_refl (real_add x0)). Qed.
Lemma lem1550317 (y : real) (x0 : real) (y0 : real) : (term650 x0 y y0) = (term42 x0 y0).
Proof. exact (MK_COMB (@lem1550316 x0) (@lem1550315 y y0)). Qed.
Lemma lem1550318 (y : real) (x0 : real) (y0 : real) : (term649 x0 y y0) = (term42 x0 y0).
Proof. exact (TRANS (@lem1550296 x0 y y0) (@lem1550317 y x0 y0)). Qed.
Lemma lem1550319 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550320 (y : real) (x0 : real) (y0 : real) : (term653 x0 y y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1550319) (@lem1550318 y x0 y0)). Qed.
Lemma lem1550321 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550322 (y : real) (x0 : real) (y0 : real) : (term648 x0 y y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1550320 y x0 y0) (@lem1550321)). Qed.
Lemma lem1550323 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1550322 y x0 y0) (@lem1550295 x0 y0 x y h1)). Qed.
Lemma lem1550325 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550326 : term453 = term454.
Proof. exact (@lem1550325 (NUMERAL 0) term66). Qed.
Lemma lem1550327 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550328 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550329 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550328 h1) (fun h1 : term454 = True => @lem1550327)). Qed.
Lemma lem1550330 : term454 = True.
Proof. exact (EQ_MP (@lem1550329) (@lem1550327)). Qed.
Lemma lem1550331 : term453 = True.
Proof. exact (TRANS (@lem1550326) (@lem1550330)). Qed.
Lemma lem1550332 : True = term453.
Proof. exact (SYM (@lem1550331)). Qed.
Lemma lem1550333 : term453.
Proof. exact (EQ_MP (@lem1550332) (@lem0)). Qed.
Lemma lem1550334 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term525 x0 y0.
Proof. exact (conj (@lem1550333) (@lem1550323 x0 y0 x y h1)). Qed.
Lemma lem1550336 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550337 (x0 : real) (y0 : real) : term526 x0 y0.
Proof. exact (@lem1550336 term181 (term42 x0 y0)). Qed.
Lemma lem1550338 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term527 x0 y0.
Proof. exact (@lem1550337 x0 y0 (@lem1550334 x0 y0 x y h1)). Qed.
Lemma lem1550339 (x0 : real) (y0 : real) : (term528 x0 y0) = (term42 x0 y0).
Proof. exact (@lem1483460 (term42 x0 y0)). Qed.
Lemma lem1550340 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550341 (x0 : real) (y0 : real) : (term529 x0 y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1550340) (@lem1550339 x0 y0)). Qed.
Lemma lem1550342 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550343 (x0 : real) (y0 : real) : (term527 x0 y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1550341 x0 y0) (@lem1550342)). Qed.
Lemma lem1550344 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1550343 x0 y0) (@lem1550338 x0 y0 x y h1)). Qed.
Lemma lem1550346 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550347 : term435 = term436.
Proof. exact (@lem1550346 (NUMERAL 0) term67). Qed.
Lemma lem1550348 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1550349 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1550350 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1550349 h1) (fun h1 : term436 = True => @lem1550348)). Qed.
Lemma lem1550351 : term436 = True.
Proof. exact (EQ_MP (@lem1550350) (@lem1550348)). Qed.
Lemma lem1550352 : term435 = True.
Proof. exact (TRANS (@lem1550347) (@lem1550351)). Qed.
Lemma lem1550353 : True = term435.
Proof. exact (SYM (@lem1550352)). Qed.
Lemma lem1550354 : term435.
Proof. exact (EQ_MP (@lem1550353) (@lem0)). Qed.
Lemma lem1550355 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term438 y y0.
Proof. exact (conj (@lem1550354) (@lem1550169 x0 y0 x y h1)). Qed.
Lemma lem1550357 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1550358 (y : real) (y0 : real) : term440 y y0.
Proof. exact (@lem1550357 term60 (term42 y y0)). Qed.
Lemma lem1550359 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term441 y y0.
Proof. exact (@lem1550358 y y0 (@lem1550355 x0 y0 x y h1)). Qed.
Lemma lem1550360 (y : real) (y0 : real) : (term442 y y0) = (term443 y y0).
Proof. exact (@lem1483508 y term60 (term44 y0)). Qed.
Lemma lem1550361 (y0 : real) : (term444 y0) = (term445 y0).
Proof. exact (@lem1483476 term60 term59 y0). Qed.
Lemma lem1550363 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550364 : term447 = term448.
Proof. exact (@lem1550363 term67 term66). Qed.
Lemma lem1550365 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1550366 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1550367 : term160 = term67.
Proof. exact (EQ_MP (@lem1550366) (@lem1550365)). Qed.
Lemma lem1550368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550369 : term158 = term60.
Proof. exact (MK_COMB (@lem1550368) (@lem1550367)). Qed.
Lemma lem1550370 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550371 : term448 = term72.
Proof. exact (MK_COMB (@lem1550370) (@lem1550369)). Qed.
Lemma lem1550372 : term447 = term72.
Proof. exact (TRANS (@lem1550364) (@lem1550371)). Qed.
Lemma lem1550373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550374 : term449 = term74.
Proof. exact (MK_COMB (@lem1550373) (@lem1550372)). Qed.
Lemma lem1550375 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550376 (y0 : real) : (term445 y0) = (term169 y0).
Proof. exact (MK_COMB (@lem1550374) (@lem1550375 y0)). Qed.
Lemma lem1550377 (y0 : real) : (term444 y0) = (term169 y0).
Proof. exact (TRANS (@lem1550361 y0) (@lem1550376 y0)). Qed.
Lemma lem1550380 (y : real) : (term248 y) = (term248 y).
Proof. exact (eq_refl (term248 y)). Qed.
Lemma lem1550381 (y : real) (y0 : real) : (term443 y y0) = (term249 y y0).
Proof. exact (MK_COMB (@lem1550380 y) (@lem1550377 y0)). Qed.
Lemma lem1550382 (y : real) (y0 : real) : (term442 y y0) = (term249 y y0).
Proof. exact (TRANS (@lem1550360 y y0) (@lem1550381 y y0)). Qed.
Lemma lem1550383 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1550384 (y : real) (y0 : real) : (term450 y y0) = (term451 y y0).
Proof. exact (MK_COMB (@lem1550383) (@lem1550382 y y0)). Qed.
Lemma lem1550385 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550386 (y : real) (y0 : real) : (term441 y y0) = (term452 y y0).
Proof. exact (MK_COMB (@lem1550384 y y0) (@lem1550385)). Qed.
Lemma lem1550387 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term452 y y0.
Proof. exact (EQ_MP (@lem1550386 y y0) (@lem1550359 x0 y0 x y h1)). Qed.
Lemma lem1550389 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550390 : term453 = term454.
Proof. exact (@lem1550389 (NUMERAL 0) term66). Qed.
Lemma lem1550391 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550392 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550393 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550392 h1) (fun h1 : term454 = True => @lem1550391)). Qed.
Lemma lem1550394 : term454 = True.
Proof. exact (EQ_MP (@lem1550393) (@lem1550391)). Qed.
Lemma lem1550395 : term453 = True.
Proof. exact (TRANS (@lem1550390) (@lem1550394)). Qed.
Lemma lem1550396 : True = term453.
Proof. exact (SYM (@lem1550395)). Qed.
Lemma lem1550397 : term453.
Proof. exact (EQ_MP (@lem1550396) (@lem0)). Qed.
Lemma lem1550398 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term456 x0 y y0.
Proof. exact (conj (@lem1550397) (@lem1550176 x0 y0 x y h1)). Qed.
Lemma lem1550400 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550401 (x0 : real) (y : real) (y0 : real) : term458 x0 y y0.
Proof. exact (@lem1550400 term181 (term333 x0 y y0)). Qed.
Lemma lem1550402 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term459 x0 y y0.
Proof. exact (@lem1550401 x0 y y0 (@lem1550398 x0 y0 x y h1)). Qed.
Lemma lem1550403 (x0 : real) (y : real) (y0 : real) : (term460 x0 y y0) = (term333 x0 y y0).
Proof. exact (@lem1483460 (term333 x0 y y0)). Qed.
Lemma lem1550404 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550405 (x0 : real) (y : real) (y0 : real) : (term461 x0 y y0) = (term342 x0 y y0).
Proof. exact (MK_COMB (@lem1550404) (@lem1550403 x0 y y0)). Qed.
Lemma lem1550406 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550407 (x0 : real) (y : real) (y0 : real) : (term459 x0 y y0) = (term343 x0 y y0).
Proof. exact (MK_COMB (@lem1550405 x0 y y0) (@lem1550406)). Qed.
Lemma lem1550408 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term343 x0 y y0.
Proof. exact (EQ_MP (@lem1550407 x0 y y0) (@lem1550402 x0 y0 x y h1)). Qed.
Lemma lem1550409 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term462 x0 y y0.
Proof. exact (conj (@lem1550408 x0 y0 x y h1) (@lem1550387 x0 y0 x y h1)). Qed.
Lemma lem1550411 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1550412 (x0 : real) (y : real) (y0 : real) : term464 x0 y y0.
Proof. exact (@lem1550411 (term333 x0 y y0) (term249 y y0)). Qed.
Lemma lem1550413 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term465 x0 y y0.
Proof. exact (@lem1550412 x0 y y0 (@lem1550409 x0 y0 x y h1)). Qed.
Lemma lem1550414 (x0 : real) (y : real) (y0 : real) : (term466 x0 y y0) = (term467 x0 y y0).
Proof. exact (@lem1483482 (term44 x0) (term332 y y0) (term249 y y0)). Qed.
Lemma lem1550415 (y : real) (y0 : real) : (term468 y y0) = (term469 y y0).
Proof. exact (@lem1483480 (term169 y) (term163 y) (term331 y0) (term169 y0)). Qed.
Lemma lem1550416 (y : real) : (term470 y) = (term471 y).
Proof. exact (@lem1483438 term72 term60 y). Qed.
Lemma lem1550418 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550419 : term473 = term47.
Proof. exact (@lem1550418 term67). Qed.
Lemma lem1550420 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550421 : term474 = term475.
Proof. exact (MK_COMB (@lem1550420) (@lem1550419)). Qed.
Lemma lem1550422 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1550423 (y : real) : (term471 y) = (term476 y).
Proof. exact (MK_COMB (@lem1550421) (@lem1550422 y)). Qed.
Lemma lem1550424 (y : real) : (term470 y) = (term476 y).
Proof. exact (TRANS (@lem1550416 y) (@lem1550423 y)). Qed.
Lemma lem1550425 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1550426 (y : real) : (term470 y) = term47.
Proof. exact (TRANS (@lem1550424 y) (@lem1550425 y)). Qed.
Lemma lem1550427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550428 (y : real) : (term477 y) = term236.
Proof. exact (MK_COMB (@lem1550427) (@lem1550426 y)). Qed.
Lemma lem1550429 (y0 : real) : (term478 y0) = (term479 y0).
Proof. exact (@lem1483438 term269 term72 y0). Qed.
Lemma lem1550432 : term480 = term181.
Proof. exact (@lem1367769 term67 term66). Qed.
Lemma lem1550433 : term327 = term265.
Proof. exact (@lem706949). Qed.
Lemma lem1550434 : (term327 = term265) = (term328 = term267).
Proof. exact (@lem1006570 term69 (BIT1 0) term265). Qed.
Lemma lem1550435 : term328 = term267.
Proof. exact (EQ_MP (@lem1550434) (@lem1550433)). Qed.
Lemma lem1550436 : term267 = term328.
Proof. exact (SYM (@lem1550435)). Qed.
Lemma lem1550437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550438 : term269 = term326.
Proof. exact (MK_COMB (@lem1550437) (@lem1550436)). Qed.
Lemma lem1550439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550440 : term481 = term482.
Proof. exact (MK_COMB (@lem1550439) (@lem1550438)). Qed.
Lemma lem1550441 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem1550442 : term483 = term480.
Proof. exact (MK_COMB (@lem1550440) (@lem1550441)). Qed.
Lemma lem1550443 : term483 = term181.
Proof. exact (TRANS (@lem1550442) (@lem1550432)). Qed.
Lemma lem1550444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550445 : term484 = term188.
Proof. exact (MK_COMB (@lem1550444) (@lem1550443)). Qed.
Lemma lem1550446 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550447 (y0 : real) : (term479 y0) = (term189 y0).
Proof. exact (MK_COMB (@lem1550445) (@lem1550446 y0)). Qed.
Lemma lem1550448 (y0 : real) : (term478 y0) = (term189 y0).
Proof. exact (TRANS (@lem1550429 y0) (@lem1550447 y0)). Qed.
Lemma lem1550449 (y0 : real) : (term189 y0) = y0.
Proof. exact (@lem1483436 y0). Qed.
Lemma lem1550450 (y0 : real) : (term478 y0) = y0.
Proof. exact (TRANS (@lem1550448 y0) (@lem1550449 y0)). Qed.
Lemma lem1550451 (y : real) (y0 : real) : (term469 y y0) = (term485 y0).
Proof. exact (MK_COMB (@lem1550428 y) (@lem1550450 y0)). Qed.
Lemma lem1550452 (y : real) (y0 : real) : (term468 y y0) = (term485 y0).
Proof. exact (TRANS (@lem1550415 y y0) (@lem1550451 y y0)). Qed.
Lemma lem1550453 (y0 : real) : (term485 y0) = y0.
Proof. exact (@lem1483448 y0). Qed.
Lemma lem1550454 (y : real) (y0 : real) : (term468 y y0) = y0.
Proof. exact (TRANS (@lem1550452 y y0) (@lem1550453 y0)). Qed.
Lemma lem1550455 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1550456 (y : real) (x0 : real) (y0 : real) : (term467 x0 y y0) = (term43 x0 y0).
Proof. exact (MK_COMB (@lem1550455 x0) (@lem1550454 y y0)). Qed.
Lemma lem1550457 (y : real) (x0 : real) (y0 : real) : (term466 x0 y y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1550414 x0 y y0) (@lem1550456 y x0 y0)). Qed.
Lemma lem1550458 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550459 (y : real) (x0 : real) (y0 : real) : (term486 x0 y y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1550458) (@lem1550457 y x0 y0)). Qed.
Lemma lem1550460 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550461 (y : real) (x0 : real) (y0 : real) : (term465 x0 y y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1550459 y x0 y0) (@lem1550460)). Qed.
Lemma lem1550462 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1550461 y x0 y0) (@lem1550413 x0 y0 x y h1)). Qed.
Lemma lem1550464 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550465 : term453 = term454.
Proof. exact (@lem1550464 (NUMERAL 0) term66). Qed.
Lemma lem1550466 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550467 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550468 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550467 h1) (fun h1 : term454 = True => @lem1550466)). Qed.
Lemma lem1550469 : term454 = True.
Proof. exact (EQ_MP (@lem1550468) (@lem1550466)). Qed.
Lemma lem1550470 : term453 = True.
Proof. exact (TRANS (@lem1550465) (@lem1550469)). Qed.
Lemma lem1550471 : True = term453.
Proof. exact (SYM (@lem1550470)). Qed.
Lemma lem1550472 : term453.
Proof. exact (EQ_MP (@lem1550471) (@lem0)). Qed.
Lemma lem1550473 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term487 x0 y0.
Proof. exact (conj (@lem1550472) (@lem1550462 x0 y0 x y h1)). Qed.
Lemma lem1550475 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550476 (x0 : real) (y0 : real) : term488 x0 y0.
Proof. exact (@lem1550475 term181 (term43 x0 y0)). Qed.
Lemma lem1550477 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term489 x0 y0.
Proof. exact (@lem1550476 x0 y0 (@lem1550473 x0 y0 x y h1)). Qed.
Lemma lem1550478 (x0 : real) (y0 : real) : (term490 x0 y0) = (term43 x0 y0).
Proof. exact (@lem1483460 (term43 x0 y0)). Qed.
Lemma lem1550479 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550480 (x0 : real) (y0 : real) : (term491 x0 y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1550479) (@lem1550478 x0 y0)). Qed.
Lemma lem1550481 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550482 (x0 : real) (y0 : real) : (term489 x0 y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1550480 x0 y0) (@lem1550481)). Qed.
Lemma lem1550483 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1550482 x0 y0) (@lem1550477 x0 y0 x y h1)). Qed.
Lemma lem1550484 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term654 x0 y0.
Proof. exact (conj (@lem1550483 x0 y0 x y h1) (@lem1550344 x0 y0 x y h1)). Qed.
Lemma lem1550486 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1550487 (x0 : real) (y0 : real) : term655 x0 y0.
Proof. exact (@lem1550486 (term43 x0 y0) (term42 x0 y0)). Qed.
Lemma lem1550488 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term656 x0 y0.
Proof. exact (@lem1550487 x0 y0 (@lem1550484 x0 y0 x y h1)). Qed.
Lemma lem1550489 (x0 : real) (y0 : real) : (term657 x0 y0) = (term658 x0 y0).
Proof. exact (@lem1483480 (term44 x0) x0 y0 (term44 y0)). Qed.
Lemma lem1550490 (x0 : real) : (term541 x0) = (term537 x0).
Proof. exact (@lem1483440 term59 x0). Qed.
Lemma lem1550492 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550493 : term538 = term47.
Proof. exact (@lem1550492 term66). Qed.
Lemma lem1550494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550495 : term539 = term475.
Proof. exact (MK_COMB (@lem1550494) (@lem1550493)). Qed.
Lemma lem1550496 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550497 (x0 : real) : (term537 x0) = (term476 x0).
Proof. exact (MK_COMB (@lem1550495) (@lem1550496 x0)). Qed.
Lemma lem1550498 (x0 : real) : (term541 x0) = (term476 x0).
Proof. exact (TRANS (@lem1550490 x0) (@lem1550497 x0)). Qed.
Lemma lem1550499 (x0 : real) : (term476 x0) = term47.
Proof. exact (@lem1483446 x0). Qed.
Lemma lem1550500 (x0 : real) : (term541 x0) = term47.
Proof. exact (TRANS (@lem1550498 x0) (@lem1550499 x0)). Qed.
Lemma lem1550501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550502 (x0 : real) : (term643 x0) = term236.
Proof. exact (MK_COMB (@lem1550501) (@lem1550500 x0)). Qed.
Lemma lem1550503 (y0 : real) : (term536 y0) = (term537 y0).
Proof. exact (@lem1483442 term59 y0). Qed.
Lemma lem1550505 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550506 : term538 = term47.
Proof. exact (@lem1550505 term66). Qed.
Lemma lem1550507 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550508 : term539 = term475.
Proof. exact (MK_COMB (@lem1550507) (@lem1550506)). Qed.
Lemma lem1550509 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550510 (y0 : real) : (term537 y0) = (term476 y0).
Proof. exact (MK_COMB (@lem1550508) (@lem1550509 y0)). Qed.
Lemma lem1550511 (y0 : real) : (term536 y0) = (term476 y0).
Proof. exact (TRANS (@lem1550503 y0) (@lem1550510 y0)). Qed.
Lemma lem1550512 (y0 : real) : (term476 y0) = term47.
Proof. exact (@lem1483446 y0). Qed.
Lemma lem1550513 (y0 : real) : (term536 y0) = term47.
Proof. exact (TRANS (@lem1550511 y0) (@lem1550512 y0)). Qed.
Lemma lem1550514 (x0 : real) (y0 : real) : (term658 x0 y0) = term542.
Proof. exact (MK_COMB (@lem1550502 x0) (@lem1550513 y0)). Qed.
Lemma lem1550515 (x0 : real) (y0 : real) : (term657 x0 y0) = term542.
Proof. exact (TRANS (@lem1550489 x0 y0) (@lem1550514 x0 y0)). Qed.
Lemma lem1550516 : term542 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1550517 (x0 : real) (y0 : real) : (term657 x0 y0) = term47.
Proof. exact (TRANS (@lem1550515 x0 y0) (@lem1550516)). Qed.
Lemma lem1550518 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550519 (x0 : real) (y0 : real) : (term659 x0 y0) = term544.
Proof. exact (MK_COMB (@lem1550518) (@lem1550517 x0 y0)). Qed.
Lemma lem1550520 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550521 (x0 : real) (y0 : real) : (term656 x0 y0) = term545.
Proof. exact (MK_COMB (@lem1550519 x0 y0) (@lem1550520)). Qed.
Lemma lem1550522 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : term545.
Proof. exact (EQ_MP (@lem1550521 x0 y0) (@lem1550488 x0 y0 x y h1)). Qed.
Lemma lem1550524 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550525 : term545 = term546.
Proof. exact (@lem1550524 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1550526 : term546 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1550527 : term545 = False.
Proof. exact (TRANS (@lem1550525) (@lem1550526)). Qed.
Lemma lem1550528 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term353 x0 y0 x y) : False.
Proof. exact (EQ_MP (@lem1550527) (@lem1550522 x0 y0 x y h1)). Qed.
Lemma lem1550529 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term390 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1550530 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term389 x0 y0 x y.
Proof. exact (proj2 (@lem1550529 x0 y0 x y h1)). Qed.
Lemma lem1550532 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term388 x0 y0 x y.
Proof. exact (proj2 (@lem1550530 x0 y0 x y h1)). Qed.
Lemma lem1550533 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term48 x x0.
Proof. exact (proj1 (@lem1550530 x0 y0 x y h1)). Qed.
Lemma lem1550534 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term103 x y.
Proof. exact (proj2 (@lem1550532 x0 y0 x y h1)). Qed.
Lemma lem1550535 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term384 x x0 y y0.
Proof. exact (proj1 (@lem1550532 x0 y0 x y h1)). Qed.
Lemma lem1550536 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term382 x x0 y y0.
Proof. exact (proj2 (@lem1550535 x0 y0 x y h1)). Qed.
Lemma lem1550538 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term380 x0 y y0.
Proof. exact (proj2 (@lem1550536 x0 y0 x y h1)). Qed.
Lemma lem1550539 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term287 x x0 y0.
Proof. exact (proj1 (@lem1550536 x0 y0 x y h1)). Qed.
Lemma lem1550541 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550542 : term453 = term454.
Proof. exact (@lem1550541 (NUMERAL 0) term66). Qed.
Lemma lem1550543 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550544 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550545 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550544 h1) (fun h1 : term454 = True => @lem1550543)). Qed.
Lemma lem1550546 : term454 = True.
Proof. exact (EQ_MP (@lem1550545) (@lem1550543)). Qed.
Lemma lem1550547 : term453 = True.
Proof. exact (TRANS (@lem1550542) (@lem1550546)). Qed.
Lemma lem1550548 : True = term453.
Proof. exact (SYM (@lem1550547)). Qed.
Lemma lem1550549 : term453.
Proof. exact (EQ_MP (@lem1550548) (@lem0)). Qed.
Lemma lem1550550 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term660 x x0 y0.
Proof. exact (conj (@lem1550549) (@lem1550539 x0 y0 x y h1)). Qed.
Lemma lem1550552 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550553 (x : real) (x0 : real) (y0 : real) : term661 x x0 y0.
Proof. exact (@lem1550552 term181 (term277 x x0 y0)). Qed.
Lemma lem1550554 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term662 x x0 y0.
Proof. exact (@lem1550553 x x0 y0 (@lem1550550 x0 y0 x y h1)). Qed.
Lemma lem1550555 (x : real) (x0 : real) (y0 : real) : (term663 x x0 y0) = (term277 x x0 y0).
Proof. exact (@lem1483460 (term277 x x0 y0)). Qed.
Lemma lem1550556 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550557 (x : real) (x0 : real) (y0 : real) : (term664 x x0 y0) = (term286 x x0 y0).
Proof. exact (MK_COMB (@lem1550556) (@lem1550555 x x0 y0)). Qed.
Lemma lem1550558 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550559 (x : real) (x0 : real) (y0 : real) : (term662 x x0 y0) = (term287 x x0 y0).
Proof. exact (MK_COMB (@lem1550557 x x0 y0) (@lem1550558)). Qed.
Lemma lem1550560 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term287 x x0 y0.
Proof. exact (EQ_MP (@lem1550559 x x0 y0) (@lem1550554 x0 y0 x y h1)). Qed.
Lemma lem1550562 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550563 : term435 = term436.
Proof. exact (@lem1550562 (NUMERAL 0) term67). Qed.
Lemma lem1550564 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1550565 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1550566 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1550565 h1) (fun h1 : term436 = True => @lem1550564)). Qed.
Lemma lem1550567 : term436 = True.
Proof. exact (EQ_MP (@lem1550566) (@lem1550564)). Qed.
Lemma lem1550568 : term435 = True.
Proof. exact (TRANS (@lem1550563) (@lem1550567)). Qed.
Lemma lem1550569 : True = term435.
Proof. exact (SYM (@lem1550568)). Qed.
Lemma lem1550570 : term435.
Proof. exact (EQ_MP (@lem1550569) (@lem0)). Qed.
Lemma lem1550571 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term665 x x0.
Proof. exact (conj (@lem1550570) (@lem1550533 x0 y0 x y h1)). Qed.
Lemma lem1550573 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550574 (x : real) (x0 : real) : term666 x x0.
Proof. exact (@lem1550573 term60 (term43 x x0)). Qed.
Lemma lem1550575 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term667 x x0.
Proof. exact (@lem1550574 x x0 (@lem1550571 x0 y0 x y h1)). Qed.
Lemma lem1550576 (x : real) (x0 : real) : (term668 x x0) = (term669 x x0).
Proof. exact (@lem1483508 (term44 x) term60 x0). Qed.
Lemma lem1550577 (x0 : real) : (term163 x0) = (term163 x0).
Proof. exact (eq_refl (term163 x0)). Qed.
Lemma lem1550578 (x : real) : (term444 x) = (term445 x).
Proof. exact (@lem1483476 term60 term59 x). Qed.
Lemma lem1550580 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550581 : term447 = term448.
Proof. exact (@lem1550580 term67 term66). Qed.
Lemma lem1550582 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1550583 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1550584 : term160 = term67.
Proof. exact (EQ_MP (@lem1550583) (@lem1550582)). Qed.
Lemma lem1550585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550586 : term158 = term60.
Proof. exact (MK_COMB (@lem1550585) (@lem1550584)). Qed.
Lemma lem1550587 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550588 : term448 = term72.
Proof. exact (MK_COMB (@lem1550587) (@lem1550586)). Qed.
Lemma lem1550589 : term447 = term72.
Proof. exact (TRANS (@lem1550581) (@lem1550588)). Qed.
Lemma lem1550590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550591 : term449 = term74.
Proof. exact (MK_COMB (@lem1550590) (@lem1550589)). Qed.
Lemma lem1550592 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550593 (x : real) : (term445 x) = (term169 x).
Proof. exact (MK_COMB (@lem1550591) (@lem1550592 x)). Qed.
Lemma lem1550594 (x : real) : (term444 x) = (term169 x).
Proof. exact (TRANS (@lem1550578 x) (@lem1550593 x)). Qed.
Lemma lem1550595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550596 (x : real) : (term579 x) = (term164 x).
Proof. exact (MK_COMB (@lem1550595) (@lem1550594 x)). Qed.
Lemma lem1550597 (x : real) (x0 : real) : (term669 x x0) = (term165 x x0).
Proof. exact (MK_COMB (@lem1550596 x) (@lem1550577 x0)). Qed.
Lemma lem1550598 (x : real) (x0 : real) : (term668 x x0) = (term165 x x0).
Proof. exact (TRANS (@lem1550576 x x0) (@lem1550597 x x0)). Qed.
Lemma lem1550599 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550600 (x : real) (x0 : real) : (term670 x x0) = (term671 x x0).
Proof. exact (MK_COMB (@lem1550599) (@lem1550598 x x0)). Qed.
Lemma lem1550601 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550602 (x : real) (x0 : real) : (term667 x x0) = (term672 x x0).
Proof. exact (MK_COMB (@lem1550600 x x0) (@lem1550601)). Qed.
Lemma lem1550603 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term672 x x0.
Proof. exact (EQ_MP (@lem1550602 x x0) (@lem1550575 x0 y0 x y h1)). Qed.
Lemma lem1550604 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term673 x x0 y0.
Proof. exact (conj (@lem1550603 x0 y0 x y h1) (@lem1550560 x0 y0 x y h1)). Qed.
Lemma lem1550606 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1550607 (x : real) (x0 : real) (y0 : real) : term674 x x0 y0.
Proof. exact (@lem1550606 (term165 x x0) (term277 x x0 y0)). Qed.
Lemma lem1550608 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term675 x x0 y0.
Proof. exact (@lem1550607 x x0 y0 (@lem1550604 x0 y0 x y h1)). Qed.
Lemma lem1550609 (x : real) (x0 : real) (y0 : real) : (term676 x x0 y0) = (term677 x x0 y0).
Proof. exact (@lem1483480 (term169 x) (term163 x) (term163 x0) (term276 x0 y0)). Qed.
Lemma lem1550610 (x : real) : (term470 x) = (term471 x).
Proof. exact (@lem1483438 term72 term60 x). Qed.
Lemma lem1550612 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550613 : term473 = term47.
Proof. exact (@lem1550612 term67). Qed.
Lemma lem1550614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550615 : term474 = term475.
Proof. exact (MK_COMB (@lem1550614) (@lem1550613)). Qed.
Lemma lem1550616 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550617 (x : real) : (term471 x) = (term476 x).
Proof. exact (MK_COMB (@lem1550615) (@lem1550616 x)). Qed.
Lemma lem1550618 (x : real) : (term470 x) = (term476 x).
Proof. exact (TRANS (@lem1550610 x) (@lem1550617 x)). Qed.
Lemma lem1550619 (x : real) : (term476 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1550620 (x : real) : (term470 x) = term47.
Proof. exact (TRANS (@lem1550618 x) (@lem1550619 x)). Qed.
Lemma lem1550621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550622 (x : real) : (term477 x) = term236.
Proof. exact (MK_COMB (@lem1550621) (@lem1550620 x)). Qed.
Lemma lem1550623 (x0 : real) (y0 : real) : (term678 x0 y0) = (term679 x0 y0).
Proof. exact (@lem1483490 (term163 x0) (term273 x0) y0). Qed.
Lemma lem1550624 (x0 : real) : (term680 x0) = (term681 x0).
Proof. exact (@lem1483438 term60 term270 x0). Qed.
Lemma lem1550627 : term682 = term59.
Proof. exact (@lem1367771 term67 term66). Qed.
Lemma lem1550628 : term327 = term265.
Proof. exact (@lem706949). Qed.
Lemma lem1550629 : (term327 = term265) = (term328 = term267).
Proof. exact (@lem1006570 term69 (BIT1 0) term265). Qed.
Lemma lem1550630 : term328 = term267.
Proof. exact (EQ_MP (@lem1550629) (@lem1550628)). Qed.
Lemma lem1550631 : term267 = term328.
Proof. exact (SYM (@lem1550630)). Qed.
Lemma lem1550632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550633 : term269 = term326.
Proof. exact (MK_COMB (@lem1550632) (@lem1550631)). Qed.
Lemma lem1550634 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550635 : term270 = term683.
Proof. exact (MK_COMB (@lem1550634) (@lem1550633)). Qed.
Lemma lem1550636 : term684 = term684.
Proof. exact (eq_refl term684). Qed.
Lemma lem1550637 : term685 = term682.
Proof. exact (MK_COMB (@lem1550636) (@lem1550635)). Qed.
Lemma lem1550638 : term685 = term59.
Proof. exact (TRANS (@lem1550637) (@lem1550627)). Qed.
Lemma lem1550639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550640 : term686 = term368.
Proof. exact (MK_COMB (@lem1550639) (@lem1550638)). Qed.
Lemma lem1550641 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550642 (x0 : real) : (term681 x0) = (term44 x0).
Proof. exact (MK_COMB (@lem1550640) (@lem1550641 x0)). Qed.
Lemma lem1550643 (x0 : real) : (term680 x0) = (term44 x0).
Proof. exact (TRANS (@lem1550624 x0) (@lem1550642 x0)). Qed.
Lemma lem1550644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550645 (x0 : real) : (term687 x0) = (term173 x0).
Proof. exact (MK_COMB (@lem1550644) (@lem1550643 x0)). Qed.
Lemma lem1550646 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550647 (x0 : real) (y0 : real) : (term679 x0 y0) = (term43 x0 y0).
Proof. exact (MK_COMB (@lem1550645 x0) (@lem1550646 y0)). Qed.
Lemma lem1550648 (x0 : real) (y0 : real) : (term678 x0 y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1550623 x0 y0) (@lem1550647 x0 y0)). Qed.
Lemma lem1550649 (x : real) (x0 : real) (y0 : real) : (term677 x x0 y0) = (term237 x0 y0).
Proof. exact (MK_COMB (@lem1550622 x) (@lem1550648 x0 y0)). Qed.
Lemma lem1550650 (x : real) (x0 : real) (y0 : real) : (term676 x x0 y0) = (term237 x0 y0).
Proof. exact (TRANS (@lem1550609 x x0 y0) (@lem1550649 x x0 y0)). Qed.
Lemma lem1550651 (x0 : real) (y0 : real) : (term237 x0 y0) = (term43 x0 y0).
Proof. exact (@lem1483448 (term43 x0 y0)). Qed.
Lemma lem1550652 (x : real) (x0 : real) (y0 : real) : (term676 x x0 y0) = (term43 x0 y0).
Proof. exact (TRANS (@lem1550650 x x0 y0) (@lem1550651 x0 y0)). Qed.
Lemma lem1550653 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550654 (x : real) (x0 : real) (y0 : real) : (term688 x x0 y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1550653) (@lem1550652 x x0 y0)). Qed.
Lemma lem1550655 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550656 (x : real) (x0 : real) (y0 : real) : (term675 x x0 y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1550654 x x0 y0) (@lem1550655)). Qed.
Lemma lem1550657 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1550656 x x0 y0) (@lem1550608 x0 y0 x y h1)). Qed.
Lemma lem1550659 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550660 : term453 = term454.
Proof. exact (@lem1550659 (NUMERAL 0) term66). Qed.
Lemma lem1550661 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550662 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550663 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550662 h1) (fun h1 : term454 = True => @lem1550661)). Qed.
Lemma lem1550664 : term454 = True.
Proof. exact (EQ_MP (@lem1550663) (@lem1550661)). Qed.
Lemma lem1550665 : term453 = True.
Proof. exact (TRANS (@lem1550660) (@lem1550664)). Qed.
Lemma lem1550666 : True = term453.
Proof. exact (SYM (@lem1550665)). Qed.
Lemma lem1550667 : term453.
Proof. exact (EQ_MP (@lem1550666) (@lem0)). Qed.
Lemma lem1550668 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term487 x0 y0.
Proof. exact (conj (@lem1550667) (@lem1550657 x0 y0 x y h1)). Qed.
Lemma lem1550670 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550671 (x0 : real) (y0 : real) : term488 x0 y0.
Proof. exact (@lem1550670 term181 (term43 x0 y0)). Qed.
Lemma lem1550672 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term489 x0 y0.
Proof. exact (@lem1550671 x0 y0 (@lem1550668 x0 y0 x y h1)). Qed.
Lemma lem1550673 (x0 : real) (y0 : real) : (term490 x0 y0) = (term43 x0 y0).
Proof. exact (@lem1483460 (term43 x0 y0)). Qed.
Lemma lem1550674 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550675 (x0 : real) (y0 : real) : (term491 x0 y0) = (term46 x0 y0).
Proof. exact (MK_COMB (@lem1550674) (@lem1550673 x0 y0)). Qed.
Lemma lem1550676 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550677 (x0 : real) (y0 : real) : (term489 x0 y0) = (term48 x0 y0).
Proof. exact (MK_COMB (@lem1550675 x0 y0) (@lem1550676)). Qed.
Lemma lem1550678 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term48 x0 y0.
Proof. exact (EQ_MP (@lem1550677 x0 y0) (@lem1550672 x0 y0 x y h1)). Qed.
Lemma lem1550680 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550681 : term435 = term436.
Proof. exact (@lem1550680 (NUMERAL 0) term67). Qed.
Lemma lem1550682 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1550683 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1550684 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1550683 h1) (fun h1 : term436 = True => @lem1550682)). Qed.
Lemma lem1550685 : term436 = True.
Proof. exact (EQ_MP (@lem1550684) (@lem1550682)). Qed.
Lemma lem1550686 : term435 = True.
Proof. exact (TRANS (@lem1550681) (@lem1550685)). Qed.
Lemma lem1550687 : True = term435.
Proof. exact (SYM (@lem1550686)). Qed.
Lemma lem1550688 : term435.
Proof. exact (EQ_MP (@lem1550687) (@lem0)). Qed.
Lemma lem1550689 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term438 x y.
Proof. exact (conj (@lem1550688) (@lem1550534 x0 y0 x y h1)). Qed.
Lemma lem1550691 (x : real) (y : real) : term439 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1550692 (x : real) (y : real) : term440 x y.
Proof. exact (@lem1550691 term60 (term42 x y)). Qed.
Lemma lem1550693 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term441 x y.
Proof. exact (@lem1550692 x y (@lem1550689 x0 y0 x y h1)). Qed.
Lemma lem1550694 (x : real) (y : real) : (term442 x y) = (term443 x y).
Proof. exact (@lem1483508 x term60 (term44 y)). Qed.
Lemma lem1550695 (y : real) : (term444 y) = (term445 y).
Proof. exact (@lem1483476 term60 term59 y). Qed.
Lemma lem1550697 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550698 : term447 = term448.
Proof. exact (@lem1550697 term67 term66). Qed.
Lemma lem1550699 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1550700 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1550701 : term160 = term67.
Proof. exact (EQ_MP (@lem1550700) (@lem1550699)). Qed.
Lemma lem1550702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550703 : term158 = term60.
Proof. exact (MK_COMB (@lem1550702) (@lem1550701)). Qed.
Lemma lem1550704 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550705 : term448 = term72.
Proof. exact (MK_COMB (@lem1550704) (@lem1550703)). Qed.
Lemma lem1550706 : term447 = term72.
Proof. exact (TRANS (@lem1550698) (@lem1550705)). Qed.
Lemma lem1550707 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550708 : term449 = term74.
Proof. exact (MK_COMB (@lem1550707) (@lem1550706)). Qed.
Lemma lem1550709 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1550710 (y : real) : (term445 y) = (term169 y).
Proof. exact (MK_COMB (@lem1550708) (@lem1550709 y)). Qed.
Lemma lem1550711 (y : real) : (term444 y) = (term169 y).
Proof. exact (TRANS (@lem1550695 y) (@lem1550710 y)). Qed.
Lemma lem1550714 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1550715 (x : real) (y : real) : (term443 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1550714 x) (@lem1550711 y)). Qed.
Lemma lem1550716 (x : real) (y : real) : (term442 x y) = (term249 x y).
Proof. exact (TRANS (@lem1550694 x y) (@lem1550715 x y)). Qed.
Lemma lem1550717 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1550718 (x : real) (y : real) : (term450 x y) = (term451 x y).
Proof. exact (MK_COMB (@lem1550717) (@lem1550716 x y)). Qed.
Lemma lem1550719 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550720 (x : real) (y : real) : (term441 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1550718 x y) (@lem1550719)). Qed.
Lemma lem1550721 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term452 x y.
Proof. exact (EQ_MP (@lem1550720 x y) (@lem1550693 x0 y0 x y h1)). Qed.
Lemma lem1550723 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550724 : term453 = term454.
Proof. exact (@lem1550723 (NUMERAL 0) term66). Qed.
Lemma lem1550725 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550726 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550727 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550726 h1) (fun h1 : term454 = True => @lem1550725)). Qed.
Lemma lem1550728 : term454 = True.
Proof. exact (EQ_MP (@lem1550727) (@lem1550725)). Qed.
Lemma lem1550729 : term453 = True.
Proof. exact (TRANS (@lem1550724) (@lem1550728)). Qed.
Lemma lem1550730 : True = term453.
Proof. exact (SYM (@lem1550729)). Qed.
Lemma lem1550731 : term453.
Proof. exact (EQ_MP (@lem1550730) (@lem0)). Qed.
Lemma lem1550732 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term547 x0 y y0.
Proof. exact (conj (@lem1550731) (@lem1550538 x0 y0 x y h1)). Qed.
Lemma lem1550734 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550735 (x0 : real) (y : real) (y0 : real) : term548 x0 y y0.
Proof. exact (@lem1550734 term181 (term370 x0 y y0)). Qed.
Lemma lem1550736 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term549 x0 y y0.
Proof. exact (@lem1550735 x0 y y0 (@lem1550732 x0 y0 x y h1)). Qed.
Lemma lem1550737 (x0 : real) (y : real) (y0 : real) : (term550 x0 y y0) = (term370 x0 y y0).
Proof. exact (@lem1483460 (term370 x0 y y0)). Qed.
Lemma lem1550738 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550739 (x0 : real) (y : real) (y0 : real) : (term551 x0 y y0) = (term379 x0 y y0).
Proof. exact (MK_COMB (@lem1550738) (@lem1550737 x0 y y0)). Qed.
Lemma lem1550740 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550741 (x0 : real) (y : real) (y0 : real) : (term549 x0 y y0) = (term380 x0 y y0).
Proof. exact (MK_COMB (@lem1550739 x0 y y0) (@lem1550740)). Qed.
Lemma lem1550742 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term380 x0 y y0.
Proof. exact (EQ_MP (@lem1550741 x0 y y0) (@lem1550736 x0 y0 x y h1)). Qed.
Lemma lem1550743 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term552 x0 y0 x y.
Proof. exact (conj (@lem1550742 x0 y0 x y h1) (@lem1550721 x0 y0 x y h1)). Qed.
Lemma lem1550745 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1550746 (x0 : real) (y0 : real) (x : real) (y : real) : term553 x0 y0 x y.
Proof. exact (@lem1550745 (term370 x0 y y0) (term249 x y)). Qed.
Lemma lem1550747 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term554 x0 y0 x y.
Proof. exact (@lem1550746 x0 y0 x y (@lem1550743 x0 y0 x y h1)). Qed.
Lemma lem1550748 (x : real) (x0 : real) (y0 : real) (y : real) : (term555 x0 y0 x y) = (term556 x x0 y0 y).
Proof. exact (@lem1483484 (term163 x) (term370 x0 y y0) (term169 y)). Qed.
Lemma lem1550749 (x0 : real) (y0 : real) (y : real) : (term557 x0 y0 y) = (term558 x0 y0 y).
Proof. exact (@lem1483482 (term44 x0) (term369 y y0) (term169 y)). Qed.
Lemma lem1550750 (y : real) (y0 : real) : (term559 y0 y) = (term560 y y0).
Proof. exact (@lem1483486 (term163 y) (term169 y) (term44 y0)). Qed.
Lemma lem1550751 (y : real) : (term561 y) = (term562 y).
Proof. exact (@lem1483438 term60 term72 y). Qed.
Lemma lem1550753 (m : nat) : (term563 m) = term47.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1550754 : term564 = term47.
Proof. exact (@lem1550753 term67). Qed.
Lemma lem1550755 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550756 : term565 = term475.
Proof. exact (MK_COMB (@lem1550755) (@lem1550754)). Qed.
Lemma lem1550757 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1550758 (y : real) : (term562 y) = (term476 y).
Proof. exact (MK_COMB (@lem1550756) (@lem1550757 y)). Qed.
Lemma lem1550759 (y : real) : (term561 y) = (term476 y).
Proof. exact (TRANS (@lem1550751 y) (@lem1550758 y)). Qed.
Lemma lem1550760 (y : real) : (term476 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1550761 (y : real) : (term561 y) = term47.
Proof. exact (TRANS (@lem1550759 y) (@lem1550760 y)). Qed.
Lemma lem1550762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550763 (y : real) : (term566 y) = term236.
Proof. exact (MK_COMB (@lem1550762) (@lem1550761 y)). Qed.
Lemma lem1550764 (y0 : real) : (term44 y0) = (term44 y0).
Proof. exact (eq_refl (term44 y0)). Qed.
Lemma lem1550765 (y : real) (y0 : real) : (term560 y y0) = (term521 y0).
Proof. exact (MK_COMB (@lem1550763 y) (@lem1550764 y0)). Qed.
Lemma lem1550766 (y : real) (y0 : real) : (term559 y0 y) = (term521 y0).
Proof. exact (TRANS (@lem1550750 y y0) (@lem1550765 y y0)). Qed.
Lemma lem1550767 (y0 : real) : (term521 y0) = (term44 y0).
Proof. exact (@lem1483448 (term44 y0)). Qed.
Lemma lem1550768 (y : real) (y0 : real) : (term559 y0 y) = (term44 y0).
Proof. exact (TRANS (@lem1550766 y y0) (@lem1550767 y0)). Qed.
Lemma lem1550769 (x0 : real) : (term173 x0) = (term173 x0).
Proof. exact (eq_refl (term173 x0)). Qed.
Lemma lem1550770 (y : real) (x0 : real) (y0 : real) : (term558 x0 y0 y) = (term567 x0 y0).
Proof. exact (MK_COMB (@lem1550769 x0) (@lem1550768 y y0)). Qed.
Lemma lem1550771 (y : real) (x0 : real) (y0 : real) : (term557 x0 y0 y) = (term567 x0 y0).
Proof. exact (TRANS (@lem1550749 x0 y0 y) (@lem1550770 y x0 y0)). Qed.
Lemma lem1550772 (x : real) : (term248 x) = (term248 x).
Proof. exact (eq_refl (term248 x)). Qed.
Lemma lem1550773 (y : real) (x : real) (x0 : real) (y0 : real) : (term556 x x0 y0 y) = (term568 x x0 y0).
Proof. exact (MK_COMB (@lem1550772 x) (@lem1550771 y x0 y0)). Qed.
Lemma lem1550774 (y : real) (x : real) (x0 : real) (y0 : real) : (term555 x0 y0 x y) = (term568 x x0 y0).
Proof. exact (TRANS (@lem1550748 x x0 y0 y) (@lem1550773 y x x0 y0)). Qed.
Lemma lem1550775 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550776 (y : real) (x : real) (x0 : real) (y0 : real) : (term569 x0 y0 x y) = (term570 x x0 y0).
Proof. exact (MK_COMB (@lem1550775) (@lem1550774 y x x0 y0)). Qed.
Lemma lem1550777 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550778 (y : real) (x : real) (x0 : real) (y0 : real) : (term554 x0 y0 x y) = (term571 x x0 y0).
Proof. exact (MK_COMB (@lem1550776 y x x0 y0) (@lem1550777)). Qed.
Lemma lem1550779 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term571 x x0 y0.
Proof. exact (EQ_MP (@lem1550778 y x x0 y0) (@lem1550747 x0 y0 x y h1)). Qed.
Lemma lem1550781 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550782 : term453 = term454.
Proof. exact (@lem1550781 (NUMERAL 0) term66). Qed.
Lemma lem1550783 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550784 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550785 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550784 h1) (fun h1 : term454 = True => @lem1550783)). Qed.
Lemma lem1550786 : term454 = True.
Proof. exact (EQ_MP (@lem1550785) (@lem1550783)). Qed.
Lemma lem1550787 : term453 = True.
Proof. exact (TRANS (@lem1550782) (@lem1550786)). Qed.
Lemma lem1550788 : True = term453.
Proof. exact (SYM (@lem1550787)). Qed.
Lemma lem1550789 : term453.
Proof. exact (EQ_MP (@lem1550788) (@lem0)). Qed.
Lemma lem1550790 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term689 x x0 y0.
Proof. exact (conj (@lem1550789) (@lem1550779 x0 y0 x y h1)). Qed.
Lemma lem1550792 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550793 (x : real) (x0 : real) (y0 : real) : term690 x x0 y0.
Proof. exact (@lem1550792 term181 (term568 x x0 y0)). Qed.
Lemma lem1550794 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term691 x x0 y0.
Proof. exact (@lem1550793 x x0 y0 (@lem1550790 x0 y0 x y h1)). Qed.
Lemma lem1550795 (x : real) (x0 : real) (y0 : real) : (term692 x x0 y0) = (term568 x x0 y0).
Proof. exact (@lem1483460 (term568 x x0 y0)). Qed.
Lemma lem1550796 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550797 (x : real) (x0 : real) (y0 : real) : (term693 x x0 y0) = (term570 x x0 y0).
Proof. exact (MK_COMB (@lem1550796) (@lem1550795 x x0 y0)). Qed.
Lemma lem1550798 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550799 (x : real) (x0 : real) (y0 : real) : (term691 x x0 y0) = (term571 x x0 y0).
Proof. exact (MK_COMB (@lem1550797 x x0 y0) (@lem1550798)). Qed.
Lemma lem1550800 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term571 x x0 y0.
Proof. exact (EQ_MP (@lem1550799 x x0 y0) (@lem1550794 x0 y0 x y h1)). Qed.
Lemma lem1550802 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550803 : term435 = term436.
Proof. exact (@lem1550802 (NUMERAL 0) term67). Qed.
Lemma lem1550804 : term437 = term69.
Proof. exact (@lem912803). Qed.
Lemma lem1550805 (h1 : term437 = term69) : term436 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term69 h1). Qed.
Lemma lem1550806 : (term437 = term69) = (term436 = True).
Proof. exact (prop_ext (fun h1 : term437 = term69 => @lem1550805 h1) (fun h1 : term436 = True => @lem1550804)). Qed.
Lemma lem1550807 : term436 = True.
Proof. exact (EQ_MP (@lem1550806) (@lem1550804)). Qed.
Lemma lem1550808 : term435 = True.
Proof. exact (TRANS (@lem1550803) (@lem1550807)). Qed.
Lemma lem1550809 : True = term435.
Proof. exact (SYM (@lem1550808)). Qed.
Lemma lem1550810 : term435.
Proof. exact (EQ_MP (@lem1550809) (@lem0)). Qed.
Lemma lem1550811 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term665 x x0.
Proof. exact (conj (@lem1550810) (@lem1550533 x0 y0 x y h1)). Qed.
Lemma lem1550813 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550814 (x : real) (x0 : real) : term666 x x0.
Proof. exact (@lem1550813 term60 (term43 x x0)). Qed.
Lemma lem1550815 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term667 x x0.
Proof. exact (@lem1550814 x x0 (@lem1550811 x0 y0 x y h1)). Qed.
Lemma lem1550816 (x : real) (x0 : real) : (term668 x x0) = (term669 x x0).
Proof. exact (@lem1483508 (term44 x) term60 x0). Qed.
Lemma lem1550817 (x0 : real) : (term163 x0) = (term163 x0).
Proof. exact (eq_refl (term163 x0)). Qed.
Lemma lem1550818 (x : real) : (term444 x) = (term445 x).
Proof. exact (@lem1483476 term60 term59 x). Qed.
Lemma lem1550820 (m : nat) (n : nat) : (term446 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1550821 : term447 = term448.
Proof. exact (@lem1550820 term67 term66). Qed.
Lemma lem1550822 : term159 = term69.
Proof. exact (@lem996237 term69). Qed.
Lemma lem1550823 : (term159 = term69) = (term160 = term67).
Proof. exact (@lem1007663 term69 (BIT1 0) term69). Qed.
Lemma lem1550824 : term160 = term67.
Proof. exact (EQ_MP (@lem1550823) (@lem1550822)). Qed.
Lemma lem1550825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550826 : term158 = term60.
Proof. exact (MK_COMB (@lem1550825) (@lem1550824)). Qed.
Lemma lem1550827 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1550828 : term448 = term72.
Proof. exact (MK_COMB (@lem1550827) (@lem1550826)). Qed.
Lemma lem1550829 : term447 = term72.
Proof. exact (TRANS (@lem1550821) (@lem1550828)). Qed.
Lemma lem1550830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550831 : term449 = term74.
Proof. exact (MK_COMB (@lem1550830) (@lem1550829)). Qed.
Lemma lem1550832 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550833 (x : real) : (term445 x) = (term169 x).
Proof. exact (MK_COMB (@lem1550831) (@lem1550832 x)). Qed.
Lemma lem1550834 (x : real) : (term444 x) = (term169 x).
Proof. exact (TRANS (@lem1550818 x) (@lem1550833 x)). Qed.
Lemma lem1550835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550836 (x : real) : (term579 x) = (term164 x).
Proof. exact (MK_COMB (@lem1550835) (@lem1550834 x)). Qed.
Lemma lem1550837 (x : real) (x0 : real) : (term669 x x0) = (term165 x x0).
Proof. exact (MK_COMB (@lem1550836 x) (@lem1550817 x0)). Qed.
Lemma lem1550838 (x : real) (x0 : real) : (term668 x x0) = (term165 x x0).
Proof. exact (TRANS (@lem1550816 x x0) (@lem1550837 x x0)). Qed.
Lemma lem1550839 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550840 (x : real) (x0 : real) : (term670 x x0) = (term671 x x0).
Proof. exact (MK_COMB (@lem1550839) (@lem1550838 x x0)). Qed.
Lemma lem1550841 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550842 (x : real) (x0 : real) : (term667 x x0) = (term672 x x0).
Proof. exact (MK_COMB (@lem1550840 x x0) (@lem1550841)). Qed.
Lemma lem1550843 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term672 x x0.
Proof. exact (EQ_MP (@lem1550842 x x0) (@lem1550815 x0 y0 x y h1)). Qed.
Lemma lem1550844 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term694 x x0 y0.
Proof. exact (conj (@lem1550843 x0 y0 x y h1) (@lem1550800 x0 y0 x y h1)). Qed.
Lemma lem1550846 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1550847 (x : real) (x0 : real) (y0 : real) : term695 x x0 y0.
Proof. exact (@lem1550846 (term165 x x0) (term568 x x0 y0)). Qed.
Lemma lem1550848 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term696 x x0 y0.
Proof. exact (@lem1550847 x x0 y0 (@lem1550844 x0 y0 x y h1)). Qed.
Lemma lem1550849 (x : real) (x0 : real) (y0 : real) : (term697 x x0 y0) = (term698 x x0 y0).
Proof. exact (@lem1483480 (term169 x) (term163 x) (term163 x0) (term567 x0 y0)). Qed.
Lemma lem1550850 (x : real) : (term470 x) = (term471 x).
Proof. exact (@lem1483438 term72 term60 x). Qed.
Lemma lem1550852 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550853 : term473 = term47.
Proof. exact (@lem1550852 term67). Qed.
Lemma lem1550854 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550855 : term474 = term475.
Proof. exact (MK_COMB (@lem1550854) (@lem1550853)). Qed.
Lemma lem1550856 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1550857 (x : real) : (term471 x) = (term476 x).
Proof. exact (MK_COMB (@lem1550855) (@lem1550856 x)). Qed.
Lemma lem1550858 (x : real) : (term470 x) = (term476 x).
Proof. exact (TRANS (@lem1550850 x) (@lem1550857 x)). Qed.
Lemma lem1550859 (x : real) : (term476 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1550860 (x : real) : (term470 x) = term47.
Proof. exact (TRANS (@lem1550858 x) (@lem1550859 x)). Qed.
Lemma lem1550861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550862 (x : real) : (term477 x) = term236.
Proof. exact (MK_COMB (@lem1550861) (@lem1550860 x)). Qed.
Lemma lem1550863 (x0 : real) (y0 : real) : (term699 x0 y0) = (term700 x0 y0).
Proof. exact (@lem1483490 (term163 x0) (term44 x0) (term44 y0)). Qed.
Lemma lem1550864 (x0 : real) : (term701 x0) = (term702 x0).
Proof. exact (@lem1483438 term60 term59 x0). Qed.
Lemma lem1550867 : term703 = term181.
Proof. exact (@lem1367769 term66 term66). Qed.
Lemma lem1550868 : term182 = term69.
Proof. exact (@lem706885). Qed.
Lemma lem1550869 : (term182 = term69) = (term183 = term67).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term69). Qed.
Lemma lem1550870 : term183 = term67.
Proof. exact (EQ_MP (@lem1550869) (@lem1550868)). Qed.
Lemma lem1550871 : term67 = term183.
Proof. exact (SYM (@lem1550870)). Qed.
Lemma lem1550872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1550873 : term60 = term184.
Proof. exact (MK_COMB (@lem1550872) (@lem1550871)). Qed.
Lemma lem1550874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550875 : term684 = term704.
Proof. exact (MK_COMB (@lem1550874) (@lem1550873)). Qed.
Lemma lem1550876 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem1550877 : term705 = term703.
Proof. exact (MK_COMB (@lem1550875) (@lem1550876)). Qed.
Lemma lem1550878 : term705 = term181.
Proof. exact (TRANS (@lem1550877) (@lem1550867)). Qed.
Lemma lem1550879 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550880 : term706 = term188.
Proof. exact (MK_COMB (@lem1550879) (@lem1550878)). Qed.
Lemma lem1550881 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550882 (x0 : real) : (term702 x0) = (term189 x0).
Proof. exact (MK_COMB (@lem1550880) (@lem1550881 x0)). Qed.
Lemma lem1550883 (x0 : real) : (term701 x0) = (term189 x0).
Proof. exact (TRANS (@lem1550864 x0) (@lem1550882 x0)). Qed.
Lemma lem1550884 (x0 : real) : (term189 x0) = x0.
Proof. exact (@lem1483436 x0). Qed.
Lemma lem1550885 (x0 : real) : (term701 x0) = x0.
Proof. exact (TRANS (@lem1550883 x0) (@lem1550884 x0)). Qed.
Lemma lem1550886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550887 (x0 : real) : (term707 x0) = (real_add x0).
Proof. exact (MK_COMB (@lem1550886) (@lem1550885 x0)). Qed.
Lemma lem1550888 (y0 : real) : (term44 y0) = (term44 y0).
Proof. exact (eq_refl (term44 y0)). Qed.
Lemma lem1550889 (x0 : real) (y0 : real) : (term700 x0 y0) = (term42 x0 y0).
Proof. exact (MK_COMB (@lem1550887 x0) (@lem1550888 y0)). Qed.
Lemma lem1550890 (x0 : real) (y0 : real) : (term699 x0 y0) = (term42 x0 y0).
Proof. exact (TRANS (@lem1550863 x0 y0) (@lem1550889 x0 y0)). Qed.
Lemma lem1550891 (x : real) (x0 : real) (y0 : real) : (term698 x x0 y0) = (term644 x0 y0).
Proof. exact (MK_COMB (@lem1550862 x) (@lem1550890 x0 y0)). Qed.
Lemma lem1550892 (x : real) (x0 : real) (y0 : real) : (term697 x x0 y0) = (term644 x0 y0).
Proof. exact (TRANS (@lem1550849 x x0 y0) (@lem1550891 x x0 y0)). Qed.
Lemma lem1550893 (x0 : real) (y0 : real) : (term644 x0 y0) = (term42 x0 y0).
Proof. exact (@lem1483448 (term42 x0 y0)). Qed.
Lemma lem1550894 (x : real) (x0 : real) (y0 : real) : (term697 x x0 y0) = (term42 x0 y0).
Proof. exact (TRANS (@lem1550892 x x0 y0) (@lem1550893 x0 y0)). Qed.
Lemma lem1550895 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550896 (x : real) (x0 : real) (y0 : real) : (term708 x x0 y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1550895) (@lem1550894 x x0 y0)). Qed.
Lemma lem1550897 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550898 (x : real) (x0 : real) (y0 : real) : (term696 x x0 y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1550896 x x0 y0) (@lem1550897)). Qed.
Lemma lem1550899 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1550898 x x0 y0) (@lem1550848 x0 y0 x y h1)). Qed.
Lemma lem1550901 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550902 : term453 = term454.
Proof. exact (@lem1550901 (NUMERAL 0) term66). Qed.
Lemma lem1550903 : term455 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1550904 (h1 : term455 = (BIT1 0)) : term454 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1550905 : (term455 = (BIT1 0)) = (term454 = True).
Proof. exact (prop_ext (fun h1 : term455 = (BIT1 0) => @lem1550904 h1) (fun h1 : term454 = True => @lem1550903)). Qed.
Lemma lem1550906 : term454 = True.
Proof. exact (EQ_MP (@lem1550905) (@lem1550903)). Qed.
Lemma lem1550907 : term453 = True.
Proof. exact (TRANS (@lem1550902) (@lem1550906)). Qed.
Lemma lem1550908 : True = term453.
Proof. exact (SYM (@lem1550907)). Qed.
Lemma lem1550909 : term453.
Proof. exact (EQ_MP (@lem1550908) (@lem0)). Qed.
Lemma lem1550910 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term525 x0 y0.
Proof. exact (conj (@lem1550909) (@lem1550899 x0 y0 x y h1)). Qed.
Lemma lem1550912 (x : real) (y : real) : term457 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1550913 (x0 : real) (y0 : real) : term526 x0 y0.
Proof. exact (@lem1550912 term181 (term42 x0 y0)). Qed.
Lemma lem1550914 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term527 x0 y0.
Proof. exact (@lem1550913 x0 y0 (@lem1550910 x0 y0 x y h1)). Qed.
Lemma lem1550915 (x0 : real) (y0 : real) : (term528 x0 y0) = (term42 x0 y0).
Proof. exact (@lem1483460 (term42 x0 y0)). Qed.
Lemma lem1550916 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550917 (x0 : real) (y0 : real) : (term529 x0 y0) = (term523 x0 y0).
Proof. exact (MK_COMB (@lem1550916) (@lem1550915 x0 y0)). Qed.
Lemma lem1550918 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550919 (x0 : real) (y0 : real) : (term527 x0 y0) = (term524 x0 y0).
Proof. exact (MK_COMB (@lem1550917 x0 y0) (@lem1550918)). Qed.
Lemma lem1550920 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term524 x0 y0.
Proof. exact (EQ_MP (@lem1550919 x0 y0) (@lem1550914 x0 y0 x y h1)). Qed.
Lemma lem1550921 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term530 x0 y0.
Proof. exact (conj (@lem1550920 x0 y0 x y h1) (@lem1550678 x0 y0 x y h1)). Qed.
Lemma lem1550923 (x : real) (y : real) : term531 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1550924 (x0 : real) (y0 : real) : term532 x0 y0.
Proof. exact (@lem1550923 (term42 x0 y0) (term43 x0 y0)). Qed.
Lemma lem1550925 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term533 x0 y0.
Proof. exact (@lem1550924 x0 y0 (@lem1550921 x0 y0 x y h1)). Qed.
Lemma lem1550926 (x0 : real) (y0 : real) : (term534 x0 y0) = (term535 x0 y0).
Proof. exact (@lem1483480 x0 (term44 x0) (term44 y0) y0). Qed.
Lemma lem1550927 (x0 : real) : (term536 x0) = (term537 x0).
Proof. exact (@lem1483442 term59 x0). Qed.
Lemma lem1550929 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550930 : term538 = term47.
Proof. exact (@lem1550929 term66). Qed.
Lemma lem1550931 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550932 : term539 = term475.
Proof. exact (MK_COMB (@lem1550931) (@lem1550930)). Qed.
Lemma lem1550933 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem1550934 (x0 : real) : (term537 x0) = (term476 x0).
Proof. exact (MK_COMB (@lem1550932) (@lem1550933 x0)). Qed.
Lemma lem1550935 (x0 : real) : (term536 x0) = (term476 x0).
Proof. exact (TRANS (@lem1550927 x0) (@lem1550934 x0)). Qed.
Lemma lem1550936 (x0 : real) : (term476 x0) = term47.
Proof. exact (@lem1483446 x0). Qed.
Lemma lem1550937 (x0 : real) : (term536 x0) = term47.
Proof. exact (TRANS (@lem1550935 x0) (@lem1550936 x0)). Qed.
Lemma lem1550938 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1550939 (x0 : real) : (term540 x0) = term236.
Proof. exact (MK_COMB (@lem1550938) (@lem1550937 x0)). Qed.
Lemma lem1550940 (y0 : real) : (term541 y0) = (term537 y0).
Proof. exact (@lem1483440 term59 y0). Qed.
Lemma lem1550942 (m : nat) : (term472 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1550943 : term538 = term47.
Proof. exact (@lem1550942 term66). Qed.
Lemma lem1550944 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1550945 : term539 = term475.
Proof. exact (MK_COMB (@lem1550944) (@lem1550943)). Qed.
Lemma lem1550946 (y0 : real) : y0 = y0.
Proof. exact (eq_refl y0). Qed.
Lemma lem1550947 (y0 : real) : (term537 y0) = (term476 y0).
Proof. exact (MK_COMB (@lem1550945) (@lem1550946 y0)). Qed.
Lemma lem1550948 (y0 : real) : (term541 y0) = (term476 y0).
Proof. exact (TRANS (@lem1550940 y0) (@lem1550947 y0)). Qed.
Lemma lem1550949 (y0 : real) : (term476 y0) = term47.
Proof. exact (@lem1483446 y0). Qed.
Lemma lem1550950 (y0 : real) : (term541 y0) = term47.
Proof. exact (TRANS (@lem1550948 y0) (@lem1550949 y0)). Qed.
Lemma lem1550951 (x0 : real) (y0 : real) : (term535 x0 y0) = term542.
Proof. exact (MK_COMB (@lem1550939 x0) (@lem1550950 y0)). Qed.
Lemma lem1550952 (x0 : real) (y0 : real) : (term534 x0 y0) = term542.
Proof. exact (TRANS (@lem1550926 x0 y0) (@lem1550951 x0 y0)). Qed.
Lemma lem1550953 : term542 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1550954 (x0 : real) (y0 : real) : (term534 x0 y0) = term47.
Proof. exact (TRANS (@lem1550952 x0 y0) (@lem1550953)). Qed.
Lemma lem1550955 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1550956 (x0 : real) (y0 : real) : (term543 x0 y0) = term544.
Proof. exact (MK_COMB (@lem1550955) (@lem1550954 x0 y0)). Qed.
Lemma lem1550957 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1550958 (x0 : real) (y0 : real) : (term533 x0 y0) = term545.
Proof. exact (MK_COMB (@lem1550956 x0 y0) (@lem1550957)). Qed.
Lemma lem1550959 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : term545.
Proof. exact (EQ_MP (@lem1550958 x0 y0) (@lem1550925 x0 y0 x y h1)). Qed.
Lemma lem1550961 (n : nat) (m : nat) : (term434 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1550962 : term545 = term546.
Proof. exact (@lem1550961 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1550963 : term546 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1550964 : term545 = False.
Proof. exact (TRANS (@lem1550962) (@lem1550963)). Qed.
Lemma lem1550965 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term390 x0 y0 x y) : False.
Proof. exact (EQ_MP (@lem1550964) (@lem1550959 x0 y0 x y h1)). Qed.
Lemma lem1550966 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term392 x0 y0 x y) : False.
Proof. exact (or_elim (@lem1550166 x0 y0 x y h1) (fun h0 : term353 x0 y0 x y => @lem1550528 x0 y0 x y h0) (fun h0 : term390 x0 y0 x y => @lem1550965 x0 y0 x y h0)). Qed.
Lemma lem1550967 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term433 x0 y0 x y) : False.
Proof. exact (or_elim (@lem1549427 x0 y0 x y h1) (fun h0 : term431 x0 y0 x y => @lem1550165 x0 y0 x y h0) (fun h0 : term392 x0 y0 x y => @lem1550966 x0 y0 x y h0)). Qed.
Lemma lem1550968 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term106 x0 y0 x y) : term106 x0 y0 x y.
Proof. exact (h1). Qed.
Lemma lem1550969 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term106 x0 y0 x y) : term433 x0 y0 x y.
Proof. exact (EQ_MP (@lem1549426 x0 y0 x y) (@lem1550968 x0 y0 x y h1)). Qed.
Lemma lem1550970 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term106 x0 y0 x y) : (term433 x0 y0 x y) = False.
Proof. exact (prop_ext (fun h2 : term433 x0 y0 x y => @lem1550967 x0 y0 x y h2) (fun h2 : False => @lem1550969 x0 y0 x y h1)). Qed.
Lemma lem1550971 (x0 : real) (y0 : real) (x : real) (y : real) (h1 : term106 x0 y0 x y) : False.
Proof. exact (EQ_MP (@lem1550970 x0 y0 x y h1) (@lem1550969 x0 y0 x y h1)). Qed.
Lemma lem1550972 (x0 : real) (y0 : real) (x : real) (h1 : term108 x0 y0 x) : term108 x0 y0 x.
Proof. exact (h1). Qed.
Lemma lem1550973 (x0 : real) (y0 : real) (x : real) (h1 : term108 x0 y0 x) : False.
Proof. exact (ex_elim (@lem1550972 x0 y0 x h1) (fun y : real => fun h0 : term107 x0 y0 x y => @lem1550971 x0 y0 x y h0)). Qed.
Lemma lem1550974 (x0 : real) (x : real) (h1 : term110 x0 x) : term110 x0 x.
Proof. exact (h1). Qed.
Lemma lem1550975 (x0 : real) (x : real) (h1 : term110 x0 x) : False.
Proof. exact (ex_elim (@lem1550974 x0 x h1) (fun y0 : real => fun h0 : term109 x0 x y0 => @lem1550973 x0 y0 x h0)). Qed.
Lemma lem1550976 (x0 : real) (h1 : term112 x0) : term112 x0.
Proof. exact (h1). Qed.
Lemma lem1550977 (x0 : real) (h1 : term112 x0) : False.
Proof. exact (ex_elim (@lem1550976 x0 h1) (fun x : real => fun h0 : term111 x0 x => @lem1550975 x0 x h0)). Qed.
Lemma lem1550978 (h1 : term114) : term114.
Proof. exact (h1). Qed.
Lemma lem1550979 (h1 : term114) : False.
Proof. exact (ex_elim (@lem1550978 h1) (fun x0 : real => fun h0 : term113 x0 => @lem1550977 x0 h0)). Qed.
Lemma lem1550980 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1550981 (h1 : term32) : term114.
Proof. exact (EQ_MP (@lem1548357) (@lem1550980 h1)). Qed.
Lemma lem1550982 (h1 : term32) : term114 = False.
Proof. exact (prop_ext (fun h2 : term114 => @lem1550979 h2) (fun h2 : False => @lem1550981 h1)). Qed.
Lemma lem1550983 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1550982 h1) (@lem1550981 h1)). Qed.
Lemma lem1550984 : term709.
Proof. exact (fun h0 : term32 => @lem1550983 h0). Qed.
Lemma lem1550985 : term710.
Proof. exact (@lem1386578 term711). Qed.
Lemma lem1550986 : term711.
Proof. exact (@lem1550985 (@lem1550984)). Qed.
