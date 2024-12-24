Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_INV2_term_abbrevs.
Require Import REAL_LT_MUL_spec.
Require Import REAL_LT_RCANCEL_IMP_spec.
Require Import REAL_MUL_RID_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1338712_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1340174_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1631096 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1631097 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1631096 x y z h1)). Qed.
Lemma lem1631098 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1631099 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1631098 x y z h1)). Qed.
Lemma lem1631100 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1631097 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1631099 x y z h1)). Qed.
Lemma lem1631101 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1631100 x y z)). Qed.
Lemma lem1631102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1631103 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1631102) (@lem1631101 x y)). Qed.
Lemma lem1631104 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1631103 x y)). Qed.
Lemma lem1631105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1631106 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1631105) (@lem1631104 x)). Qed.
Lemma lem1631107 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1631106 x)). Qed.
Lemma lem1631108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1631109 : term12 = term13.
Proof. exact (MK_COMB (@lem1631108) (@lem1631107)). Qed.
Lemma lem1631110 : term13.
Proof. exact (EQ_MP (@lem1631109) (@lem1338912)). Qed.
Lemma lem1631111 (x : real) : term14 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1631112 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1631113 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1631112 x) (@lem1631111 x)). Qed.
Lemma lem1631114 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1631113 x y). Qed.
Lemma lem1631115 (y : real) (x : real) : (term16 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1631117 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1631118 (x : real) (h1 : term17) : term18 x.
Proof. exact (@lem1631117 h1 x). Qed.
Lemma lem1631119 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1631120 (x : real) (h1 : term17) : term19 x.
Proof. exact (EQ_MP (@lem1631119 x) (@lem1631118 x h1)). Qed.
Lemma lem1631121 (x : real) (h1 : term20 x) : term20 x.
Proof. exact (h1). Qed.
Lemma lem1631122 (x : real) (h1 : term17) (h2 : term20 x) : (term21 x) = term22.
Proof. exact (@lem1631120 x h1 (@lem1631121 x h2)). Qed.
Lemma lem1631123 (x : real) (h1 : term20 x) : term23 x.
Proof. exact (fun h0 : term17 => @lem1631122 x h0 h1). Qed.
Lemma lem1631124 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1631125 (x : real) (h1 : term17) (h2 : term20 x) : (term21 x) = term22.
Proof. exact (@lem1631123 x h2 (@lem1631124 h1)). Qed.
Lemma lem1631126 (x : real) (h1 : term17) : term19 x.
Proof. exact (fun h0 : term20 x => @lem1631125 x h1 h0). Qed.
Lemma lem1631127 (h1 : term17) : term17.
Proof. exact (fun x : real => @lem1631126 x h1). Qed.
Lemma lem1631128 : term24.
Proof. exact (fun h0 : term17 => @lem1631127 h0). Qed.
Lemma lem1631129 : term17.
Proof. exact (@lem1631128 (@lem1340174)). Qed.
Lemma lem1631130 (x : real) : term18 x.
Proof. exact (@lem1631129 x). Qed.
Lemma lem1631131 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1631133 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1631134 (x : real) (h1 : term25) : term26 x.
Proof. exact (@lem1631133 h1 x). Qed.
Lemma lem1631135 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1631136 (x : real) (h1 : term25) : term27 x.
Proof. exact (EQ_MP (@lem1631135 x) (@lem1631134 x h1)). Qed.
Lemma lem1631137 (x : real) (y : real) (h1 : term25) : term28 x y.
Proof. exact (@lem1631136 x h1 y). Qed.
Lemma lem1631138 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1631139 (x : real) (y : real) (h1 : term25) : term29 x y.
Proof. exact (EQ_MP (@lem1631138 x y) (@lem1631137 x y h1)). Qed.
Lemma lem1631140 (x : real) (y : real) (h1 : term30 x y) : term30 x y.
Proof. exact (h1). Qed.
Lemma lem1631141 (x : real) (y : real) (h1 : term25) (h2 : term30 x y) : term31 x y.
Proof. exact (@lem1631139 x y h1 (@lem1631140 x y h2)). Qed.
Lemma lem1631142 (x : real) (y : real) (h1 : term30 x y) : term32 x y.
Proof. exact (fun h0 : term25 => @lem1631141 x y h0 h1). Qed.
Lemma lem1631143 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1631144 (x : real) (y : real) (h1 : term25) (h2 : term30 x y) : term31 x y.
Proof. exact (@lem1631142 x y h2 (@lem1631143 h1)). Qed.
Lemma lem1631145 (x : real) (y : real) (h1 : term25) : term29 x y.
Proof. exact (fun h0 : term30 x y => @lem1631144 x y h1 h0). Qed.
Lemma lem1631146 (x : real) (h1 : term25) : term27 x.
Proof. exact (fun y : real => @lem1631145 x y h1). Qed.
Lemma lem1631147 (h1 : term25) : term25.
Proof. exact (fun x : real => @lem1631146 x h1). Qed.
Lemma lem1631148 : term33.
Proof. exact (fun h0 : term25 => @lem1631147 h0). Qed.
Lemma lem1631149 : term25.
Proof. exact (@lem1631148 (@lem1487565)). Qed.
Lemma lem1631150 (x : real) : term26 x.
Proof. exact (@lem1631149 x). Qed.
Lemma lem1631151 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1631152 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1631151 x) (@lem1631150 x)). Qed.
Lemma lem1631153 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1631152 x y). Qed.
Lemma lem1631154 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1631156 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1631157 (x : real) (h1 : term34) : term35 x.
Proof. exact (@lem1631156 h1 x). Qed.
Lemma lem1631158 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1631159 (x : real) (h1 : term34) : term36 x.
Proof. exact (EQ_MP (@lem1631158 x) (@lem1631157 x h1)). Qed.
Lemma lem1631160 (x : real) (y : real) (h1 : term34) : term37 x y.
Proof. exact (@lem1631159 x h1 y). Qed.
Lemma lem1631161 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1631162 (x : real) (y : real) (h1 : term34) : term38 x y.
Proof. exact (EQ_MP (@lem1631161 x y) (@lem1631160 x y h1)). Qed.
Lemma lem1631163 (x : real) (y : real) (z : real) (h1 : term34) : term39 x y z.
Proof. exact (@lem1631162 x y h1 z). Qed.
Lemma lem1631164 (z : real) (x : real) (y : real) : (term39 x y z) = (term40 z x y).
Proof. exact (eq_refl (term39 x y z)). Qed.
Lemma lem1631165 (z : real) (x : real) (y : real) (h1 : term34) : term40 z x y.
Proof. exact (EQ_MP (@lem1631164 z x y) (@lem1631163 x y z h1)). Qed.
Lemma lem1631166 (x : real) (y : real) (z : real) (h1 : term41 x y z) : term41 x y z.
Proof. exact (h1). Qed.
Lemma lem1631167 (x : real) (y : real) (z : real) (h1 : term34) (h2 : term41 x y z) : real_lt x y.
Proof. exact (@lem1631165 z x y h1 (@lem1631166 x y z h2)). Qed.
Lemma lem1631168 (x : real) (y : real) (z : real) (h1 : term41 x y z) : term42 x y.
Proof. exact (fun h0 : term34 => @lem1631167 x y z h0 h1). Qed.
Lemma lem1631169 (x : real) (y : real) (h1 : term43 x y) : term43 x y.
Proof. exact (h1). Qed.
Lemma lem1631170 (x : real) (y : real) (h1 : term43 x y) : term42 x y.
Proof. exact (ex_elim (@lem1631169 x y h1) (fun z : real => fun h0 : term44 x y z => @lem1631168 x y z h0)). Qed.
Lemma lem1631171 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1631172 (x : real) (y : real) (h1 : term34) (h2 : term43 x y) : real_lt x y.
Proof. exact (@lem1631170 x y h2 (@lem1631171 h1)). Qed.
Lemma lem1631173 (x : real) (y : real) (h1 : term34) : term45 x y.
Proof. exact (fun h0 : term43 x y => @lem1631172 x y h1 h0). Qed.
Lemma lem1631174 (x : real) (h1 : term34) : term46 x.
Proof. exact (fun y : real => @lem1631173 x y h1). Qed.
Lemma lem1631175 (h1 : term34) : term47.
Proof. exact (fun x : real => @lem1631174 x h1). Qed.
Lemma lem1631176 : term48.
Proof. exact (fun h0 : term34 => @lem1631175 h0). Qed.
Lemma lem1631177 : term47.
Proof. exact (@lem1631176 (@lem1598629)). Qed.
Lemma lem1631178 (x : real) : term49 x.
Proof. exact (@lem1631177 x). Qed.
Lemma lem1631179 (x : real) : (term49 x) = (term46 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1631180 (x : real) : term46 x.
Proof. exact (EQ_MP (@lem1631179 x) (@lem1631178 x)). Qed.
Lemma lem1631181 (x : real) (y : real) : term50 x y.
Proof. exact (@lem1631180 x y). Qed.
Lemma lem1631182 (x : real) (y : real) : (term50 x y) = (term45 x y).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1631184 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1631185 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1631186 (x : real) (h1 : term52 x) : term52 x.
Proof. exact (h1). Qed.
Lemma lem1631188 (x : real) (y : real) : term45 x y.
Proof. exact (EQ_MP (@lem1631182 x y) (@lem1631181 x y)). Qed.
Lemma lem1631189 (y : real) (x : real) : term53 y x.
Proof. exact (@lem1631188 (real_inv y) (real_inv x)). Qed.
Lemma lem1631191 (x : real) (y : real) : term29 x y.
Proof. exact (EQ_MP (@lem1631154 x y) (@lem1631153 x y)). Qed.
Lemma lem1631192 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term54 y x.
Proof. exact (conj (@lem1631185 x y h1) (@lem1631186 x h2)). Qed.
Lemma lem1631213 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem17045 (term52 x) (term52 y)). Qed.
Lemma lem1631215 (y : real) (x : real) : (term57 y x) = (term57 y x).
Proof. exact (eq_refl (term57 y x)). Qed.
Lemma lem1631216 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1631215 y x) (@lem1631213 x y)). Qed.
Lemma lem1631217 (x : real) (y : real) : (term60 x y) = (term58 x y).
Proof. exact (@lem17362 (term54 y x) (term30 x y)). Qed.
Lemma lem1631237 (x : real) (y : real) : (term60 x y) = (term59 x y).
Proof. exact (TRANS (@lem1631217 x y) (@lem1631216 x y)). Qed.
Lemma lem1631238 (y : real) (x : real) : (real_lt x y) = (term61 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1631244 (y : real) (x : real) : (real_sub y x) = (term62 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1631249 (x : real) (y : real) : (term62 y x) = (term63 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1631251 (x : real) (y : real) : (real_sub y x) = (term63 x y).
Proof. exact (TRANS (@lem1631244 y x) (@lem1631249 x y)). Qed.
Lemma lem1631252 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631253 (x : real) (y : real) : (term65 y x) = (term66 x y).
Proof. exact (MK_COMB (@lem1631252) (@lem1631251 x y)). Qed.
Lemma lem1631254 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631255 (x : real) (y : real) : (term61 y x) = (term68 x y).
Proof. exact (MK_COMB (@lem1631253 x y) (@lem1631254)). Qed.
Lemma lem1631256 (x : real) (y : real) : (real_lt x y) = (term68 x y).
Proof. exact (TRANS (@lem1631238 y x) (@lem1631255 x y)). Qed.
Lemma lem1631257 (x : real) : (term52 x) = (term69 x).
Proof. exact (@lem1483521 x term67). Qed.
Lemma lem1631263 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1483519 x term67). Qed.
Lemma lem1631265 (x : nat) : (term72 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1631266 : term73 = term67.
Proof. exact (@lem1631265 term74). Qed.
Lemma lem1631267 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1631268 (x : real) : (term71 x) = (term75 x).
Proof. exact (MK_COMB (@lem1631267 x) (@lem1631266)). Qed.
Lemma lem1631269 (x : real) : (term75 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1631270 (x : real) : (term71 x) = x.
Proof. exact (TRANS (@lem1631268 x) (@lem1631269 x)). Qed.
Lemma lem1631272 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1631263 x) (@lem1631270 x)). Qed.
Lemma lem1631273 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631274 (x : real) : (term76 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631273) (@lem1631272 x)). Qed.
Lemma lem1631275 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631276 (x : real) : (term69 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631274 x) (@lem1631275)). Qed.
Lemma lem1631277 (x : real) : (term52 x) = (term77 x).
Proof. exact (TRANS (@lem1631257 x) (@lem1631276 x)). Qed.
Lemma lem1631278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631279 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1631278) (@lem1631256 x y)). Qed.
Lemma lem1631280 (y : real) (x : real) : (term54 y x) = (term80 y x).
Proof. exact (MK_COMB (@lem1631279 x y) (@lem1631277 x)). Qed.
Lemma lem1631281 (x : real) : (term81 x) = (term82 x).
Proof. exact (@lem1483531 term67 x). Qed.
Lemma lem1631287 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1483519 term67 x). Qed.
Lemma lem1631292 (x : real) : (term84 x) = (term64 x).
Proof. exact (@lem1483448 (term64 x)). Qed.
Lemma lem1631294 (x : real) : (term83 x) = (term64 x).
Proof. exact (TRANS (@lem1631287 x) (@lem1631292 x)). Qed.
Lemma lem1631295 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1631296 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem1631295) (@lem1631294 x)). Qed.
Lemma lem1631297 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631298 (x : real) : (term82 x) = (term87 x).
Proof. exact (MK_COMB (@lem1631296 x) (@lem1631297)). Qed.
Lemma lem1631299 (x : real) : (term81 x) = (term87 x).
Proof. exact (TRANS (@lem1631281 x) (@lem1631298 x)). Qed.
Lemma lem1631300 (y : real) : (term81 y) = (term82 y).
Proof. exact (@lem1483531 term67 y). Qed.
Lemma lem1631306 (y : real) : (term83 y) = (term84 y).
Proof. exact (@lem1483519 term67 y). Qed.
Lemma lem1631311 (y : real) : (term84 y) = (term64 y).
Proof. exact (@lem1483448 (term64 y)). Qed.
Lemma lem1631313 (y : real) : (term83 y) = (term64 y).
Proof. exact (TRANS (@lem1631306 y) (@lem1631311 y)). Qed.
Lemma lem1631314 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1631315 (y : real) : (term85 y) = (term86 y).
Proof. exact (MK_COMB (@lem1631314) (@lem1631313 y)). Qed.
Lemma lem1631316 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631317 (y : real) : (term82 y) = (term87 y).
Proof. exact (MK_COMB (@lem1631315 y) (@lem1631316)). Qed.
Lemma lem1631318 (y : real) : (term81 y) = (term87 y).
Proof. exact (TRANS (@lem1631300 y) (@lem1631317 y)). Qed.
Lemma lem1631319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1631320 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1631319) (@lem1631299 x)). Qed.
Lemma lem1631321 (x : real) (y : real) : (term56 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1631320 x) (@lem1631318 y)). Qed.
Lemma lem1631322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631323 (y : real) (x : real) : (term57 y x) = (term91 y x).
Proof. exact (MK_COMB (@lem1631322) (@lem1631280 y x)). Qed.
Lemma lem1631324 (x : real) (y : real) : (term59 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1631323 y x) (@lem1631321 x y)). Qed.
Lemma lem1631331 (x : real) (y : real) : (term60 x y) = (term92 x y).
Proof. exact (TRANS (@lem1631237 x y) (@lem1631324 x y)). Qed.
Lemma lem1631354 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (@lem19158 (term87 x) (term80 y x) (term87 y)). Qed.
Lemma lem1631355 (x : real) (y : real) : (term60 x y) = (term93 x y).
Proof. exact (TRANS (@lem1631331 x y) (@lem1631354 x y)). Qed.
Lemma lem1631365 (x : real) (y : real) (h1 : term93 x y) : term93 x y.
Proof. exact (h1). Qed.
Lemma lem1631366 (y : real) (x : real) (h1 : term94 y x) : term94 y x.
Proof. exact (h1). Qed.
Lemma lem1631367 (y : real) (x : real) (h1 : term94 y x) : term87 x.
Proof. exact (proj2 (@lem1631366 y x h1)). Qed.
Lemma lem1631368 (y : real) (x : real) (h1 : term94 y x) : term80 y x.
Proof. exact (proj1 (@lem1631366 y x h1)). Qed.
Lemma lem1631369 (y : real) (x : real) (h1 : term94 y x) : term77 x.
Proof. exact (proj2 (@lem1631368 y x h1)). Qed.
Lemma lem1631372 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631373 : term96 = term97.
Proof. exact (@lem1631372 (NUMERAL 0) term74). Qed.
Lemma lem1631374 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631375 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631376 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631375 h1) (fun h1 : term97 = True => @lem1631374)). Qed.
Lemma lem1631377 : term97 = True.
Proof. exact (EQ_MP (@lem1631376) (@lem1631374)). Qed.
Lemma lem1631378 : term96 = True.
Proof. exact (TRANS (@lem1631373) (@lem1631377)). Qed.
Lemma lem1631379 : True = term96.
Proof. exact (SYM (@lem1631378)). Qed.
Lemma lem1631380 : term96.
Proof. exact (EQ_MP (@lem1631379) (@lem0)). Qed.
Lemma lem1631381 (y : real) (x : real) (h1 : term94 y x) : term99 x.
Proof. exact (conj (@lem1631380) (@lem1631367 y x h1)). Qed.
Lemma lem1631383 (x : real) (y : real) : term100 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1631384 (x : real) : term101 x.
Proof. exact (@lem1631383 term22 (term64 x)). Qed.
Lemma lem1631385 (y : real) (x : real) (h1 : term94 y x) : term102 x.
Proof. exact (@lem1631384 x (@lem1631381 y x h1)). Qed.
Lemma lem1631386 (x : real) : (term103 x) = (term64 x).
Proof. exact (@lem1483460 (term64 x)). Qed.
Lemma lem1631387 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1631388 (x : real) : (term104 x) = (term86 x).
Proof. exact (MK_COMB (@lem1631387) (@lem1631386 x)). Qed.
Lemma lem1631389 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631390 (x : real) : (term102 x) = (term87 x).
Proof. exact (MK_COMB (@lem1631388 x) (@lem1631389)). Qed.
Lemma lem1631391 (y : real) (x : real) (h1 : term94 y x) : term87 x.
Proof. exact (EQ_MP (@lem1631390 x) (@lem1631385 y x h1)). Qed.
Lemma lem1631393 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631394 : term96 = term97.
Proof. exact (@lem1631393 (NUMERAL 0) term74). Qed.
Lemma lem1631395 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631396 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631397 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631396 h1) (fun h1 : term97 = True => @lem1631395)). Qed.
Lemma lem1631398 : term97 = True.
Proof. exact (EQ_MP (@lem1631397) (@lem1631395)). Qed.
Lemma lem1631399 : term96 = True.
Proof. exact (TRANS (@lem1631394) (@lem1631398)). Qed.
Lemma lem1631400 : True = term96.
Proof. exact (SYM (@lem1631399)). Qed.
Lemma lem1631401 : term96.
Proof. exact (EQ_MP (@lem1631400) (@lem0)). Qed.
Lemma lem1631402 (y : real) (x : real) (h1 : term94 y x) : term105 x.
Proof. exact (conj (@lem1631401) (@lem1631369 y x h1)). Qed.
Lemma lem1631404 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631405 (x : real) : term107 x.
Proof. exact (@lem1631404 term22 x). Qed.
Lemma lem1631406 (y : real) (x : real) (h1 : term94 y x) : term108 x.
Proof. exact (@lem1631405 x (@lem1631402 y x h1)). Qed.
Lemma lem1631407 (x : real) : (term109 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1631408 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631409 (x : real) : (term110 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631408) (@lem1631407 x)). Qed.
Lemma lem1631410 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631411 (x : real) : (term108 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631409 x) (@lem1631410)). Qed.
Lemma lem1631412 (y : real) (x : real) (h1 : term94 y x) : term77 x.
Proof. exact (EQ_MP (@lem1631411 x) (@lem1631406 y x h1)). Qed.
Lemma lem1631413 (y : real) (x : real) (h1 : term94 y x) : term111 x.
Proof. exact (conj (@lem1631412 y x h1) (@lem1631391 y x h1)). Qed.
Lemma lem1631415 (x : real) (y : real) : term112 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1631416 (x : real) : term113 x.
Proof. exact (@lem1631415 x (term64 x)). Qed.
Lemma lem1631417 (y : real) (x : real) (h1 : term94 y x) : term114 x.
Proof. exact (@lem1631416 x (@lem1631413 y x h1)). Qed.
Lemma lem1631418 (x : real) : (term115 x) = (term116 x).
Proof. exact (@lem1483442 term117 x). Qed.
Lemma lem1631420 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1631421 : term119 = term67.
Proof. exact (@lem1631420 term74). Qed.
Lemma lem1631422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1631423 : term120 = term121.
Proof. exact (MK_COMB (@lem1631422) (@lem1631421)). Qed.
Lemma lem1631424 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1631425 (x : real) : (term116 x) = (term122 x).
Proof. exact (MK_COMB (@lem1631423) (@lem1631424 x)). Qed.
Lemma lem1631426 (x : real) : (term115 x) = (term122 x).
Proof. exact (TRANS (@lem1631418 x) (@lem1631425 x)). Qed.
Lemma lem1631427 (x : real) : (term122 x) = term67.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1631428 (x : real) : (term115 x) = term67.
Proof. exact (TRANS (@lem1631426 x) (@lem1631427 x)). Qed.
Lemma lem1631429 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631430 (x : real) : (term123 x) = term124.
Proof. exact (MK_COMB (@lem1631429) (@lem1631428 x)). Qed.
Lemma lem1631431 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631432 (x : real) : (term114 x) = term125.
Proof. exact (MK_COMB (@lem1631430 x) (@lem1631431)). Qed.
Lemma lem1631433 (y : real) (x : real) (h1 : term94 y x) : term125.
Proof. exact (EQ_MP (@lem1631432 x) (@lem1631417 y x h1)). Qed.
Lemma lem1631435 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631436 : term125 = term126.
Proof. exact (@lem1631435 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1631437 : term126 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1631438 : term125 = False.
Proof. exact (TRANS (@lem1631436) (@lem1631437)). Qed.
Lemma lem1631439 (y : real) (x : real) (h1 : term94 y x) : False.
Proof. exact (EQ_MP (@lem1631438) (@lem1631433 y x h1)). Qed.
Lemma lem1631440 (x : real) (y : real) (h1 : term127 x y) : term127 x y.
Proof. exact (h1). Qed.
Lemma lem1631441 (x : real) (y : real) (h1 : term127 x y) : term87 y.
Proof. exact (proj2 (@lem1631440 x y h1)). Qed.
Lemma lem1631442 (x : real) (y : real) (h1 : term127 x y) : term80 y x.
Proof. exact (proj1 (@lem1631440 x y h1)). Qed.
Lemma lem1631443 (x : real) (y : real) (h1 : term127 x y) : term77 x.
Proof. exact (proj2 (@lem1631442 x y h1)). Qed.
Lemma lem1631444 (x : real) (y : real) (h1 : term127 x y) : term68 x y.
Proof. exact (proj1 (@lem1631442 x y h1)). Qed.
Lemma lem1631446 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631447 : term96 = term97.
Proof. exact (@lem1631446 (NUMERAL 0) term74). Qed.
Lemma lem1631448 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631449 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631450 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631449 h1) (fun h1 : term97 = True => @lem1631448)). Qed.
Lemma lem1631451 : term97 = True.
Proof. exact (EQ_MP (@lem1631450) (@lem1631448)). Qed.
Lemma lem1631452 : term96 = True.
Proof. exact (TRANS (@lem1631447) (@lem1631451)). Qed.
Lemma lem1631453 : True = term96.
Proof. exact (SYM (@lem1631452)). Qed.
Lemma lem1631454 : term96.
Proof. exact (EQ_MP (@lem1631453) (@lem0)). Qed.
Lemma lem1631455 (x : real) (y : real) (h1 : term127 x y) : term105 x.
Proof. exact (conj (@lem1631454) (@lem1631443 x y h1)). Qed.
Lemma lem1631457 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631458 (x : real) : term107 x.
Proof. exact (@lem1631457 term22 x). Qed.
Lemma lem1631459 (x : real) (y : real) (h1 : term127 x y) : term108 x.
Proof. exact (@lem1631458 x (@lem1631455 x y h1)). Qed.
Lemma lem1631460 (x : real) : (term109 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1631461 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631462 (x : real) : (term110 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631461) (@lem1631460 x)). Qed.
Lemma lem1631463 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631464 (x : real) : (term108 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631462 x) (@lem1631463)). Qed.
Lemma lem1631465 (x : real) (y : real) (h1 : term127 x y) : term77 x.
Proof. exact (EQ_MP (@lem1631464 x) (@lem1631459 x y h1)). Qed.
Lemma lem1631467 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631468 : term96 = term97.
Proof. exact (@lem1631467 (NUMERAL 0) term74). Qed.
Lemma lem1631469 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631470 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631471 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631470 h1) (fun h1 : term97 = True => @lem1631469)). Qed.
Lemma lem1631472 : term97 = True.
Proof. exact (EQ_MP (@lem1631471) (@lem1631469)). Qed.
Lemma lem1631473 : term96 = True.
Proof. exact (TRANS (@lem1631468) (@lem1631472)). Qed.
Lemma lem1631474 : True = term96.
Proof. exact (SYM (@lem1631473)). Qed.
Lemma lem1631475 : term96.
Proof. exact (EQ_MP (@lem1631474) (@lem0)). Qed.
Lemma lem1631476 (x : real) (y : real) (h1 : term127 x y) : term99 y.
Proof. exact (conj (@lem1631475) (@lem1631441 x y h1)). Qed.
Lemma lem1631478 (x : real) (y : real) : term100 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1631479 (y : real) : term101 y.
Proof. exact (@lem1631478 term22 (term64 y)). Qed.
Lemma lem1631480 (x : real) (y : real) (h1 : term127 x y) : term102 y.
Proof. exact (@lem1631479 y (@lem1631476 x y h1)). Qed.
Lemma lem1631481 (y : real) : (term103 y) = (term64 y).
Proof. exact (@lem1483460 (term64 y)). Qed.
Lemma lem1631482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1631483 (y : real) : (term104 y) = (term86 y).
Proof. exact (MK_COMB (@lem1631482) (@lem1631481 y)). Qed.
Lemma lem1631484 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631485 (y : real) : (term102 y) = (term87 y).
Proof. exact (MK_COMB (@lem1631483 y) (@lem1631484)). Qed.
Lemma lem1631486 (x : real) (y : real) (h1 : term127 x y) : term87 y.
Proof. exact (EQ_MP (@lem1631485 y) (@lem1631480 x y h1)). Qed.
Lemma lem1631488 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631489 : term96 = term97.
Proof. exact (@lem1631488 (NUMERAL 0) term74). Qed.
Lemma lem1631490 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631491 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631492 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631491 h1) (fun h1 : term97 = True => @lem1631490)). Qed.
Lemma lem1631493 : term97 = True.
Proof. exact (EQ_MP (@lem1631492) (@lem1631490)). Qed.
Lemma lem1631494 : term96 = True.
Proof. exact (TRANS (@lem1631489) (@lem1631493)). Qed.
Lemma lem1631495 : True = term96.
Proof. exact (SYM (@lem1631494)). Qed.
Lemma lem1631496 : term96.
Proof. exact (EQ_MP (@lem1631495) (@lem0)). Qed.
Lemma lem1631497 (x : real) (y : real) (h1 : term127 x y) : term128 x y.
Proof. exact (conj (@lem1631496) (@lem1631444 x y h1)). Qed.
Lemma lem1631499 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631500 (x : real) (y : real) : term129 x y.
Proof. exact (@lem1631499 term22 (term63 x y)). Qed.
Lemma lem1631501 (x : real) (y : real) (h1 : term127 x y) : term130 x y.
Proof. exact (@lem1631500 x y (@lem1631497 x y h1)). Qed.
Lemma lem1631502 (x : real) (y : real) : (term131 x y) = (term63 x y).
Proof. exact (@lem1483460 (term63 x y)). Qed.
Lemma lem1631503 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631504 (x : real) (y : real) : (term132 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1631503) (@lem1631502 x y)). Qed.
Lemma lem1631505 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631506 (x : real) (y : real) : (term130 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1631504 x y) (@lem1631505)). Qed.
Lemma lem1631507 (x : real) (y : real) (h1 : term127 x y) : term68 x y.
Proof. exact (EQ_MP (@lem1631506 x y) (@lem1631501 x y h1)). Qed.
Lemma lem1631508 (x : real) (y : real) (h1 : term127 x y) : term133 x y.
Proof. exact (conj (@lem1631507 x y h1) (@lem1631486 x y h1)). Qed.
Lemma lem1631510 (x : real) (y : real) : term112 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1631511 (x : real) (y : real) : term134 x y.
Proof. exact (@lem1631510 (term63 x y) (term64 y)). Qed.
Lemma lem1631512 (x : real) (y : real) (h1 : term127 x y) : term135 x y.
Proof. exact (@lem1631511 x y (@lem1631508 x y h1)). Qed.
Lemma lem1631513 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (@lem1483482 (term64 x) y (term64 y)). Qed.
Lemma lem1631514 (y : real) : (term115 y) = (term116 y).
Proof. exact (@lem1483442 term117 y). Qed.
Lemma lem1631516 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1631517 : term119 = term67.
Proof. exact (@lem1631516 term74). Qed.
Lemma lem1631518 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1631519 : term120 = term121.
Proof. exact (MK_COMB (@lem1631518) (@lem1631517)). Qed.
Lemma lem1631520 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1631521 (y : real) : (term116 y) = (term122 y).
Proof. exact (MK_COMB (@lem1631519) (@lem1631520 y)). Qed.
Lemma lem1631522 (y : real) : (term115 y) = (term122 y).
Proof. exact (TRANS (@lem1631514 y) (@lem1631521 y)). Qed.
Lemma lem1631523 (y : real) : (term122 y) = term67.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1631524 (y : real) : (term115 y) = term67.
Proof. exact (TRANS (@lem1631522 y) (@lem1631523 y)). Qed.
Lemma lem1631525 (x : real) : (term138 x) = (term138 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1631526 (y : real) (x : real) : (term137 x y) = (term139 x).
Proof. exact (MK_COMB (@lem1631525 x) (@lem1631524 y)). Qed.
Lemma lem1631527 (y : real) (x : real) : (term136 x y) = (term139 x).
Proof. exact (TRANS (@lem1631513 x y) (@lem1631526 y x)). Qed.
Lemma lem1631528 (x : real) : (term139 x) = (term64 x).
Proof. exact (@lem1483450 (term64 x)). Qed.
Lemma lem1631529 (y : real) (x : real) : (term136 x y) = (term64 x).
Proof. exact (TRANS (@lem1631527 y x) (@lem1631528 x)). Qed.
Lemma lem1631530 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631531 (y : real) (x : real) : (term140 x y) = (term141 x).
Proof. exact (MK_COMB (@lem1631530) (@lem1631529 y x)). Qed.
Lemma lem1631532 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631533 (y : real) (x : real) : (term135 x y) = (term142 x).
Proof. exact (MK_COMB (@lem1631531 y x) (@lem1631532)). Qed.
Lemma lem1631534 (x : real) (y : real) (h1 : term127 x y) : term142 x.
Proof. exact (EQ_MP (@lem1631533 y x) (@lem1631512 x y h1)). Qed.
Lemma lem1631536 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631537 : term96 = term97.
Proof. exact (@lem1631536 (NUMERAL 0) term74). Qed.
Lemma lem1631538 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631539 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631540 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631539 h1) (fun h1 : term97 = True => @lem1631538)). Qed.
Lemma lem1631541 : term97 = True.
Proof. exact (EQ_MP (@lem1631540) (@lem1631538)). Qed.
Lemma lem1631542 : term96 = True.
Proof. exact (TRANS (@lem1631537) (@lem1631541)). Qed.
Lemma lem1631543 : True = term96.
Proof. exact (SYM (@lem1631542)). Qed.
Lemma lem1631544 : term96.
Proof. exact (EQ_MP (@lem1631543) (@lem0)). Qed.
Lemma lem1631545 (x : real) (y : real) (h1 : term127 x y) : term143 x.
Proof. exact (conj (@lem1631544) (@lem1631534 x y h1)). Qed.
Lemma lem1631547 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631548 (x : real) : term144 x.
Proof. exact (@lem1631547 term22 (term64 x)). Qed.
Lemma lem1631549 (x : real) (y : real) (h1 : term127 x y) : term145 x.
Proof. exact (@lem1631548 x (@lem1631545 x y h1)). Qed.
Lemma lem1631550 (x : real) : (term103 x) = (term64 x).
Proof. exact (@lem1483460 (term64 x)). Qed.
Lemma lem1631551 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631552 (x : real) : (term146 x) = (term141 x).
Proof. exact (MK_COMB (@lem1631551) (@lem1631550 x)). Qed.
Lemma lem1631553 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631554 (x : real) : (term145 x) = (term142 x).
Proof. exact (MK_COMB (@lem1631552 x) (@lem1631553)). Qed.
Lemma lem1631555 (x : real) (y : real) (h1 : term127 x y) : term142 x.
Proof. exact (EQ_MP (@lem1631554 x) (@lem1631549 x y h1)). Qed.
Lemma lem1631556 (x : real) (y : real) (h1 : term127 x y) : term147 x.
Proof. exact (conj (@lem1631555 x y h1) (@lem1631465 x y h1)). Qed.
Lemma lem1631558 (x : real) (y : real) : term148 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1631559 (x : real) : term149 x.
Proof. exact (@lem1631558 (term64 x) x). Qed.
Lemma lem1631560 (x : real) (y : real) (h1 : term127 x y) : term150 x.
Proof. exact (@lem1631559 x (@lem1631556 x y h1)). Qed.
Lemma lem1631561 (x : real) : (term151 x) = (term116 x).
Proof. exact (@lem1483440 term117 x). Qed.
Lemma lem1631563 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1631564 : term119 = term67.
Proof. exact (@lem1631563 term74). Qed.
Lemma lem1631565 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1631566 : term120 = term121.
Proof. exact (MK_COMB (@lem1631565) (@lem1631564)). Qed.
Lemma lem1631567 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1631568 (x : real) : (term116 x) = (term122 x).
Proof. exact (MK_COMB (@lem1631566) (@lem1631567 x)). Qed.
Lemma lem1631569 (x : real) : (term151 x) = (term122 x).
Proof. exact (TRANS (@lem1631561 x) (@lem1631568 x)). Qed.
Lemma lem1631570 (x : real) : (term122 x) = term67.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1631571 (x : real) : (term151 x) = term67.
Proof. exact (TRANS (@lem1631569 x) (@lem1631570 x)). Qed.
Lemma lem1631572 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631573 (x : real) : (term152 x) = term124.
Proof. exact (MK_COMB (@lem1631572) (@lem1631571 x)). Qed.
Lemma lem1631574 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631575 (x : real) : (term150 x) = term125.
Proof. exact (MK_COMB (@lem1631573 x) (@lem1631574)). Qed.
Lemma lem1631576 (x : real) (y : real) (h1 : term127 x y) : term125.
Proof. exact (EQ_MP (@lem1631575 x) (@lem1631560 x y h1)). Qed.
Lemma lem1631578 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631579 : term125 = term126.
Proof. exact (@lem1631578 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1631580 : term126 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1631581 : term125 = False.
Proof. exact (TRANS (@lem1631579) (@lem1631580)). Qed.
Lemma lem1631582 (x : real) (y : real) (h1 : term127 x y) : False.
Proof. exact (EQ_MP (@lem1631581) (@lem1631576 x y h1)). Qed.
Lemma lem1631583 (x : real) (y : real) (h1 : term93 x y) : False.
Proof. exact (or_elim (@lem1631365 x y h1) (fun h0 : term94 y x => @lem1631439 y x h0) (fun h0 : term127 x y => @lem1631582 x y h0)). Qed.
Lemma lem1631585 (x : real) (y : real) (h1 : term93 x y) : term93 x y.
Proof. exact (h1). Qed.
Lemma lem1631586 (x : real) (y : real) (h1 : term93 x y) : (term93 x y) = False.
Proof. exact (prop_ext (fun h2 : term93 x y => @lem1631583 x y h1) (fun h2 : False => @lem1631585 x y h1)). Qed.
Lemma lem1631587 (x : real) (y : real) (h1 : term93 x y) : False.
Proof. exact (EQ_MP (@lem1631586 x y h1) (@lem1631585 x y h1)). Qed.
Lemma lem1631588 (x : real) (y : real) (h1 : term60 x y) : term60 x y.
Proof. exact (h1). Qed.
Lemma lem1631589 (x : real) (y : real) (h1 : term60 x y) : term93 x y.
Proof. exact (EQ_MP (@lem1631355 x y) (@lem1631588 x y h1)). Qed.
Lemma lem1631590 (x : real) (y : real) (h1 : term60 x y) : (term93 x y) = False.
Proof. exact (prop_ext (fun h2 : term93 x y => @lem1631587 x y h2) (fun h2 : False => @lem1631589 x y h1)). Qed.
Lemma lem1631591 (x : real) (y : real) (h1 : term60 x y) : False.
Proof. exact (EQ_MP (@lem1631590 x y h1) (@lem1631589 x y h1)). Qed.
Lemma lem1631592 (x : real) (y : real) : term153 x y.
Proof. exact (fun h0 : term60 x y => @lem1631591 x y h0). Qed.
Lemma lem1631593 (x : real) (y : real) : term154 x y.
Proof. exact (@lem1386578 (term155 x y)). Qed.
Lemma lem1631594 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1631593 x y (@lem1631592 x y)). Qed.
Lemma lem1631595 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term30 x y.
Proof. exact (@lem1631594 x y (@lem1631192 y x h1 h2)). Qed.
Lemma lem1631596 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term31 x y.
Proof. exact (@lem1631191 x y (@lem1631595 y x h1 h2)). Qed.
Lemma lem1631597 (x : real) (y : real) (h1 : term156 x y) : term156 x y.
Proof. exact (h1). Qed.
Lemma lem1631599 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1631131 x) (@lem1631130 x)). Qed.
Lemma lem1631601 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1631131 x) (@lem1631130 x)). Qed.
Lemma lem1631602 (y : real) : term19 y.
Proof. exact (@lem1631601 y). Qed.
Lemma lem1631603 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term54 y x.
Proof. exact (conj (@lem1631185 x y h1) (@lem1631186 x h2)). Qed.
Lemma lem1631604 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term54 y x.
Proof. exact (conj (@lem1631185 x y h1) (@lem1631186 x h2)). Qed.
Lemma lem1631619 (x : real) : (term157 x) = (x = term67).
Proof. exact (@lem16933 (x = term67)). Qed.
Lemma lem1631621 (y : real) (x : real) : (term57 y x) = (term57 y x).
Proof. exact (eq_refl (term57 y x)). Qed.
Lemma lem1631622 (y : real) (x : real) : (term158 y x) = (term159 y x).
Proof. exact (MK_COMB (@lem1631621 y x) (@lem1631619 x)). Qed.
Lemma lem1631623 (y : real) (x : real) : (term160 y x) = (term158 y x).
Proof. exact (@lem17362 (term54 y x) (term20 x)). Qed.
Lemma lem1631635 (y : real) (x : real) : (term160 y x) = (term159 y x).
Proof. exact (TRANS (@lem1631623 y x) (@lem1631622 y x)). Qed.
Lemma lem1631636 (y : real) (x : real) : (real_lt x y) = (term61 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1631642 (y : real) (x : real) : (real_sub y x) = (term62 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1631647 (x : real) (y : real) : (term62 y x) = (term63 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1631649 (x : real) (y : real) : (real_sub y x) = (term63 x y).
Proof. exact (TRANS (@lem1631642 y x) (@lem1631647 x y)). Qed.
Lemma lem1631650 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631651 (x : real) (y : real) : (term65 y x) = (term66 x y).
Proof. exact (MK_COMB (@lem1631650) (@lem1631649 x y)). Qed.
Lemma lem1631652 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631653 (x : real) (y : real) : (term61 y x) = (term68 x y).
Proof. exact (MK_COMB (@lem1631651 x y) (@lem1631652)). Qed.
Lemma lem1631654 (x : real) (y : real) : (real_lt x y) = (term68 x y).
Proof. exact (TRANS (@lem1631636 y x) (@lem1631653 x y)). Qed.
Lemma lem1631655 (x : real) : (term52 x) = (term69 x).
Proof. exact (@lem1483521 x term67). Qed.
Lemma lem1631661 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1483519 x term67). Qed.
Lemma lem1631663 (x : nat) : (term72 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1631664 : term73 = term67.
Proof. exact (@lem1631663 term74). Qed.
Lemma lem1631665 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1631666 (x : real) : (term71 x) = (term75 x).
Proof. exact (MK_COMB (@lem1631665 x) (@lem1631664)). Qed.
Lemma lem1631667 (x : real) : (term75 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1631668 (x : real) : (term71 x) = x.
Proof. exact (TRANS (@lem1631666 x) (@lem1631667 x)). Qed.
Lemma lem1631670 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1631661 x) (@lem1631668 x)). Qed.
Lemma lem1631671 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631672 (x : real) : (term76 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631671) (@lem1631670 x)). Qed.
Lemma lem1631673 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631674 (x : real) : (term69 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631672 x) (@lem1631673)). Qed.
Lemma lem1631675 (x : real) : (term52 x) = (term77 x).
Proof. exact (TRANS (@lem1631655 x) (@lem1631674 x)). Qed.
Lemma lem1631676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631677 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1631676) (@lem1631654 x y)). Qed.
Lemma lem1631678 (y : real) (x : real) : (term54 y x) = (term80 y x).
Proof. exact (MK_COMB (@lem1631677 x y) (@lem1631675 x)). Qed.
Lemma lem1631679 (x : real) : (x = term67) = ((term70 x) = term67).
Proof. exact (@lem1483529 x term67). Qed.
Lemma lem1631685 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1483519 x term67). Qed.
Lemma lem1631687 (x : nat) : (term72 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1631688 : term73 = term67.
Proof. exact (@lem1631687 term74). Qed.
Lemma lem1631689 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1631690 (x : real) : (term71 x) = (term75 x).
Proof. exact (MK_COMB (@lem1631689 x) (@lem1631688)). Qed.
Lemma lem1631691 (x : real) : (term75 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1631692 (x : real) : (term71 x) = x.
Proof. exact (TRANS (@lem1631690 x) (@lem1631691 x)). Qed.
Lemma lem1631694 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1631685 x) (@lem1631692 x)). Qed.
Lemma lem1631695 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1631696 (x : real) : (term161 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1631695) (@lem1631694 x)). Qed.
Lemma lem1631697 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631698 (x : real) : ((term70 x) = term67) = (x = term67).
Proof. exact (MK_COMB (@lem1631696 x) (@lem1631697)). Qed.
Lemma lem1631699 (x : real) : (x = term67) = (x = term67).
Proof. exact (TRANS (@lem1631679 x) (@lem1631698 x)). Qed.
Lemma lem1631700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631701 (y : real) (x : real) : (term57 y x) = (term91 y x).
Proof. exact (MK_COMB (@lem1631700) (@lem1631678 y x)). Qed.
Lemma lem1631702 (y : real) (x : real) : (term159 y x) = (term162 y x).
Proof. exact (MK_COMB (@lem1631701 y x) (@lem1631699 x)). Qed.
Lemma lem1631723 (y : real) (x : real) : (term160 y x) = (term162 y x).
Proof. exact (TRANS (@lem1631635 y x) (@lem1631702 y x)). Qed.
Lemma lem1631727 (y : real) (x : real) (h1 : term162 y x) : term162 y x.
Proof. exact (h1). Qed.
Lemma lem1631728 (y : real) (x : real) (h1 : term162 y x) : x = term67.
Proof. exact (proj2 (@lem1631727 y x h1)). Qed.
Lemma lem1631729 (y : real) (x : real) (h1 : term162 y x) : term80 y x.
Proof. exact (proj1 (@lem1631727 y x h1)). Qed.
Lemma lem1631730 (y : real) (x : real) (h1 : term162 y x) : term77 x.
Proof. exact (proj2 (@lem1631729 y x h1)). Qed.
Lemma lem1631733 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631734 : term96 = term97.
Proof. exact (@lem1631733 (NUMERAL 0) term74). Qed.
Lemma lem1631735 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631736 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631737 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631736 h1) (fun h1 : term97 = True => @lem1631735)). Qed.
Lemma lem1631738 : term97 = True.
Proof. exact (EQ_MP (@lem1631737) (@lem1631735)). Qed.
Lemma lem1631739 : term96 = True.
Proof. exact (TRANS (@lem1631734) (@lem1631738)). Qed.
Lemma lem1631740 : True = term96.
Proof. exact (SYM (@lem1631739)). Qed.
Lemma lem1631741 : term96.
Proof. exact (EQ_MP (@lem1631740) (@lem0)). Qed.
Lemma lem1631742 (y : real) (x : real) (h1 : term162 y x) : term105 x.
Proof. exact (conj (@lem1631741) (@lem1631730 y x h1)). Qed.
Lemma lem1631744 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631745 (x : real) : term107 x.
Proof. exact (@lem1631744 term22 x). Qed.
Lemma lem1631746 (y : real) (x : real) (h1 : term162 y x) : term108 x.
Proof. exact (@lem1631745 x (@lem1631742 y x h1)). Qed.
Lemma lem1631747 (x : real) : (term109 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1631748 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631749 (x : real) : (term110 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631748) (@lem1631747 x)). Qed.
Lemma lem1631750 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631751 (x : real) : (term108 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631749 x) (@lem1631750)). Qed.
Lemma lem1631752 (y : real) (x : real) (h1 : term162 y x) : term77 x.
Proof. exact (EQ_MP (@lem1631751 x) (@lem1631746 y x h1)). Qed.
Lemma lem1631754 (y : real) : term163 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1631755 (x : real) : term163 x.
Proof. exact (@lem1631754 x). Qed.
Lemma lem1631756 (y : real) (x : real) (h1 : term162 y x) : term164 x.
Proof. exact (@lem1631755 x (@lem1631728 y x h1)). Qed.
Lemma lem1631757 (y : real) (x : real) (h1 : term162 y x) : term165 x.
Proof. exact (@lem1631756 y x h1 term117). Qed.
Lemma lem1631758 (x : real) : (term165 x) = ((term64 x) = term67).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1631765 (y : real) (x : real) (h1 : term162 y x) : (term64 x) = term67.
Proof. exact (EQ_MP (@lem1631758 x) (@lem1631757 y x h1)). Qed.
Lemma lem1631766 (y : real) (x : real) (h1 : term162 y x) : term166 x.
Proof. exact (conj (@lem1631765 y x h1) (@lem1631752 y x h1)). Qed.
Lemma lem1631768 (x : real) (y : real) : term167 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1631769 (x : real) : term168 x.
Proof. exact (@lem1631768 (term64 x) x). Qed.
Lemma lem1631770 (y : real) (x : real) (h1 : term162 y x) : term150 x.
Proof. exact (@lem1631769 x (@lem1631766 y x h1)). Qed.
Lemma lem1631771 (x : real) : (term151 x) = (term116 x).
Proof. exact (@lem1483440 term117 x). Qed.
Lemma lem1631773 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1631774 : term119 = term67.
Proof. exact (@lem1631773 term74). Qed.
Lemma lem1631775 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1631776 : term120 = term121.
Proof. exact (MK_COMB (@lem1631775) (@lem1631774)). Qed.
Lemma lem1631777 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1631778 (x : real) : (term116 x) = (term122 x).
Proof. exact (MK_COMB (@lem1631776) (@lem1631777 x)). Qed.
Lemma lem1631779 (x : real) : (term151 x) = (term122 x).
Proof. exact (TRANS (@lem1631771 x) (@lem1631778 x)). Qed.
Lemma lem1631780 (x : real) : (term122 x) = term67.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1631781 (x : real) : (term151 x) = term67.
Proof. exact (TRANS (@lem1631779 x) (@lem1631780 x)). Qed.
Lemma lem1631782 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631783 (x : real) : (term152 x) = term124.
Proof. exact (MK_COMB (@lem1631782) (@lem1631781 x)). Qed.
Lemma lem1631784 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631785 (x : real) : (term150 x) = term125.
Proof. exact (MK_COMB (@lem1631783 x) (@lem1631784)). Qed.
Lemma lem1631786 (y : real) (x : real) (h1 : term162 y x) : term125.
Proof. exact (EQ_MP (@lem1631785 x) (@lem1631770 y x h1)). Qed.
Lemma lem1631788 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631789 : term125 = term126.
Proof. exact (@lem1631788 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1631790 : term126 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1631791 : term125 = False.
Proof. exact (TRANS (@lem1631789) (@lem1631790)). Qed.
Lemma lem1631792 (y : real) (x : real) (h1 : term162 y x) : False.
Proof. exact (EQ_MP (@lem1631791) (@lem1631786 y x h1)). Qed.
Lemma lem1631794 (y : real) (x : real) (h1 : term162 y x) : term162 y x.
Proof. exact (h1). Qed.
Lemma lem1631795 (y : real) (x : real) (h1 : term162 y x) : (term162 y x) = False.
Proof. exact (prop_ext (fun h2 : term162 y x => @lem1631792 y x h1) (fun h2 : False => @lem1631794 y x h1)). Qed.
Lemma lem1631796 (y : real) (x : real) (h1 : term162 y x) : False.
Proof. exact (EQ_MP (@lem1631795 y x h1) (@lem1631794 y x h1)). Qed.
Lemma lem1631797 (y : real) (x : real) (h1 : term160 y x) : term160 y x.
Proof. exact (h1). Qed.
Lemma lem1631798 (y : real) (x : real) (h1 : term160 y x) : term162 y x.
Proof. exact (EQ_MP (@lem1631723 y x) (@lem1631797 y x h1)). Qed.
Lemma lem1631799 (y : real) (x : real) (h1 : term160 y x) : (term162 y x) = False.
Proof. exact (prop_ext (fun h2 : term162 y x => @lem1631796 y x h2) (fun h2 : False => @lem1631798 y x h1)). Qed.
Lemma lem1631800 (y : real) (x : real) (h1 : term160 y x) : False.
Proof. exact (EQ_MP (@lem1631799 y x h1) (@lem1631798 y x h1)). Qed.
Lemma lem1631801 (y : real) (x : real) : term169 y x.
Proof. exact (fun h0 : term160 y x => @lem1631800 y x h0). Qed.
Lemma lem1631802 (y : real) (x : real) : term170 y x.
Proof. exact (@lem1386578 (term171 y x)). Qed.
Lemma lem1631803 (y : real) (x : real) : term171 y x.
Proof. exact (@lem1631802 y x (@lem1631801 y x)). Qed.
Lemma lem1631818 (y : real) : (term157 y) = (y = term67).
Proof. exact (@lem16933 (y = term67)). Qed.
Lemma lem1631820 (y : real) (x : real) : (term57 y x) = (term57 y x).
Proof. exact (eq_refl (term57 y x)). Qed.
Lemma lem1631821 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1631820 y x) (@lem1631818 y)). Qed.
Lemma lem1631822 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem17362 (term54 y x) (term20 y)). Qed.
Lemma lem1631834 (x : real) (y : real) : (term174 x y) = (term173 x y).
Proof. exact (TRANS (@lem1631822 x y) (@lem1631821 x y)). Qed.
Lemma lem1631835 (y : real) (x : real) : (real_lt x y) = (term61 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1631841 (y : real) (x : real) : (real_sub y x) = (term62 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1631846 (x : real) (y : real) : (term62 y x) = (term63 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1631848 (x : real) (y : real) : (real_sub y x) = (term63 x y).
Proof. exact (TRANS (@lem1631841 y x) (@lem1631846 x y)). Qed.
Lemma lem1631849 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631850 (x : real) (y : real) : (term65 y x) = (term66 x y).
Proof. exact (MK_COMB (@lem1631849) (@lem1631848 x y)). Qed.
Lemma lem1631851 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631852 (x : real) (y : real) : (term61 y x) = (term68 x y).
Proof. exact (MK_COMB (@lem1631850 x y) (@lem1631851)). Qed.
Lemma lem1631853 (x : real) (y : real) : (real_lt x y) = (term68 x y).
Proof. exact (TRANS (@lem1631835 y x) (@lem1631852 x y)). Qed.
Lemma lem1631854 (x : real) : (term52 x) = (term69 x).
Proof. exact (@lem1483521 x term67). Qed.
Lemma lem1631860 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1483519 x term67). Qed.
Lemma lem1631862 (x : nat) : (term72 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1631863 : term73 = term67.
Proof. exact (@lem1631862 term74). Qed.
Lemma lem1631864 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1631865 (x : real) : (term71 x) = (term75 x).
Proof. exact (MK_COMB (@lem1631864 x) (@lem1631863)). Qed.
Lemma lem1631866 (x : real) : (term75 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1631867 (x : real) : (term71 x) = x.
Proof. exact (TRANS (@lem1631865 x) (@lem1631866 x)). Qed.
Lemma lem1631869 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1631860 x) (@lem1631867 x)). Qed.
Lemma lem1631870 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631871 (x : real) : (term76 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631870) (@lem1631869 x)). Qed.
Lemma lem1631872 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631873 (x : real) : (term69 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631871 x) (@lem1631872)). Qed.
Lemma lem1631874 (x : real) : (term52 x) = (term77 x).
Proof. exact (TRANS (@lem1631854 x) (@lem1631873 x)). Qed.
Lemma lem1631875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631876 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1631875) (@lem1631853 x y)). Qed.
Lemma lem1631877 (y : real) (x : real) : (term54 y x) = (term80 y x).
Proof. exact (MK_COMB (@lem1631876 x y) (@lem1631874 x)). Qed.
Lemma lem1631878 (y : real) : (y = term67) = ((term70 y) = term67).
Proof. exact (@lem1483529 y term67). Qed.
Lemma lem1631884 (y : real) : (term70 y) = (term71 y).
Proof. exact (@lem1483519 y term67). Qed.
Lemma lem1631886 (x : nat) : (term72 x) = term67.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1631887 : term73 = term67.
Proof. exact (@lem1631886 term74). Qed.
Lemma lem1631888 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1631889 (y : real) : (term71 y) = (term75 y).
Proof. exact (MK_COMB (@lem1631888 y) (@lem1631887)). Qed.
Lemma lem1631890 (y : real) : (term75 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1631891 (y : real) : (term71 y) = y.
Proof. exact (TRANS (@lem1631889 y) (@lem1631890 y)). Qed.
Lemma lem1631893 (y : real) : (term70 y) = y.
Proof. exact (TRANS (@lem1631884 y) (@lem1631891 y)). Qed.
Lemma lem1631894 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1631895 (y : real) : (term161 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1631894) (@lem1631893 y)). Qed.
Lemma lem1631896 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631897 (y : real) : ((term70 y) = term67) = (y = term67).
Proof. exact (MK_COMB (@lem1631895 y) (@lem1631896)). Qed.
Lemma lem1631898 (y : real) : (y = term67) = (y = term67).
Proof. exact (TRANS (@lem1631878 y) (@lem1631897 y)). Qed.
Lemma lem1631899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631900 (y : real) (x : real) : (term57 y x) = (term91 y x).
Proof. exact (MK_COMB (@lem1631899) (@lem1631877 y x)). Qed.
Lemma lem1631901 (x : real) (y : real) : (term173 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1631900 y x) (@lem1631898 y)). Qed.
Lemma lem1631922 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (TRANS (@lem1631834 x y) (@lem1631901 x y)). Qed.
Lemma lem1631926 (x : real) (y : real) (h1 : term175 x y) : term175 x y.
Proof. exact (h1). Qed.
Lemma lem1631927 (x : real) (y : real) (h1 : term175 x y) : y = term67.
Proof. exact (proj2 (@lem1631926 x y h1)). Qed.
Lemma lem1631928 (x : real) (y : real) (h1 : term175 x y) : term80 y x.
Proof. exact (proj1 (@lem1631926 x y h1)). Qed.
Lemma lem1631929 (x : real) (y : real) (h1 : term175 x y) : term77 x.
Proof. exact (proj2 (@lem1631928 x y h1)). Qed.
Lemma lem1631930 (x : real) (y : real) (h1 : term175 x y) : term68 x y.
Proof. exact (proj1 (@lem1631928 x y h1)). Qed.
Lemma lem1631932 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631933 : term96 = term97.
Proof. exact (@lem1631932 (NUMERAL 0) term74). Qed.
Lemma lem1631934 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631935 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631936 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631935 h1) (fun h1 : term97 = True => @lem1631934)). Qed.
Lemma lem1631937 : term97 = True.
Proof. exact (EQ_MP (@lem1631936) (@lem1631934)). Qed.
Lemma lem1631938 : term96 = True.
Proof. exact (TRANS (@lem1631933) (@lem1631937)). Qed.
Lemma lem1631939 : True = term96.
Proof. exact (SYM (@lem1631938)). Qed.
Lemma lem1631940 : term96.
Proof. exact (EQ_MP (@lem1631939) (@lem0)). Qed.
Lemma lem1631941 (x : real) (y : real) (h1 : term175 x y) : term105 x.
Proof. exact (conj (@lem1631940) (@lem1631929 x y h1)). Qed.
Lemma lem1631943 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631944 (x : real) : term107 x.
Proof. exact (@lem1631943 term22 x). Qed.
Lemma lem1631945 (x : real) (y : real) (h1 : term175 x y) : term108 x.
Proof. exact (@lem1631944 x (@lem1631941 x y h1)). Qed.
Lemma lem1631946 (x : real) : (term109 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1631947 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631948 (x : real) : (term110 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1631947) (@lem1631946 x)). Qed.
Lemma lem1631949 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631950 (x : real) : (term108 x) = (term77 x).
Proof. exact (MK_COMB (@lem1631948 x) (@lem1631949)). Qed.
Lemma lem1631951 (x : real) (y : real) (h1 : term175 x y) : term77 x.
Proof. exact (EQ_MP (@lem1631950 x) (@lem1631945 x y h1)). Qed.
Lemma lem1631953 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1631954 : term96 = term97.
Proof. exact (@lem1631953 (NUMERAL 0) term74). Qed.
Lemma lem1631955 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1631956 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1631957 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1631956 h1) (fun h1 : term97 = True => @lem1631955)). Qed.
Lemma lem1631958 : term97 = True.
Proof. exact (EQ_MP (@lem1631957) (@lem1631955)). Qed.
Lemma lem1631959 : term96 = True.
Proof. exact (TRANS (@lem1631954) (@lem1631958)). Qed.
Lemma lem1631960 : True = term96.
Proof. exact (SYM (@lem1631959)). Qed.
Lemma lem1631961 : term96.
Proof. exact (EQ_MP (@lem1631960) (@lem0)). Qed.
Lemma lem1631962 (x : real) (y : real) (h1 : term175 x y) : term128 x y.
Proof. exact (conj (@lem1631961) (@lem1631930 x y h1)). Qed.
Lemma lem1631964 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1631965 (x : real) (y : real) : term129 x y.
Proof. exact (@lem1631964 term22 (term63 x y)). Qed.
Lemma lem1631966 (x : real) (y : real) (h1 : term175 x y) : term130 x y.
Proof. exact (@lem1631965 x y (@lem1631962 x y h1)). Qed.
Lemma lem1631967 (x : real) (y : real) : (term131 x y) = (term63 x y).
Proof. exact (@lem1483460 (term63 x y)). Qed.
Lemma lem1631968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1631969 (x : real) (y : real) : (term132 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1631968) (@lem1631967 x y)). Qed.
Lemma lem1631970 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1631971 (x : real) (y : real) : (term130 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1631969 x y) (@lem1631970)). Qed.
Lemma lem1631972 (x : real) (y : real) (h1 : term175 x y) : term68 x y.
Proof. exact (EQ_MP (@lem1631971 x y) (@lem1631966 x y h1)). Qed.
Lemma lem1631974 (y : real) : term163 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1631975 (x : real) (y : real) (h1 : term175 x y) : term164 y.
Proof. exact (@lem1631974 y (@lem1631927 x y h1)). Qed.
Lemma lem1631976 (x : real) (y : real) (h1 : term175 x y) : term165 y.
Proof. exact (@lem1631975 x y h1 term117). Qed.
Lemma lem1631977 (y : real) : (term165 y) = ((term64 y) = term67).
Proof. exact (eq_refl (term165 y)). Qed.
Lemma lem1631984 (x : real) (y : real) (h1 : term175 x y) : (term64 y) = term67.
Proof. exact (EQ_MP (@lem1631977 y) (@lem1631976 x y h1)). Qed.
Lemma lem1631985 (x : real) (y : real) (h1 : term175 x y) : term176 x y.
Proof. exact (conj (@lem1631984 x y h1) (@lem1631972 x y h1)). Qed.
Lemma lem1631987 (x : real) (y : real) : term167 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1631988 (x : real) (y : real) : term177 x y.
Proof. exact (@lem1631987 (term64 y) (term63 x y)). Qed.
Lemma lem1631989 (x : real) (y : real) (h1 : term175 x y) : term178 x y.
Proof. exact (@lem1631988 x y (@lem1631985 x y h1)). Qed.
Lemma lem1631990 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (@lem1483484 (term64 x) (term64 y) y). Qed.
Lemma lem1631991 (y : real) : (term151 y) = (term116 y).
Proof. exact (@lem1483440 term117 y). Qed.
Lemma lem1631993 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1631994 : term119 = term67.
Proof. exact (@lem1631993 term74). Qed.
Lemma lem1631995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1631996 : term120 = term121.
Proof. exact (MK_COMB (@lem1631995) (@lem1631994)). Qed.
Lemma lem1631997 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1631998 (y : real) : (term116 y) = (term122 y).
Proof. exact (MK_COMB (@lem1631996) (@lem1631997 y)). Qed.
Lemma lem1631999 (y : real) : (term151 y) = (term122 y).
Proof. exact (TRANS (@lem1631991 y) (@lem1631998 y)). Qed.
Lemma lem1632000 (y : real) : (term122 y) = term67.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1632001 (y : real) : (term151 y) = term67.
Proof. exact (TRANS (@lem1631999 y) (@lem1632000 y)). Qed.
Lemma lem1632002 (x : real) : (term138 x) = (term138 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1632003 (y : real) (x : real) : (term180 x y) = (term139 x).
Proof. exact (MK_COMB (@lem1632002 x) (@lem1632001 y)). Qed.
Lemma lem1632004 (y : real) (x : real) : (term179 x y) = (term139 x).
Proof. exact (TRANS (@lem1631990 x y) (@lem1632003 y x)). Qed.
Lemma lem1632005 (x : real) : (term139 x) = (term64 x).
Proof. exact (@lem1483450 (term64 x)). Qed.
Lemma lem1632006 (y : real) (x : real) : (term179 x y) = (term64 x).
Proof. exact (TRANS (@lem1632004 y x) (@lem1632005 x)). Qed.
Lemma lem1632007 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1632008 (y : real) (x : real) : (term181 x y) = (term141 x).
Proof. exact (MK_COMB (@lem1632007) (@lem1632006 y x)). Qed.
Lemma lem1632009 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1632010 (y : real) (x : real) : (term178 x y) = (term142 x).
Proof. exact (MK_COMB (@lem1632008 y x) (@lem1632009)). Qed.
Lemma lem1632011 (x : real) (y : real) (h1 : term175 x y) : term142 x.
Proof. exact (EQ_MP (@lem1632010 y x) (@lem1631989 x y h1)). Qed.
Lemma lem1632013 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1632014 : term96 = term97.
Proof. exact (@lem1632013 (NUMERAL 0) term74). Qed.
Lemma lem1632015 : term98 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1632016 (h1 : term98 = (BIT1 0)) : term97 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1632017 : (term98 = (BIT1 0)) = (term97 = True).
Proof. exact (prop_ext (fun h1 : term98 = (BIT1 0) => @lem1632016 h1) (fun h1 : term97 = True => @lem1632015)). Qed.
Lemma lem1632018 : term97 = True.
Proof. exact (EQ_MP (@lem1632017) (@lem1632015)). Qed.
Lemma lem1632019 : term96 = True.
Proof. exact (TRANS (@lem1632014) (@lem1632018)). Qed.
Lemma lem1632020 : True = term96.
Proof. exact (SYM (@lem1632019)). Qed.
Lemma lem1632021 : term96.
Proof. exact (EQ_MP (@lem1632020) (@lem0)). Qed.
Lemma lem1632022 (x : real) (y : real) (h1 : term175 x y) : term143 x.
Proof. exact (conj (@lem1632021) (@lem1632011 x y h1)). Qed.
Lemma lem1632024 (x : real) (y : real) : term106 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1632025 (x : real) : term144 x.
Proof. exact (@lem1632024 term22 (term64 x)). Qed.
Lemma lem1632026 (x : real) (y : real) (h1 : term175 x y) : term145 x.
Proof. exact (@lem1632025 x (@lem1632022 x y h1)). Qed.
Lemma lem1632027 (x : real) : (term103 x) = (term64 x).
Proof. exact (@lem1483460 (term64 x)). Qed.
Lemma lem1632028 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1632029 (x : real) : (term146 x) = (term141 x).
Proof. exact (MK_COMB (@lem1632028) (@lem1632027 x)). Qed.
Lemma lem1632030 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1632031 (x : real) : (term145 x) = (term142 x).
Proof. exact (MK_COMB (@lem1632029 x) (@lem1632030)). Qed.
Lemma lem1632032 (x : real) (y : real) (h1 : term175 x y) : term142 x.
Proof. exact (EQ_MP (@lem1632031 x) (@lem1632026 x y h1)). Qed.
Lemma lem1632033 (x : real) (y : real) (h1 : term175 x y) : term147 x.
Proof. exact (conj (@lem1632032 x y h1) (@lem1631951 x y h1)). Qed.
Lemma lem1632035 (x : real) (y : real) : term148 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1632036 (x : real) : term149 x.
Proof. exact (@lem1632035 (term64 x) x). Qed.
Lemma lem1632037 (x : real) (y : real) (h1 : term175 x y) : term150 x.
Proof. exact (@lem1632036 x (@lem1632033 x y h1)). Qed.
Lemma lem1632038 (x : real) : (term151 x) = (term116 x).
Proof. exact (@lem1483440 term117 x). Qed.
Lemma lem1632040 (m : nat) : (term118 m) = term67.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1632041 : term119 = term67.
Proof. exact (@lem1632040 term74). Qed.
Lemma lem1632042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1632043 : term120 = term121.
Proof. exact (MK_COMB (@lem1632042) (@lem1632041)). Qed.
Lemma lem1632044 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1632045 (x : real) : (term116 x) = (term122 x).
Proof. exact (MK_COMB (@lem1632043) (@lem1632044 x)). Qed.
Lemma lem1632046 (x : real) : (term151 x) = (term122 x).
Proof. exact (TRANS (@lem1632038 x) (@lem1632045 x)). Qed.
Lemma lem1632047 (x : real) : (term122 x) = term67.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1632048 (x : real) : (term151 x) = term67.
Proof. exact (TRANS (@lem1632046 x) (@lem1632047 x)). Qed.
Lemma lem1632049 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1632050 (x : real) : (term152 x) = term124.
Proof. exact (MK_COMB (@lem1632049) (@lem1632048 x)). Qed.
Lemma lem1632051 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1632052 (x : real) : (term150 x) = term125.
Proof. exact (MK_COMB (@lem1632050 x) (@lem1632051)). Qed.
Lemma lem1632053 (x : real) (y : real) (h1 : term175 x y) : term125.
Proof. exact (EQ_MP (@lem1632052 x) (@lem1632037 x y h1)). Qed.
Lemma lem1632055 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1632056 : term125 = term126.
Proof. exact (@lem1632055 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1632057 : term126 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1632058 : term125 = False.
Proof. exact (TRANS (@lem1632056) (@lem1632057)). Qed.
Lemma lem1632059 (x : real) (y : real) (h1 : term175 x y) : False.
Proof. exact (EQ_MP (@lem1632058) (@lem1632053 x y h1)). Qed.
Lemma lem1632061 (x : real) (y : real) (h1 : term175 x y) : term175 x y.
Proof. exact (h1). Qed.
Lemma lem1632062 (x : real) (y : real) (h1 : term175 x y) : (term175 x y) = False.
Proof. exact (prop_ext (fun h2 : term175 x y => @lem1632059 x y h1) (fun h2 : False => @lem1632061 x y h1)). Qed.
Lemma lem1632063 (x : real) (y : real) (h1 : term175 x y) : False.
Proof. exact (EQ_MP (@lem1632062 x y h1) (@lem1632061 x y h1)). Qed.
Lemma lem1632064 (x : real) (y : real) (h1 : term174 x y) : term174 x y.
Proof. exact (h1). Qed.
Lemma lem1632065 (x : real) (y : real) (h1 : term174 x y) : term175 x y.
Proof. exact (EQ_MP (@lem1631922 x y) (@lem1632064 x y h1)). Qed.
Lemma lem1632066 (x : real) (y : real) (h1 : term174 x y) : (term175 x y) = False.
Proof. exact (prop_ext (fun h2 : term175 x y => @lem1632063 x y h2) (fun h2 : False => @lem1632065 x y h1)). Qed.
Lemma lem1632067 (x : real) (y : real) (h1 : term174 x y) : False.
Proof. exact (EQ_MP (@lem1632066 x y h1) (@lem1632065 x y h1)). Qed.
Lemma lem1632068 (x : real) (y : real) : term182 x y.
Proof. exact (fun h0 : term174 x y => @lem1632067 x y h0). Qed.
Lemma lem1632069 (x : real) (y : real) : term183 x y.
Proof. exact (@lem1386578 (term184 x y)). Qed.
Lemma lem1632070 (x : real) (y : real) : term184 x y.
Proof. exact (@lem1632069 x y (@lem1632068 x y)). Qed.
Lemma lem1632071 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term20 y.
Proof. exact (@lem1632070 x y (@lem1631604 y x h1 h2)). Qed.
Lemma lem1632072 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term20 x.
Proof. exact (@lem1631803 y x (@lem1631603 y x h1 h2)). Qed.
Lemma lem1632073 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : (term21 y) = term22.
Proof. exact (@lem1631602 y (@lem1632071 y x h1 h2)). Qed.
Lemma lem1632074 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : (term21 x) = term22.
Proof. exact (@lem1631599 x (@lem1632072 y x h1 h2)). Qed.
Lemma lem1632075 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term156 x y.
Proof. exact (conj (@lem1632074 y x h1 h2) (@lem1632073 y x h1 h2)). Qed.
Lemma lem1632076 (x : real) : term185 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1632077 (x : real) : (term185 x) = ((term109 x) = x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem1632079 (x : real) : term186 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1632080 (x : real) : (term186 x) = (term8 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1632081 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1632080 x) (@lem1632079 x)). Qed.
Lemma lem1632082 (x : real) (y : real) : term187 x y.
Proof. exact (@lem1632081 x y). Qed.
Lemma lem1632083 (x : real) (y : real) : (term187 x y) = (term4 x y).
Proof. exact (eq_refl (term187 x y)). Qed.
Lemma lem1632084 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1632083 x y) (@lem1632082 x y)). Qed.
Lemma lem1632085 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1632084 x y z). Qed.
Lemma lem1632086 (x : real) (y : real) (z : real) : (term188 x y z) = ((term0 x y z) = (term1 x y z)).
Proof. exact (eq_refl (term188 x y z)). Qed.
Lemma lem1632095 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (EQ_MP (@lem1632086 x y z) (@lem1632085 x y z)). Qed.
Lemma lem1632096 (x : real) (y : real) : (term189 x y) = (term190 x y).
Proof. exact (@lem1632095 (real_inv y) x y). Qed.
Lemma lem1632097 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1632098 (x : real) (y : real) : (term191 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1632097) (@lem1632096 x y)). Qed.
Lemma lem1632100 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (EQ_MP (@lem1632086 x y z) (@lem1632085 x y z)). Qed.
Lemma lem1632101 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (@lem1632100 (real_inv x) x y). Qed.
Lemma lem1632103 (x : real) (y : real) (h1 : term156 x y) : (term21 x) = term22.
Proof. exact (proj1 (@lem1631597 x y h1)). Qed.
Lemma lem1632104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1632105 (x : real) (y : real) (h1 : term156 x y) : (term195 x) = term196.
Proof. exact (MK_COMB (@lem1632104) (@lem1632103 x y h1)). Qed.
Lemma lem1632106 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632107 (x : real) (y : real) (h1 : term156 x y) : (term194 x y) = (term109 y).
Proof. exact (MK_COMB (@lem1632105 x y h1) (@lem1632106 y)). Qed.
Lemma lem1632109 (x : real) : (term109 x) = x.
Proof. exact (EQ_MP (@lem1632077 x) (@lem1632076 x)). Qed.
Lemma lem1632110 (y : real) : (term109 y) = y.
Proof. exact (@lem1632109 y). Qed.
Lemma lem1632111 (x : real) (y : real) (h1 : term156 x y) : (term194 x y) = y.
Proof. exact (TRANS (@lem1632107 x y h1) (@lem1632110 y)). Qed.
Lemma lem1632112 (x : real) (y : real) (h1 : term156 x y) : (term193 x y) = y.
Proof. exact (TRANS (@lem1632101 x y) (@lem1632111 x y h1)). Qed.
Lemma lem1632113 (x : real) (y : real) (h1 : term156 x y) : (term197 x y) = (term198 x y).
Proof. exact (MK_COMB (@lem1632098 x y) (@lem1632112 x y h1)). Qed.
Lemma lem1632114 (x : real) (y : real) (h1 : term156 x y) : (term198 x y) = (term197 x y).
Proof. exact (SYM (@lem1632113 x y h1)). Qed.
Lemma lem1632116 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1631115 y x) (@lem1631114 x y)). Qed.
Lemma lem1632117 (x : real) (y : real) : (term199 y x) = (term200 x y).
Proof. exact (@lem1632116 x (real_inv y)). Qed.
Lemma lem1632118 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1632119 (x : real) (y : real) : (term201 y x) = (term202 x y).
Proof. exact (MK_COMB (@lem1632118) (@lem1632117 x y)). Qed.
Lemma lem1632120 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632121 (x : real) (y : real) : (term190 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1632119 x y) (@lem1632120 y)). Qed.
Lemma lem1632122 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1632123 (x : real) (y : real) : (term192 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1632122) (@lem1632121 x y)). Qed.
Lemma lem1632124 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632125 (x : real) (y : real) : (term198 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1632123 x y) (@lem1632124 y)). Qed.
Lemma lem1632126 (x : real) (y : real) : (term205 x y) = (term198 x y).
Proof. exact (SYM (@lem1632125 x y)). Qed.
Lemma lem1632127 (x : real) : term206 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1632128 (x : real) : (term206 x) = ((term207 x) = x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1632130 (x : real) : term208 x.
Proof. exact (@lem1631110 x). Qed.
Lemma lem1632131 (x : real) : (term208 x) = (term9 x).
Proof. exact (eq_refl (term208 x)). Qed.
Lemma lem1632132 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1632131 x) (@lem1632130 x)). Qed.
Lemma lem1632133 (x : real) (y : real) : term209 x y.
Proof. exact (@lem1632132 x y). Qed.
Lemma lem1632134 (x : real) (y : real) : (term209 x y) = (term5 x y).
Proof. exact (eq_refl (term209 x y)). Qed.
Lemma lem1632135 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1632134 x y) (@lem1632133 x y)). Qed.
Lemma lem1632136 (x : real) (y : real) (z : real) : term210 x y z.
Proof. exact (@lem1632135 x y z). Qed.
Lemma lem1632137 (x : real) (y : real) (z : real) : (term210 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term210 x y z)). Qed.
Lemma lem1632141 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1632146 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1632137 x y z) (@lem1632136 x y z)). Qed.
Lemma lem1632147 (x : real) (y : real) : (term203 x y) = (term211 x y).
Proof. exact (@lem1632146 x (real_inv y) y). Qed.
Lemma lem1632149 (x : real) (y : real) (h1 : term156 x y) : (term21 y) = term22.
Proof. exact (proj2 (@lem1631597 x y h1)). Qed.
Lemma lem1632150 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1632151 (x : real) (y : real) (h1 : term156 x y) : (term211 x y) = (term207 x).
Proof. exact (MK_COMB (@lem1632150 x) (@lem1632149 x y h1)). Qed.
Lemma lem1632153 (x : real) : (term207 x) = x.
Proof. exact (EQ_MP (@lem1632128 x) (@lem1632127 x)). Qed.
Lemma lem1632154 (x : real) (y : real) (h1 : term156 x y) : (term211 x y) = x.
Proof. exact (TRANS (@lem1632151 x y h1) (@lem1632153 x)). Qed.
Lemma lem1632155 (x : real) (y : real) (h1 : term156 x y) : (term203 x y) = x.
Proof. exact (TRANS (@lem1632147 x y) (@lem1632154 x y h1)). Qed.
Lemma lem1632156 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1632157 (x : real) (y : real) (h1 : term156 x y) : (term204 x y) = (real_lt x).
Proof. exact (MK_COMB (@lem1632156) (@lem1632155 x y h1)). Qed.
Lemma lem1632158 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632159 (x : real) (y : real) (h1 : term156 x y) : (term205 x y) = (real_lt x y).
Proof. exact (MK_COMB (@lem1632157 x y h1) (@lem1632158 y)). Qed.
Lemma lem1632161 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1632141 x y) (@lem1631185 x y h1)). Qed.
Lemma lem1632162 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : (term205 x y) = True.
Proof. exact (TRANS (@lem1632159 x y h1) (@lem1632161 x y h2)). Qed.
Lemma lem1632163 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : True = (term205 x y).
Proof. exact (SYM (@lem1632162 x y h1 h2)). Qed.
Lemma lem1632164 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : term205 x y.
Proof. exact (EQ_MP (@lem1632163 x y h1 h2) (@lem0)). Qed.
Lemma lem1632165 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : term198 x y.
Proof. exact (EQ_MP (@lem1632126 x y) (@lem1632164 x y h1 h2)). Qed.
Lemma lem1632166 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : term197 x y.
Proof. exact (EQ_MP (@lem1632114 x y h1) (@lem1632165 x y h1 h2)). Qed.
Lemma lem1632167 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : (term156 x y) = (term197 x y).
Proof. exact (prop_ext (fun h3 : term156 x y => @lem1632166 x y h1 h2) (fun h3 : term197 x y => @lem1631597 x y h1)). Qed.
Lemma lem1632168 (x : real) (y : real) (h1 : term156 x y) (h2 : real_lt x y) : term197 x y.
Proof. exact (EQ_MP (@lem1632167 x y h1 h2) (@lem1631597 x y h1)). Qed.
Lemma lem1632169 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : (term156 x y) = (term197 x y).
Proof. exact (prop_ext (fun h3 : term156 x y => @lem1632168 x y h3 h1) (fun h3 : term197 x y => @lem1632075 y x h1 h2)). Qed.
Lemma lem1632170 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term197 x y.
Proof. exact (EQ_MP (@lem1632169 y x h1 h2) (@lem1632075 y x h1 h2)). Qed.
Lemma lem1632171 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term212 x y.
Proof. exact (conj (@lem1631596 y x h1 h2) (@lem1632170 y x h1 h2)). Qed.
Lemma lem1632172 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term213 y x.
Proof. exact (ex_intro (term214 y x) (real_mul x y) (@lem1632171 y x h1 h2)). Qed.
Lemma lem1632173 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term215 y x.
Proof. exact (@lem1631189 y x (@lem1632172 y x h1 h2)). Qed.
Lemma lem1632174 (x : real) (y : real) (h1 : term51 x y) : real_lt x y.
Proof. exact (proj2 (@lem1631184 x y h1)). Qed.
Lemma lem1632175 (x : real) (y : real) (h1 : term51 x y) : term52 x.
Proof. exact (proj1 (@lem1631184 x y h1)). Qed.
Lemma lem1632176 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : (real_lt x y) = (term215 y x).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1632173 y x h1 h2) (fun h3 : term215 y x => @lem1631185 x y h1)). Qed.
Lemma lem1632177 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term215 y x.
Proof. exact (EQ_MP (@lem1632176 y x h1 h2) (@lem1631185 x y h1)). Qed.
Lemma lem1632178 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : (term52 x) = (term215 y x).
Proof. exact (prop_ext (fun h3 : term52 x => @lem1632177 y x h1 h2) (fun h3 : term215 y x => @lem1631186 x h2)). Qed.
Lemma lem1632179 (y : real) (x : real) (h1 : real_lt x y) (h2 : term52 x) : term215 y x.
Proof. exact (EQ_MP (@lem1632178 y x h1 h2) (@lem1631186 x h2)). Qed.
Lemma lem1632180 (y : real) (x : real) (h1 : term51 x y) (h2 : term52 x) : (real_lt x y) = (term215 y x).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1632179 y x h3 h2) (fun h3 : term215 y x => @lem1632174 x y h1)). Qed.
Lemma lem1632181 (y : real) (x : real) (h1 : term51 x y) (h2 : term52 x) : term215 y x.
Proof. exact (EQ_MP (@lem1632180 y x h1 h2) (@lem1632174 x y h1)). Qed.
Lemma lem1632182 (x : real) (y : real) (h1 : term51 x y) : (term52 x) = (term215 y x).
Proof. exact (prop_ext (fun h2 : term52 x => @lem1632181 y x h1 h2) (fun h2 : term215 y x => @lem1632175 x y h1)). Qed.
Lemma lem1632183 (x : real) (y : real) (h1 : term51 x y) : term215 y x.
Proof. exact (EQ_MP (@lem1632182 x y h1) (@lem1632175 x y h1)). Qed.
Lemma lem1632184 (y : real) (x : real) : term216 y x.
Proof. exact (fun h0 : term51 x y => @lem1632183 x y h0). Qed.
Lemma lem1632189 (x : real) : term217 x.
Proof. exact (fun y : real => @lem1632184 y x). Qed.
Lemma lem1632194 : term218.
Proof. exact (fun x : real => @lem1632189 x). Qed.
