Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_UNIQUE_GEN_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import REAL_SGN_EQ_spec.
Require Import REAL_SGN_NEG_spec.
Require Import REAL_SUB_0_spec.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1361604_spec.
Require Import thm1362040_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483454_spec.
Require Import thm1483460_spec.
Require Import thm1483472_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483490_spec.
Require Import thm1483498_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm4211_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1919106 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 ((real_neg x) = x) (x = term2)). Qed.
Lemma lem1919107 (x : real) : ((real_neg x) = x) = ((term3 x) = term2).
Proof. exact (@lem1483529 (real_neg x) x). Qed.
Lemma lem1919108 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919115 (x : real) : (real_neg x) = (term4 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1919116 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1919117 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1919116) (@lem1919115 x)). Qed.
Lemma lem1919118 (x : real) : (term3 x) = (term7 x).
Proof. exact (MK_COMB (@lem1919117 x) (@lem1919108 x)). Qed.
Lemma lem1919119 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem1483519 (term4 x) x). Qed.
Lemma lem1919123 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1483438 term10 term10 x). Qed.
Lemma lem1919124 : term11 = term12.
Proof. exact (@lem1367763 term13 term13). Qed.
Lemma lem1919125 : term14 = term15.
Proof. exact (@lem706885). Qed.
Lemma lem1919126 : (term14 = term15) = (term16 = term17).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term15). Qed.
Lemma lem1919127 : term16 = term17.
Proof. exact (EQ_MP (@lem1919126) (@lem1919125)). Qed.
Lemma lem1919128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919129 : term18 = term19.
Proof. exact (MK_COMB (@lem1919128) (@lem1919127)). Qed.
Lemma lem1919130 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919131 : term12 = term20.
Proof. exact (MK_COMB (@lem1919130) (@lem1919129)). Qed.
Lemma lem1919132 : term11 = term20.
Proof. exact (TRANS (@lem1919124) (@lem1919131)). Qed.
Lemma lem1919133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919134 : term21 = term22.
Proof. exact (MK_COMB (@lem1919133) (@lem1919132)). Qed.
Lemma lem1919135 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919136 (x : real) : (term9 x) = (term23 x).
Proof. exact (MK_COMB (@lem1919134) (@lem1919135 x)). Qed.
Lemma lem1919138 (x : real) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1919123 x) (@lem1919136 x)). Qed.
Lemma lem1919139 (x : real) : (term7 x) = (term23 x).
Proof. exact (TRANS (@lem1919119 x) (@lem1919138 x)). Qed.
Lemma lem1919140 (x : real) : (term3 x) = (term23 x).
Proof. exact (TRANS (@lem1919118 x) (@lem1919139 x)). Qed.
Lemma lem1919141 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1919142 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1919141) (@lem1919140 x)). Qed.
Lemma lem1919143 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919144 (x : real) : ((term3 x) = term2) = ((term23 x) = term2).
Proof. exact (MK_COMB (@lem1919142 x) (@lem1919143)). Qed.
Lemma lem1919145 (x : real) : ((real_neg x) = x) = ((term23 x) = term2).
Proof. exact (TRANS (@lem1919107 x) (@lem1919144 x)). Qed.
Lemma lem1919146 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483554 x term2). Qed.
Lemma lem1919152 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1919154 (x : nat) : (term30 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1919155 : term31 = term2.
Proof. exact (@lem1919154 term13). Qed.
Lemma lem1919156 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1919157 (x : real) : (term29 x) = (term32 x).
Proof. exact (MK_COMB (@lem1919156 x) (@lem1919155)). Qed.
Lemma lem1919158 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1919159 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1919157 x) (@lem1919158 x)). Qed.
Lemma lem1919161 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1919152 x) (@lem1919159 x)). Qed.
Lemma lem1919162 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919163 (x : real) : (term33 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1919162) (@lem1919161 x)). Qed.
Lemma lem1919166 (x : real) : (real_neg x) = (term4 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1919167 (x : real) : (term34 x) = (term34 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem1919168 (x : real) : ((term33 x) = (real_neg x)) = ((term33 x) = (term4 x)).
Proof. exact (MK_COMB (@lem1919167 x) (@lem1919166 x)). Qed.
Lemma lem1919169 (x : real) : (term33 x) = (term4 x).
Proof. exact (EQ_MP (@lem1919168 x) (@lem1919163 x)). Qed.
Lemma lem1919170 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919171 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1919170) (@lem1919169 x)). Qed.
Lemma lem1919172 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919173 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1919171 x) (@lem1919172)). Qed.
Lemma lem1919174 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919175 (x : real) : (term39 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1919174) (@lem1919161 x)). Qed.
Lemma lem1919176 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919177 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1919175 x) (@lem1919176)). Qed.
Lemma lem1919178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919179 (x : real) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem1919178) (@lem1919177 x)). Qed.
Lemma lem1919180 (x : real) : (term27 x) = (term44 x).
Proof. exact (MK_COMB (@lem1919179 x) (@lem1919173 x)). Qed.
Lemma lem1919181 (x : real) : (term26 x) = (term44 x).
Proof. exact (TRANS (@lem1919146 x) (@lem1919180 x)). Qed.
Lemma lem1919182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1919183 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1919182) (@lem1919145 x)). Qed.
Lemma lem1919184 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem1919183 x) (@lem1919181 x)). Qed.
Lemma lem1919185 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1483554 (real_neg x) x). Qed.
Lemma lem1919186 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919193 (x : real) : (real_neg x) = (term4 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1919194 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1919195 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1919194) (@lem1919193 x)). Qed.
Lemma lem1919196 (x : real) : (term3 x) = (term7 x).
Proof. exact (MK_COMB (@lem1919195 x) (@lem1919186 x)). Qed.
Lemma lem1919197 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem1483519 (term4 x) x). Qed.
Lemma lem1919201 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1483438 term10 term10 x). Qed.
Lemma lem1919202 : term11 = term12.
Proof. exact (@lem1367763 term13 term13). Qed.
Lemma lem1919203 : term14 = term15.
Proof. exact (@lem706885). Qed.
Lemma lem1919204 : (term14 = term15) = (term16 = term17).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term15). Qed.
Lemma lem1919205 : term16 = term17.
Proof. exact (EQ_MP (@lem1919204) (@lem1919203)). Qed.
Lemma lem1919206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919207 : term18 = term19.
Proof. exact (MK_COMB (@lem1919206) (@lem1919205)). Qed.
Lemma lem1919208 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919209 : term12 = term20.
Proof. exact (MK_COMB (@lem1919208) (@lem1919207)). Qed.
Lemma lem1919210 : term11 = term20.
Proof. exact (TRANS (@lem1919202) (@lem1919209)). Qed.
Lemma lem1919211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919212 : term21 = term22.
Proof. exact (MK_COMB (@lem1919211) (@lem1919210)). Qed.
Lemma lem1919213 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919214 (x : real) : (term9 x) = (term23 x).
Proof. exact (MK_COMB (@lem1919212) (@lem1919213 x)). Qed.
Lemma lem1919216 (x : real) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1919201 x) (@lem1919214 x)). Qed.
Lemma lem1919217 (x : real) : (term7 x) = (term23 x).
Proof. exact (TRANS (@lem1919197 x) (@lem1919216 x)). Qed.
Lemma lem1919218 (x : real) : (term3 x) = (term23 x).
Proof. exact (TRANS (@lem1919196 x) (@lem1919217 x)). Qed.
Lemma lem1919219 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919220 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1919219) (@lem1919218 x)). Qed.
Lemma lem1919221 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1483512 (term23 x)). Qed.
Lemma lem1919222 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1483476 term10 term20 x). Qed.
Lemma lem1919224 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919225 : term57 = term58.
Proof. exact (@lem1919224 term13 term17). Qed.
Lemma lem1919226 : term59 = term15.
Proof. exact (@lem996238 term15). Qed.
Lemma lem1919227 : (term59 = term15) = (term60 = term17).
Proof. exact (@lem1007663 (BIT1 0) term15 term15). Qed.
Lemma lem1919228 : term60 = term17.
Proof. exact (EQ_MP (@lem1919227) (@lem1919226)). Qed.
Lemma lem1919229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919230 : term58 = term19.
Proof. exact (MK_COMB (@lem1919229) (@lem1919228)). Qed.
Lemma lem1919231 : term57 = term19.
Proof. exact (TRANS (@lem1919225) (@lem1919230)). Qed.
Lemma lem1919232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919233 : term61 = term62.
Proof. exact (MK_COMB (@lem1919232) (@lem1919231)). Qed.
Lemma lem1919234 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919235 (x : real) : (term54 x) = (term63 x).
Proof. exact (MK_COMB (@lem1919233) (@lem1919234 x)). Qed.
Lemma lem1919236 (x : real) : (term53 x) = (term63 x).
Proof. exact (TRANS (@lem1919222 x) (@lem1919235 x)). Qed.
Lemma lem1919237 (x : real) : (term52 x) = (term63 x).
Proof. exact (TRANS (@lem1919221 x) (@lem1919236 x)). Qed.
Lemma lem1919238 (x : real) : (term64 x) = (term64 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1919239 (x : real) : ((term51 x) = (term52 x)) = ((term51 x) = (term63 x)).
Proof. exact (MK_COMB (@lem1919238 x) (@lem1919237 x)). Qed.
Lemma lem1919240 (x : real) : (term51 x) = (term63 x).
Proof. exact (EQ_MP (@lem1919239 x) (@lem1919220 x)). Qed.
Lemma lem1919241 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919242 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1919241) (@lem1919240 x)). Qed.
Lemma lem1919243 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919244 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1919242 x) (@lem1919243)). Qed.
Lemma lem1919245 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919246 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1919245) (@lem1919218 x)). Qed.
Lemma lem1919247 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919248 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1919246 x) (@lem1919247)). Qed.
Lemma lem1919249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919250 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1919249) (@lem1919248 x)). Qed.
Lemma lem1919251 (x : real) : (term50 x) = (term75 x).
Proof. exact (MK_COMB (@lem1919250 x) (@lem1919244 x)). Qed.
Lemma lem1919252 (x : real) : (term49 x) = (term75 x).
Proof. exact (TRANS (@lem1919185 x) (@lem1919251 x)). Qed.
Lemma lem1919253 (x : real) : (x = term2) = ((term28 x) = term2).
Proof. exact (@lem1483529 x term2). Qed.
Lemma lem1919259 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1919261 (x : nat) : (term30 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1919262 : term31 = term2.
Proof. exact (@lem1919261 term13). Qed.
Lemma lem1919263 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1919264 (x : real) : (term29 x) = (term32 x).
Proof. exact (MK_COMB (@lem1919263 x) (@lem1919262)). Qed.
Lemma lem1919265 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1919266 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1919264 x) (@lem1919265 x)). Qed.
Lemma lem1919268 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1919259 x) (@lem1919266 x)). Qed.
Lemma lem1919269 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1919270 (x : real) : (term76 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1919269) (@lem1919268 x)). Qed.
Lemma lem1919271 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919272 (x : real) : ((term28 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1919270 x) (@lem1919271)). Qed.
Lemma lem1919273 (x : real) : (x = term2) = (x = term2).
Proof. exact (TRANS (@lem1919253 x) (@lem1919272 x)). Qed.
Lemma lem1919274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1919275 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1919274) (@lem1919252 x)). Qed.
Lemma lem1919276 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1919275 x) (@lem1919273 x)). Qed.
Lemma lem1919277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919278 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1919277) (@lem1919184 x)). Qed.
Lemma lem1919279 (x : real) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1919278 x) (@lem1919276 x)). Qed.
Lemma lem1919286 (x : real) : (term0 x) = (term83 x).
Proof. exact (TRANS (@lem1919106 x) (@lem1919279 x)). Qed.
Lemma lem1919303 (x : real) : (term80 x) = (term84 x).
Proof. exact (@lem19367 (term72 x) (term68 x) (x = term2)). Qed.
Lemma lem1919320 (x : real) : (term48 x) = (term85 x).
Proof. exact (@lem19158 (term41 x) ((term23 x) = term2) (term38 x)). Qed.
Lemma lem1919321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919322 (x : real) : (term82 x) = (term86 x).
Proof. exact (MK_COMB (@lem1919321) (@lem1919320 x)). Qed.
Lemma lem1919323 (x : real) : (term83 x) = (term87 x).
Proof. exact (MK_COMB (@lem1919322 x) (@lem1919303 x)). Qed.
Lemma lem1919324 (x : real) : (term0 x) = (term87 x).
Proof. exact (TRANS (@lem1919286 x) (@lem1919323 x)). Qed.
Lemma lem1919346 (x : real) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1919347 (x : real) (h1 : term85 x) : term85 x.
Proof. exact (h1). Qed.
Lemma lem1919348 (x : real) (h1 : term88 x) : term88 x.
Proof. exact (h1). Qed.
Lemma lem1919349 (x : real) (h1 : term88 x) : term41 x.
Proof. exact (proj2 (@lem1919348 x h1)). Qed.
Lemma lem1919350 (x : real) (h1 : term88 x) : (term23 x) = term2.
Proof. exact (proj1 (@lem1919348 x h1)). Qed.
Lemma lem1919352 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919353 : term90 = term91.
Proof. exact (@lem1919352 (NUMERAL 0) term17). Qed.
Lemma lem1919354 : term92 = term15.
Proof. exact (@lem912803). Qed.
Lemma lem1919355 (h1 : term92 = term15) : term91 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term15 h1). Qed.
Lemma lem1919356 : (term92 = term15) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = term15 => @lem1919355 h1) (fun h1 : term91 = True => @lem1919354)). Qed.
Lemma lem1919357 : term91 = True.
Proof. exact (EQ_MP (@lem1919356) (@lem1919354)). Qed.
Lemma lem1919358 : term90 = True.
Proof. exact (TRANS (@lem1919353) (@lem1919357)). Qed.
Lemma lem1919359 : True = term90.
Proof. exact (SYM (@lem1919358)). Qed.
Lemma lem1919360 : term90.
Proof. exact (EQ_MP (@lem1919359) (@lem0)). Qed.
Lemma lem1919361 (x : real) (h1 : term88 x) : term93 x.
Proof. exact (conj (@lem1919360) (@lem1919349 x h1)). Qed.
Lemma lem1919363 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1919364 (x : real) : term95 x.
Proof. exact (@lem1919363 term19 x). Qed.
Lemma lem1919371 (x : real) (h1 : term88 x) : term68 x.
Proof. exact (@lem1919364 x (@lem1919361 x h1)). Qed.
Lemma lem1919373 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1919374 (x : real) : term97 x.
Proof. exact (@lem1919373 (term23 x)). Qed.
Lemma lem1919375 (x : real) (h1 : term88 x) : term98 x.
Proof. exact (@lem1919374 x (@lem1919350 x h1)). Qed.
Lemma lem1919376 (x : real) (h1 : term88 x) : term99 x.
Proof. exact (@lem1919375 x h1 term100). Qed.
Lemma lem1919377 (x : real) : (term99 x) = ((term101 x) = term2).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1919378 (x : real) (h1 : term88 x) : (term101 x) = term2.
Proof. exact (EQ_MP (@lem1919377 x) (@lem1919376 x h1)). Qed.
Lemma lem1919379 (x : real) : (term101 x) = (term23 x).
Proof. exact (@lem1483460 (term23 x)). Qed.
Lemma lem1919380 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1919381 (x : real) : (term102 x) = (term25 x).
Proof. exact (MK_COMB (@lem1919380) (@lem1919379 x)). Qed.
Lemma lem1919382 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919383 (x : real) : ((term101 x) = term2) = ((term23 x) = term2).
Proof. exact (MK_COMB (@lem1919381 x) (@lem1919382)). Qed.
Lemma lem1919384 (x : real) (h1 : term88 x) : (term23 x) = term2.
Proof. exact (EQ_MP (@lem1919383 x) (@lem1919378 x h1)). Qed.
Lemma lem1919385 (x : real) (h1 : term88 x) : term103 x.
Proof. exact (conj (@lem1919384 x h1) (@lem1919371 x h1)). Qed.
Lemma lem1919387 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1919388 (x : real) : term105 x.
Proof. exact (@lem1919387 (term23 x) (term63 x)). Qed.
Lemma lem1919389 (x : real) (h1 : term88 x) : term106 x.
Proof. exact (@lem1919388 x (@lem1919385 x h1)). Qed.
Lemma lem1919390 (x : real) : (term107 x) = (term108 x).
Proof. exact (@lem1483438 term20 term19 x). Qed.
Lemma lem1919392 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1919393 : term110 = term2.
Proof. exact (@lem1919392 term17). Qed.
Lemma lem1919394 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919395 : term111 = term112.
Proof. exact (MK_COMB (@lem1919394) (@lem1919393)). Qed.
Lemma lem1919396 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919397 (x : real) : (term108 x) = (term113 x).
Proof. exact (MK_COMB (@lem1919395) (@lem1919396 x)). Qed.
Lemma lem1919398 (x : real) : (term107 x) = (term113 x).
Proof. exact (TRANS (@lem1919390 x) (@lem1919397 x)). Qed.
Lemma lem1919399 (x : real) : (term113 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1919400 (x : real) : (term107 x) = term2.
Proof. exact (TRANS (@lem1919398 x) (@lem1919399 x)). Qed.
Lemma lem1919401 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919402 (x : real) : (term114 x) = term115.
Proof. exact (MK_COMB (@lem1919401) (@lem1919400 x)). Qed.
Lemma lem1919403 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919404 (x : real) : (term106 x) = term116.
Proof. exact (MK_COMB (@lem1919402 x) (@lem1919403)). Qed.
Lemma lem1919405 (x : real) (h1 : term88 x) : term116.
Proof. exact (EQ_MP (@lem1919404 x) (@lem1919389 x h1)). Qed.
Lemma lem1919407 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919408 : term116 = term117.
Proof. exact (@lem1919407 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1919409 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1919410 : term116 = False.
Proof. exact (TRANS (@lem1919408) (@lem1919409)). Qed.
Lemma lem1919411 (x : real) (h1 : term88 x) : False.
Proof. exact (EQ_MP (@lem1919410) (@lem1919405 x h1)). Qed.
Lemma lem1919412 (x : real) (h1 : term118 x) : term118 x.
Proof. exact (h1). Qed.
Lemma lem1919413 (x : real) (h1 : term118 x) : term38 x.
Proof. exact (proj2 (@lem1919412 x h1)). Qed.
Lemma lem1919414 (x : real) (h1 : term118 x) : (term23 x) = term2.
Proof. exact (proj1 (@lem1919412 x h1)). Qed.
Lemma lem1919416 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919417 : term90 = term91.
Proof. exact (@lem1919416 (NUMERAL 0) term17). Qed.
Lemma lem1919418 : term92 = term15.
Proof. exact (@lem912803). Qed.
Lemma lem1919419 (h1 : term92 = term15) : term91 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term15 h1). Qed.
Lemma lem1919420 : (term92 = term15) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = term15 => @lem1919419 h1) (fun h1 : term91 = True => @lem1919418)). Qed.
Lemma lem1919421 : term91 = True.
Proof. exact (EQ_MP (@lem1919420) (@lem1919418)). Qed.
Lemma lem1919422 : term90 = True.
Proof. exact (TRANS (@lem1919417) (@lem1919421)). Qed.
Lemma lem1919423 : True = term90.
Proof. exact (SYM (@lem1919422)). Qed.
Lemma lem1919424 : term90.
Proof. exact (EQ_MP (@lem1919423) (@lem0)). Qed.
Lemma lem1919425 (x : real) (h1 : term118 x) : term119 x.
Proof. exact (conj (@lem1919424) (@lem1919413 x h1)). Qed.
Lemma lem1919427 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1919428 (x : real) : term120 x.
Proof. exact (@lem1919427 term19 (term4 x)). Qed.
Lemma lem1919429 (x : real) (h1 : term118 x) : term121 x.
Proof. exact (@lem1919428 x (@lem1919425 x h1)). Qed.
Lemma lem1919430 (x : real) : (term122 x) = (term123 x).
Proof. exact (@lem1483476 term19 term10 x). Qed.
Lemma lem1919432 (m : nat) (n : nat) : (term124 m n) = (term125 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1919433 : term126 = term127.
Proof. exact (@lem1919432 term17 term13). Qed.
Lemma lem1919434 : term128 = term15.
Proof. exact (@lem996237 term15). Qed.
Lemma lem1919435 : (term128 = term15) = (term129 = term17).
Proof. exact (@lem1007663 term15 (BIT1 0) term15). Qed.
Lemma lem1919436 : term129 = term17.
Proof. exact (EQ_MP (@lem1919435) (@lem1919434)). Qed.
Lemma lem1919437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919438 : term130 = term19.
Proof. exact (MK_COMB (@lem1919437) (@lem1919436)). Qed.
Lemma lem1919439 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919440 : term127 = term20.
Proof. exact (MK_COMB (@lem1919439) (@lem1919438)). Qed.
Lemma lem1919441 : term126 = term20.
Proof. exact (TRANS (@lem1919433) (@lem1919440)). Qed.
Lemma lem1919442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919443 : term131 = term22.
Proof. exact (MK_COMB (@lem1919442) (@lem1919441)). Qed.
Lemma lem1919444 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919445 (x : real) : (term123 x) = (term23 x).
Proof. exact (MK_COMB (@lem1919443) (@lem1919444 x)). Qed.
Lemma lem1919446 (x : real) : (term122 x) = (term23 x).
Proof. exact (TRANS (@lem1919430 x) (@lem1919445 x)). Qed.
Lemma lem1919447 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919448 (x : real) : (term132 x) = (term70 x).
Proof. exact (MK_COMB (@lem1919447) (@lem1919446 x)). Qed.
Lemma lem1919449 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919450 (x : real) : (term121 x) = (term72 x).
Proof. exact (MK_COMB (@lem1919448 x) (@lem1919449)). Qed.
Lemma lem1919451 (x : real) (h1 : term118 x) : term72 x.
Proof. exact (EQ_MP (@lem1919450 x) (@lem1919429 x h1)). Qed.
Lemma lem1919453 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1919454 (x : real) : term97 x.
Proof. exact (@lem1919453 (term23 x)). Qed.
Lemma lem1919455 (x : real) (h1 : term118 x) : term98 x.
Proof. exact (@lem1919454 x (@lem1919414 x h1)). Qed.
Lemma lem1919456 (x : real) (h1 : term118 x) : term133 x.
Proof. exact (@lem1919455 x h1 term10). Qed.
Lemma lem1919457 (x : real) : (term133 x) = ((term53 x) = term2).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1919458 (x : real) (h1 : term118 x) : (term53 x) = term2.
Proof. exact (EQ_MP (@lem1919457 x) (@lem1919456 x h1)). Qed.
Lemma lem1919459 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1483476 term10 term20 x). Qed.
Lemma lem1919461 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919462 : term57 = term58.
Proof. exact (@lem1919461 term13 term17). Qed.
Lemma lem1919463 : term59 = term15.
Proof. exact (@lem996238 term15). Qed.
Lemma lem1919464 : (term59 = term15) = (term60 = term17).
Proof. exact (@lem1007663 (BIT1 0) term15 term15). Qed.
Lemma lem1919465 : term60 = term17.
Proof. exact (EQ_MP (@lem1919464) (@lem1919463)). Qed.
Lemma lem1919466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919467 : term58 = term19.
Proof. exact (MK_COMB (@lem1919466) (@lem1919465)). Qed.
Lemma lem1919468 : term57 = term19.
Proof. exact (TRANS (@lem1919462) (@lem1919467)). Qed.
Lemma lem1919469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919470 : term61 = term62.
Proof. exact (MK_COMB (@lem1919469) (@lem1919468)). Qed.
Lemma lem1919471 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919472 (x : real) : (term54 x) = (term63 x).
Proof. exact (MK_COMB (@lem1919470) (@lem1919471 x)). Qed.
Lemma lem1919473 (x : real) : (term53 x) = (term63 x).
Proof. exact (TRANS (@lem1919459 x) (@lem1919472 x)). Qed.
Lemma lem1919474 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1919475 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1919474) (@lem1919473 x)). Qed.
Lemma lem1919476 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919477 (x : real) : ((term53 x) = term2) = ((term63 x) = term2).
Proof. exact (MK_COMB (@lem1919475 x) (@lem1919476)). Qed.
Lemma lem1919478 (x : real) (h1 : term118 x) : (term63 x) = term2.
Proof. exact (EQ_MP (@lem1919477 x) (@lem1919458 x h1)). Qed.
Lemma lem1919479 (x : real) (h1 : term118 x) : term136 x.
Proof. exact (conj (@lem1919478 x h1) (@lem1919451 x h1)). Qed.
Lemma lem1919481 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1919482 (x : real) : term137 x.
Proof. exact (@lem1919481 (term63 x) (term23 x)). Qed.
Lemma lem1919483 (x : real) (h1 : term118 x) : term138 x.
Proof. exact (@lem1919482 x (@lem1919479 x h1)). Qed.
Lemma lem1919484 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1483438 term19 term20 x). Qed.
Lemma lem1919486 (m : nat) : (term141 m) = term2.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1919487 : term142 = term2.
Proof. exact (@lem1919486 term17). Qed.
Lemma lem1919488 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919489 : term143 = term112.
Proof. exact (MK_COMB (@lem1919488) (@lem1919487)). Qed.
Lemma lem1919490 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919491 (x : real) : (term140 x) = (term113 x).
Proof. exact (MK_COMB (@lem1919489) (@lem1919490 x)). Qed.
Lemma lem1919492 (x : real) : (term139 x) = (term113 x).
Proof. exact (TRANS (@lem1919484 x) (@lem1919491 x)). Qed.
Lemma lem1919493 (x : real) : (term113 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1919494 (x : real) : (term139 x) = term2.
Proof. exact (TRANS (@lem1919492 x) (@lem1919493 x)). Qed.
Lemma lem1919495 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919496 (x : real) : (term144 x) = term115.
Proof. exact (MK_COMB (@lem1919495) (@lem1919494 x)). Qed.
Lemma lem1919497 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919498 (x : real) : (term138 x) = term116.
Proof. exact (MK_COMB (@lem1919496 x) (@lem1919497)). Qed.
Lemma lem1919499 (x : real) (h1 : term118 x) : term116.
Proof. exact (EQ_MP (@lem1919498 x) (@lem1919483 x h1)). Qed.
Lemma lem1919501 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919502 : term116 = term117.
Proof. exact (@lem1919501 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1919503 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1919504 : term116 = False.
Proof. exact (TRANS (@lem1919502) (@lem1919503)). Qed.
Lemma lem1919505 (x : real) (h1 : term118 x) : False.
Proof. exact (EQ_MP (@lem1919504) (@lem1919499 x h1)). Qed.
Lemma lem1919506 (x : real) (h1 : term85 x) : False.
Proof. exact (or_elim (@lem1919347 x h1) (fun h0 : term88 x => @lem1919411 x h0) (fun h0 : term118 x => @lem1919505 x h0)). Qed.
Lemma lem1919507 (x : real) (h1 : term84 x) : term84 x.
Proof. exact (h1). Qed.
Lemma lem1919508 (x : real) (h1 : term145 x) : term145 x.
Proof. exact (h1). Qed.
Lemma lem1919509 (x : real) (h1 : term145 x) : x = term2.
Proof. exact (proj2 (@lem1919508 x h1)). Qed.
Lemma lem1919510 (x : real) (h1 : term145 x) : term72 x.
Proof. exact (proj1 (@lem1919508 x h1)). Qed.
Lemma lem1919512 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919513 : term146 = term147.
Proof. exact (@lem1919512 (NUMERAL 0) term13). Qed.
Lemma lem1919514 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1919515 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1919516 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1919515 h1) (fun h1 : term147 = True => @lem1919514)). Qed.
Lemma lem1919517 : term147 = True.
Proof. exact (EQ_MP (@lem1919516) (@lem1919514)). Qed.
Lemma lem1919518 : term146 = True.
Proof. exact (TRANS (@lem1919513) (@lem1919517)). Qed.
Lemma lem1919519 : True = term146.
Proof. exact (SYM (@lem1919518)). Qed.
Lemma lem1919520 : term146.
Proof. exact (EQ_MP (@lem1919519) (@lem0)). Qed.
Lemma lem1919521 (x : real) (h1 : term145 x) : term149 x.
Proof. exact (conj (@lem1919520) (@lem1919510 x h1)). Qed.
Lemma lem1919523 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1919524 (x : real) : term150 x.
Proof. exact (@lem1919523 term100 (term23 x)). Qed.
Lemma lem1919525 (x : real) (h1 : term145 x) : term151 x.
Proof. exact (@lem1919524 x (@lem1919521 x h1)). Qed.
Lemma lem1919526 (x : real) : (term101 x) = (term23 x).
Proof. exact (@lem1483460 (term23 x)). Qed.
Lemma lem1919527 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919528 (x : real) : (term152 x) = (term70 x).
Proof. exact (MK_COMB (@lem1919527) (@lem1919526 x)). Qed.
Lemma lem1919529 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919530 (x : real) : (term151 x) = (term72 x).
Proof. exact (MK_COMB (@lem1919528 x) (@lem1919529)). Qed.
Lemma lem1919531 (x : real) (h1 : term145 x) : term72 x.
Proof. exact (EQ_MP (@lem1919530 x) (@lem1919525 x h1)). Qed.
Lemma lem1919533 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1919534 (x : real) : term96 x.
Proof. exact (@lem1919533 x). Qed.
Lemma lem1919535 (x : real) (h1 : term145 x) : term153 x.
Proof. exact (@lem1919534 x (@lem1919509 x h1)). Qed.
Lemma lem1919536 (x : real) (h1 : term145 x) : term154 x.
Proof. exact (@lem1919535 x h1 term19). Qed.
Lemma lem1919537 (x : real) : (term154 x) = ((term63 x) = term2).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1919544 (x : real) (h1 : term145 x) : (term63 x) = term2.
Proof. exact (EQ_MP (@lem1919537 x) (@lem1919536 x h1)). Qed.
Lemma lem1919545 (x : real) (h1 : term145 x) : term136 x.
Proof. exact (conj (@lem1919544 x h1) (@lem1919531 x h1)). Qed.
Lemma lem1919547 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1919548 (x : real) : term137 x.
Proof. exact (@lem1919547 (term63 x) (term23 x)). Qed.
Lemma lem1919549 (x : real) (h1 : term145 x) : term138 x.
Proof. exact (@lem1919548 x (@lem1919545 x h1)). Qed.
Lemma lem1919550 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1483438 term19 term20 x). Qed.
Lemma lem1919552 (m : nat) : (term141 m) = term2.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1919553 : term142 = term2.
Proof. exact (@lem1919552 term17). Qed.
Lemma lem1919554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919555 : term143 = term112.
Proof. exact (MK_COMB (@lem1919554) (@lem1919553)). Qed.
Lemma lem1919556 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919557 (x : real) : (term140 x) = (term113 x).
Proof. exact (MK_COMB (@lem1919555) (@lem1919556 x)). Qed.
Lemma lem1919558 (x : real) : (term139 x) = (term113 x).
Proof. exact (TRANS (@lem1919550 x) (@lem1919557 x)). Qed.
Lemma lem1919559 (x : real) : (term113 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1919560 (x : real) : (term139 x) = term2.
Proof. exact (TRANS (@lem1919558 x) (@lem1919559 x)). Qed.
Lemma lem1919561 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919562 (x : real) : (term144 x) = term115.
Proof. exact (MK_COMB (@lem1919561) (@lem1919560 x)). Qed.
Lemma lem1919563 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919564 (x : real) : (term138 x) = term116.
Proof. exact (MK_COMB (@lem1919562 x) (@lem1919563)). Qed.
Lemma lem1919565 (x : real) (h1 : term145 x) : term116.
Proof. exact (EQ_MP (@lem1919564 x) (@lem1919549 x h1)). Qed.
Lemma lem1919567 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919568 : term116 = term117.
Proof. exact (@lem1919567 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1919569 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1919570 : term116 = False.
Proof. exact (TRANS (@lem1919568) (@lem1919569)). Qed.
Lemma lem1919571 (x : real) (h1 : term145 x) : False.
Proof. exact (EQ_MP (@lem1919570) (@lem1919565 x h1)). Qed.
Lemma lem1919572 (x : real) (h1 : term155 x) : term155 x.
Proof. exact (h1). Qed.
Lemma lem1919573 (x : real) (h1 : term155 x) : x = term2.
Proof. exact (proj2 (@lem1919572 x h1)). Qed.
Lemma lem1919574 (x : real) (h1 : term155 x) : term68 x.
Proof. exact (proj1 (@lem1919572 x h1)). Qed.
Lemma lem1919576 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919577 : term146 = term147.
Proof. exact (@lem1919576 (NUMERAL 0) term13). Qed.
Lemma lem1919578 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1919579 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1919580 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1919579 h1) (fun h1 : term147 = True => @lem1919578)). Qed.
Lemma lem1919581 : term147 = True.
Proof. exact (EQ_MP (@lem1919580) (@lem1919578)). Qed.
Lemma lem1919582 : term146 = True.
Proof. exact (TRANS (@lem1919577) (@lem1919581)). Qed.
Lemma lem1919583 : True = term146.
Proof. exact (SYM (@lem1919582)). Qed.
Lemma lem1919584 : term146.
Proof. exact (EQ_MP (@lem1919583) (@lem0)). Qed.
Lemma lem1919585 (x : real) (h1 : term155 x) : term156 x.
Proof. exact (conj (@lem1919584) (@lem1919574 x h1)). Qed.
Lemma lem1919587 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1919588 (x : real) : term157 x.
Proof. exact (@lem1919587 term100 (term63 x)). Qed.
Lemma lem1919589 (x : real) (h1 : term155 x) : term158 x.
Proof. exact (@lem1919588 x (@lem1919585 x h1)). Qed.
Lemma lem1919590 (x : real) : (term159 x) = (term63 x).
Proof. exact (@lem1483460 (term63 x)). Qed.
Lemma lem1919591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919592 (x : real) : (term160 x) = (term66 x).
Proof. exact (MK_COMB (@lem1919591) (@lem1919590 x)). Qed.
Lemma lem1919593 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919594 (x : real) : (term158 x) = (term68 x).
Proof. exact (MK_COMB (@lem1919592 x) (@lem1919593)). Qed.
Lemma lem1919595 (x : real) (h1 : term155 x) : term68 x.
Proof. exact (EQ_MP (@lem1919594 x) (@lem1919589 x h1)). Qed.
Lemma lem1919597 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1919598 (x : real) : term96 x.
Proof. exact (@lem1919597 x). Qed.
Lemma lem1919599 (x : real) (h1 : term155 x) : term153 x.
Proof. exact (@lem1919598 x (@lem1919573 x h1)). Qed.
Lemma lem1919600 (x : real) (h1 : term155 x) : term161 x.
Proof. exact (@lem1919599 x h1 term20). Qed.
Lemma lem1919601 (x : real) : (term161 x) = ((term23 x) = term2).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1919608 (x : real) (h1 : term155 x) : (term23 x) = term2.
Proof. exact (EQ_MP (@lem1919601 x) (@lem1919600 x h1)). Qed.
Lemma lem1919609 (x : real) (h1 : term155 x) : term103 x.
Proof. exact (conj (@lem1919608 x h1) (@lem1919595 x h1)). Qed.
Lemma lem1919611 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1919612 (x : real) : term105 x.
Proof. exact (@lem1919611 (term23 x) (term63 x)). Qed.
Lemma lem1919613 (x : real) (h1 : term155 x) : term106 x.
Proof. exact (@lem1919612 x (@lem1919609 x h1)). Qed.
Lemma lem1919614 (x : real) : (term107 x) = (term108 x).
Proof. exact (@lem1483438 term20 term19 x). Qed.
Lemma lem1919616 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1919617 : term110 = term2.
Proof. exact (@lem1919616 term17). Qed.
Lemma lem1919618 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919619 : term111 = term112.
Proof. exact (MK_COMB (@lem1919618) (@lem1919617)). Qed.
Lemma lem1919620 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1919621 (x : real) : (term108 x) = (term113 x).
Proof. exact (MK_COMB (@lem1919619) (@lem1919620 x)). Qed.
Lemma lem1919622 (x : real) : (term107 x) = (term113 x).
Proof. exact (TRANS (@lem1919614 x) (@lem1919621 x)). Qed.
Lemma lem1919623 (x : real) : (term113 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1919624 (x : real) : (term107 x) = term2.
Proof. exact (TRANS (@lem1919622 x) (@lem1919623 x)). Qed.
Lemma lem1919625 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919626 (x : real) : (term114 x) = term115.
Proof. exact (MK_COMB (@lem1919625) (@lem1919624 x)). Qed.
Lemma lem1919627 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919628 (x : real) : (term106 x) = term116.
Proof. exact (MK_COMB (@lem1919626 x) (@lem1919627)). Qed.
Lemma lem1919629 (x : real) (h1 : term155 x) : term116.
Proof. exact (EQ_MP (@lem1919628 x) (@lem1919613 x h1)). Qed.
Lemma lem1919631 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1919632 : term116 = term117.
Proof. exact (@lem1919631 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1919633 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1919634 : term116 = False.
Proof. exact (TRANS (@lem1919632) (@lem1919633)). Qed.
Lemma lem1919635 (x : real) (h1 : term155 x) : False.
Proof. exact (EQ_MP (@lem1919634) (@lem1919629 x h1)). Qed.
Lemma lem1919636 (x : real) (h1 : term84 x) : False.
Proof. exact (or_elim (@lem1919507 x h1) (fun h0 : term145 x => @lem1919571 x h0) (fun h0 : term155 x => @lem1919635 x h0)). Qed.
Lemma lem1919637 (x : real) (h1 : term87 x) : False.
Proof. exact (or_elim (@lem1919346 x h1) (fun h0 : term85 x => @lem1919506 x h0) (fun h0 : term84 x => @lem1919636 x h0)). Qed.
Lemma lem1919639 (x : real) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1919640 (x : real) (h1 : term87 x) : (term87 x) = False.
Proof. exact (prop_ext (fun h2 : term87 x => @lem1919637 x h1) (fun h2 : False => @lem1919639 x h1)). Qed.
Lemma lem1919641 (x : real) (h1 : term87 x) : False.
Proof. exact (EQ_MP (@lem1919640 x h1) (@lem1919639 x h1)). Qed.
Lemma lem1919642 (x : real) (h1 : term0 x) : term0 x.
Proof. exact (h1). Qed.
Lemma lem1919643 (x : real) (h1 : term0 x) : term87 x.
Proof. exact (EQ_MP (@lem1919324 x) (@lem1919642 x h1)). Qed.
Lemma lem1919644 (x : real) (h1 : term0 x) : (term87 x) = False.
Proof. exact (prop_ext (fun h2 : term87 x => @lem1919641 x h2) (fun h2 : False => @lem1919643 x h1)). Qed.
Lemma lem1919645 (x : real) (h1 : term0 x) : False.
Proof. exact (EQ_MP (@lem1919644 x h1) (@lem1919643 x h1)). Qed.
Lemma lem1919646 (x : real) : term162 x.
Proof. exact (fun h0 : term0 x => @lem1919645 x h0). Qed.
Lemma lem1919647 (x : real) : term163 x.
Proof. exact (@lem1386578 (((real_neg x) = x) = (x = term2))). Qed.
Lemma lem1919658 : term164.
Proof. exact (proj1 (@lem1740125)). Qed.
Lemma lem1919659 (x : real) : term165 x.
Proof. exact (@lem1919658 x). Qed.
Lemma lem1919660 (x : real) : (term165 x) = (((real_sgn x) = term2) = (x = term2)).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1919698 (x : real) (y : real) : (term166 x y) = (term167 x y).
Proof. exact (@lem17646 ((term168 x) = (term168 y)) ((term169 x y) = term2)). Qed.
Lemma lem1919699 (x : real) (y : real) : ((term168 x) = (term168 y)) = ((term170 x y) = term2).
Proof. exact (@lem1483529 (term168 x) (term168 y)). Qed.
Lemma lem1919724 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (@lem1483519 (term168 x) (term168 y)). Qed.
Lemma lem1919725 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1919726 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1919725) (@lem1919724 x y)). Qed.
Lemma lem1919727 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919728 (x : real) (y : real) : ((term170 x y) = term2) = ((term171 x y) = term2).
Proof. exact (MK_COMB (@lem1919726 x y) (@lem1919727)). Qed.
Lemma lem1919729 (x : real) (y : real) : ((term168 x) = (term168 y)) = ((term171 x y) = term2).
Proof. exact (TRANS (@lem1919699 x y) (@lem1919728 x y)). Qed.
Lemma lem1919730 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483554 (term169 x y) term2). Qed.
Lemma lem1919731 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919738 (y : real) : (real_neg y) = (term4 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1919741 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1919742 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem1919741 x) (@lem1919738 y)). Qed.
Lemma lem1919743 (x : real) (y : real) : (term177 x y) = (term178 x y).
Proof. exact (@lem1483519 x (term4 y)). Qed.
Lemma lem1919744 (y : real) : (term179 y) = (term180 y).
Proof. exact (@lem1483476 term10 term10 y). Qed.
Lemma lem1919746 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919747 : term181 = term182.
Proof. exact (@lem1919746 term13 term13). Qed.
Lemma lem1919748 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1919749 : term184 = term13.
Proof. exact (EQ_MP (@lem1919748) (@lem940073)). Qed.
Lemma lem1919750 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919751 : term182 = term100.
Proof. exact (MK_COMB (@lem1919750) (@lem1919749)). Qed.
Lemma lem1919752 : term181 = term100.
Proof. exact (TRANS (@lem1919747) (@lem1919751)). Qed.
Lemma lem1919753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919754 : term185 = term186.
Proof. exact (MK_COMB (@lem1919753) (@lem1919752)). Qed.
Lemma lem1919755 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1919756 (y : real) : (term180 y) = (term187 y).
Proof. exact (MK_COMB (@lem1919754) (@lem1919755 y)). Qed.
Lemma lem1919757 (y : real) : (term179 y) = (term187 y).
Proof. exact (TRANS (@lem1919744 y) (@lem1919756 y)). Qed.
Lemma lem1919758 (y : real) : (term187 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1919759 (y : real) : (term179 y) = y.
Proof. exact (TRANS (@lem1919757 y) (@lem1919758 y)). Qed.
Lemma lem1919760 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1919763 (x : real) (y : real) : (term178 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1919760 x) (@lem1919759 y)). Qed.
Lemma lem1919764 (x : real) (y : real) : (term177 x y) = (real_add x y).
Proof. exact (TRANS (@lem1919743 x y) (@lem1919763 x y)). Qed.
Lemma lem1919765 (x : real) (y : real) : (term176 x y) = (real_add x y).
Proof. exact (TRANS (@lem1919742 x y) (@lem1919764 x y)). Qed.
Lemma lem1919778 (x : real) (y : real) : (real_sub x y) = (term188 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1919779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919780 (x : real) (y : real) : (term189 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1919779) (@lem1919778 x y)). Qed.
Lemma lem1919781 (x : real) (y : real) : (term169 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem1919780 x y) (@lem1919765 x y)). Qed.
Lemma lem1919782 (x : real) (y : real) : (term191 x y) = (term192 x y).
Proof. exact (@lem1483454 x (term4 y) (real_add x y)). Qed.
Lemma lem1919783 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (@lem1483508 x x y). Qed.
Lemma lem1919784 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1919785 (x : real) : (real_mul x x) = (term168 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1919786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1919787 (x : real) : (term195 x) = (term196 x).
Proof. exact (MK_COMB (@lem1919786) (@lem1919785 x)). Qed.
Lemma lem1919788 (x : real) (y : real) : (term194 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1919787 x) (@lem1919784 x y)). Qed.
Lemma lem1919789 (x : real) (y : real) : (term193 x y) = (term197 x y).
Proof. exact (TRANS (@lem1919783 x y) (@lem1919788 x y)). Qed.
Lemma lem1919790 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1919791 (x : real) (y : real) : (term198 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem1919790) (@lem1919789 x y)). Qed.
Lemma lem1919792 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (@lem1483508 x (term4 y) y). Qed.
Lemma lem1919793 (y : real) : (term202 y) = (term203 y).
Proof. exact (@lem1483472 term10 y y). Qed.
Lemma lem1919794 (y : real) : (real_mul y y) = (term168 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1919795 : term204 = term204.
Proof. exact (eq_refl term204). Qed.
Lemma lem1919796 (y : real) : (term203 y) = (term205 y).
Proof. exact (MK_COMB (@lem1919795) (@lem1919794 y)). Qed.
Lemma lem1919797 (y : real) : (term202 y) = (term205 y).
Proof. exact (TRANS (@lem1919793 y) (@lem1919796 y)). Qed.
Lemma lem1919798 (y : real) (x : real) : (term206 y x) = (term207 y x).
Proof. exact (@lem1483472 term10 y x). Qed.
Lemma lem1919799 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1919800 : term204 = term204.
Proof. exact (eq_refl term204). Qed.
Lemma lem1919801 (x : real) (y : real) : (term207 y x) = (term207 x y).
Proof. exact (MK_COMB (@lem1919800) (@lem1919799 x y)). Qed.
Lemma lem1919802 (x : real) (y : real) : (term206 y x) = (term207 x y).
Proof. exact (TRANS (@lem1919798 y x) (@lem1919801 x y)). Qed.
Lemma lem1919803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1919804 (x : real) (y : real) : (term208 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem1919803) (@lem1919802 x y)). Qed.
Lemma lem1919805 (x : real) (y : real) : (term201 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1919804 x y) (@lem1919797 y)). Qed.
Lemma lem1919806 (x : real) (y : real) : (term200 x y) = (term210 x y).
Proof. exact (TRANS (@lem1919792 x y) (@lem1919805 x y)). Qed.
Lemma lem1919807 (x : real) (y : real) : (term192 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1919791 x y) (@lem1919806 x y)). Qed.
Lemma lem1919808 (x : real) (y : real) : (term191 x y) = (term211 x y).
Proof. exact (TRANS (@lem1919782 x y) (@lem1919807 x y)). Qed.
Lemma lem1919809 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1483482 (term168 x) (real_mul x y) (term210 x y)). Qed.
Lemma lem1919810 (x : real) (y : real) : (term213 x y) = (term214 x y).
Proof. exact (@lem1483490 (real_mul x y) (term207 x y) (term205 y)). Qed.
Lemma lem1919811 (x : real) (y : real) : (term215 x y) = (term216 x y).
Proof. exact (@lem1483442 term10 (real_mul x y)). Qed.
Lemma lem1919813 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1919814 : term217 = term2.
Proof. exact (@lem1919813 term13). Qed.
Lemma lem1919815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919816 : term218 = term112.
Proof. exact (MK_COMB (@lem1919815) (@lem1919814)). Qed.
Lemma lem1919817 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1919818 (x : real) (y : real) : (term216 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1919816) (@lem1919817 x y)). Qed.
Lemma lem1919819 (x : real) (y : real) : (term215 x y) = (term219 x y).
Proof. exact (TRANS (@lem1919811 x y) (@lem1919818 x y)). Qed.
Lemma lem1919820 (x : real) (y : real) : (term219 x y) = term2.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1919821 (x : real) (y : real) : (term215 x y) = term2.
Proof. exact (TRANS (@lem1919819 x y) (@lem1919820 x y)). Qed.
Lemma lem1919822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1919823 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1919822) (@lem1919821 x y)). Qed.
Lemma lem1919824 (y : real) : (term205 y) = (term205 y).
Proof. exact (eq_refl (term205 y)). Qed.
Lemma lem1919825 (x : real) (y : real) : (term214 x y) = (term222 y).
Proof. exact (MK_COMB (@lem1919823 x y) (@lem1919824 y)). Qed.
Lemma lem1919826 (x : real) (y : real) : (term213 x y) = (term222 y).
Proof. exact (TRANS (@lem1919810 x y) (@lem1919825 x y)). Qed.
Lemma lem1919827 (y : real) : (term222 y) = (term205 y).
Proof. exact (@lem1483448 (term205 y)). Qed.
Lemma lem1919828 (x : real) (y : real) : (term213 x y) = (term205 y).
Proof. exact (TRANS (@lem1919826 x y) (@lem1919827 y)). Qed.
Lemma lem1919829 (x : real) : (term196 x) = (term196 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem1919830 (x : real) (y : real) : (term212 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1919829 x) (@lem1919828 x y)). Qed.
Lemma lem1919831 (x : real) (y : real) : (term211 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919809 x y) (@lem1919830 x y)). Qed.
Lemma lem1919832 (x : real) (y : real) : (term191 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919808 x y) (@lem1919831 x y)). Qed.
Lemma lem1919833 (x : real) (y : real) : (term169 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919781 x y) (@lem1919832 x y)). Qed.
Lemma lem1919834 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1919835 (x : real) (y : real) : (term223 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1919834) (@lem1919833 x y)). Qed.
Lemma lem1919836 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem1919835 x y) (@lem1919731)). Qed.
Lemma lem1919837 (x : real) (y : real) : (term226 x y) = (term227 x y).
Proof. exact (@lem1483519 (term171 x y) term2). Qed.
Lemma lem1919839 (x : nat) : (term30 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1919840 : term31 = term2.
Proof. exact (@lem1919839 term13). Qed.
Lemma lem1919841 (x : real) (y : real) : (term228 x y) = (term228 x y).
Proof. exact (eq_refl (term228 x y)). Qed.
Lemma lem1919842 (x : real) (y : real) : (term227 x y) = (term229 x y).
Proof. exact (MK_COMB (@lem1919841 x y) (@lem1919840)). Qed.
Lemma lem1919843 (x : real) (y : real) : (term229 x y) = (term171 x y).
Proof. exact (@lem1483450 (term171 x y)). Qed.
Lemma lem1919844 (x : real) (y : real) : (term227 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919842 x y) (@lem1919843 x y)). Qed.
Lemma lem1919845 (x : real) (y : real) : (term226 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919837 x y) (@lem1919844 x y)). Qed.
Lemma lem1919846 (x : real) (y : real) : (term225 x y) = (term171 x y).
Proof. exact (TRANS (@lem1919836 x y) (@lem1919845 x y)). Qed.
Lemma lem1919847 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919848 (x : real) (y : real) : (term230 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem1919847) (@lem1919846 x y)). Qed.
Lemma lem1919849 (x : real) (y : real) : (term231 x y) = (term232 x y).
Proof. exact (@lem1483512 (term171 x y)). Qed.
Lemma lem1919850 (x : real) (y : real) : (term232 x y) = (term233 x y).
Proof. exact (@lem1483508 (term168 x) term10 (term205 y)). Qed.
Lemma lem1919851 (y : real) : (term234 y) = (term235 y).
Proof. exact (@lem1483476 term10 term10 (term168 y)). Qed.
Lemma lem1919853 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919854 : term181 = term182.
Proof. exact (@lem1919853 term13 term13). Qed.
Lemma lem1919855 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1919856 : term184 = term13.
Proof. exact (EQ_MP (@lem1919855) (@lem940073)). Qed.
Lemma lem1919857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919858 : term182 = term100.
Proof. exact (MK_COMB (@lem1919857) (@lem1919856)). Qed.
Lemma lem1919859 : term181 = term100.
Proof. exact (TRANS (@lem1919854) (@lem1919858)). Qed.
Lemma lem1919860 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919861 : term185 = term186.
Proof. exact (MK_COMB (@lem1919860) (@lem1919859)). Qed.
Lemma lem1919862 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1919863 (y : real) : (term235 y) = (term236 y).
Proof. exact (MK_COMB (@lem1919861) (@lem1919862 y)). Qed.
Lemma lem1919864 (y : real) : (term234 y) = (term236 y).
Proof. exact (TRANS (@lem1919851 y) (@lem1919863 y)). Qed.
Lemma lem1919865 (y : real) : (term236 y) = (term168 y).
Proof. exact (@lem1483436 (term168 y)). Qed.
Lemma lem1919866 (y : real) : (term234 y) = (term168 y).
Proof. exact (TRANS (@lem1919864 y) (@lem1919865 y)). Qed.
Lemma lem1919869 (x : real) : (term237 x) = (term237 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1919870 (x : real) (y : real) : (term233 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1919869 x) (@lem1919866 y)). Qed.
Lemma lem1919871 (x : real) (y : real) : (term232 x y) = (term238 x y).
Proof. exact (TRANS (@lem1919850 x y) (@lem1919870 x y)). Qed.
Lemma lem1919872 (x : real) (y : real) : (term231 x y) = (term238 x y).
Proof. exact (TRANS (@lem1919849 x y) (@lem1919871 x y)). Qed.
Lemma lem1919873 (x : real) (y : real) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem1919874 (x : real) (y : real) : ((term230 x y) = (term231 x y)) = ((term230 x y) = (term238 x y)).
Proof. exact (MK_COMB (@lem1919873 x y) (@lem1919872 x y)). Qed.
Lemma lem1919875 (x : real) (y : real) : (term230 x y) = (term238 x y).
Proof. exact (EQ_MP (@lem1919874 x y) (@lem1919848 x y)). Qed.
Lemma lem1919876 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919877 (x : real) (y : real) : (term240 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1919876) (@lem1919875 x y)). Qed.
Lemma lem1919878 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919879 (x : real) (y : real) : (term242 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1919877 x y) (@lem1919878)). Qed.
Lemma lem1919880 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919881 (x : real) (y : real) : (term244 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1919880) (@lem1919846 x y)). Qed.
Lemma lem1919882 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919883 (x : real) (y : real) : (term246 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1919881 x y) (@lem1919882)). Qed.
Lemma lem1919884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919885 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1919884) (@lem1919883 x y)). Qed.
Lemma lem1919886 (x : real) (y : real) : (term175 x y) = (term250 x y).
Proof. exact (MK_COMB (@lem1919885 x y) (@lem1919879 x y)). Qed.
Lemma lem1919887 (x : real) (y : real) : (term174 x y) = (term250 x y).
Proof. exact (TRANS (@lem1919730 x y) (@lem1919886 x y)). Qed.
Lemma lem1919888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1919889 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (MK_COMB (@lem1919888) (@lem1919729 x y)). Qed.
Lemma lem1919890 (x : real) (y : real) : (term253 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1919889 x y) (@lem1919887 x y)). Qed.
Lemma lem1919891 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (@lem1483554 (term168 x) (term168 y)). Qed.
Lemma lem1919916 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (@lem1483519 (term168 x) (term168 y)). Qed.
Lemma lem1919917 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1919918 (x : real) (y : real) : (term257 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem1919917) (@lem1919916 x y)). Qed.
Lemma lem1919919 (x : real) (y : real) : (term231 x y) = (term232 x y).
Proof. exact (@lem1483512 (term171 x y)). Qed.
Lemma lem1919920 (x : real) (y : real) : (term232 x y) = (term233 x y).
Proof. exact (@lem1483508 (term168 x) term10 (term205 y)). Qed.
Lemma lem1919921 (y : real) : (term234 y) = (term235 y).
Proof. exact (@lem1483476 term10 term10 (term168 y)). Qed.
Lemma lem1919923 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919924 : term181 = term182.
Proof. exact (@lem1919923 term13 term13). Qed.
Lemma lem1919925 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1919926 : term184 = term13.
Proof. exact (EQ_MP (@lem1919925) (@lem940073)). Qed.
Lemma lem1919927 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919928 : term182 = term100.
Proof. exact (MK_COMB (@lem1919927) (@lem1919926)). Qed.
Lemma lem1919929 : term181 = term100.
Proof. exact (TRANS (@lem1919924) (@lem1919928)). Qed.
Lemma lem1919930 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919931 : term185 = term186.
Proof. exact (MK_COMB (@lem1919930) (@lem1919929)). Qed.
Lemma lem1919932 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1919933 (y : real) : (term235 y) = (term236 y).
Proof. exact (MK_COMB (@lem1919931) (@lem1919932 y)). Qed.
Lemma lem1919934 (y : real) : (term234 y) = (term236 y).
Proof. exact (TRANS (@lem1919921 y) (@lem1919933 y)). Qed.
Lemma lem1919935 (y : real) : (term236 y) = (term168 y).
Proof. exact (@lem1483436 (term168 y)). Qed.
Lemma lem1919936 (y : real) : (term234 y) = (term168 y).
Proof. exact (TRANS (@lem1919934 y) (@lem1919935 y)). Qed.
Lemma lem1919939 (x : real) : (term237 x) = (term237 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1919940 (x : real) (y : real) : (term233 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1919939 x) (@lem1919936 y)). Qed.
Lemma lem1919941 (x : real) (y : real) : (term232 x y) = (term238 x y).
Proof. exact (TRANS (@lem1919920 x y) (@lem1919940 x y)). Qed.
Lemma lem1919942 (x : real) (y : real) : (term231 x y) = (term238 x y).
Proof. exact (TRANS (@lem1919919 x y) (@lem1919941 x y)). Qed.
Lemma lem1919943 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1919944 (x : real) (y : real) : ((term257 x y) = (term231 x y)) = ((term257 x y) = (term238 x y)).
Proof. exact (MK_COMB (@lem1919943 x y) (@lem1919942 x y)). Qed.
Lemma lem1919945 (x : real) (y : real) : (term257 x y) = (term238 x y).
Proof. exact (EQ_MP (@lem1919944 x y) (@lem1919918 x y)). Qed.
Lemma lem1919946 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919947 (x : real) (y : real) : (term259 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1919946) (@lem1919945 x y)). Qed.
Lemma lem1919948 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919949 (x : real) (y : real) : (term260 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1919947 x y) (@lem1919948)). Qed.
Lemma lem1919950 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1919951 (x : real) (y : real) : (term261 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1919950) (@lem1919916 x y)). Qed.
Lemma lem1919952 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919953 (x : real) (y : real) : (term262 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1919951 x y) (@lem1919952)). Qed.
Lemma lem1919954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1919955 (x : real) (y : real) : (term263 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1919954) (@lem1919953 x y)). Qed.
Lemma lem1919956 (x : real) (y : real) : (term256 x y) = (term250 x y).
Proof. exact (MK_COMB (@lem1919955 x y) (@lem1919949 x y)). Qed.
Lemma lem1919957 (x : real) (y : real) : (term255 x y) = (term250 x y).
Proof. exact (TRANS (@lem1919891 x y) (@lem1919956 x y)). Qed.
Lemma lem1919958 (x : real) (y : real) : ((term169 x y) = term2) = ((term225 x y) = term2).
Proof. exact (@lem1483529 (term169 x y) term2). Qed.
Lemma lem1919959 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1919966 (y : real) : (real_neg y) = (term4 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1919969 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1919970 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem1919969 x) (@lem1919966 y)). Qed.
Lemma lem1919971 (x : real) (y : real) : (term177 x y) = (term178 x y).
Proof. exact (@lem1483519 x (term4 y)). Qed.
Lemma lem1919972 (y : real) : (term179 y) = (term180 y).
Proof. exact (@lem1483476 term10 term10 y). Qed.
Lemma lem1919974 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1919975 : term181 = term182.
Proof. exact (@lem1919974 term13 term13). Qed.
Lemma lem1919976 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1919977 : term184 = term13.
Proof. exact (EQ_MP (@lem1919976) (@lem940073)). Qed.
Lemma lem1919978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1919979 : term182 = term100.
Proof. exact (MK_COMB (@lem1919978) (@lem1919977)). Qed.
Lemma lem1919980 : term181 = term100.
Proof. exact (TRANS (@lem1919975) (@lem1919979)). Qed.
Lemma lem1919981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1919982 : term185 = term186.
Proof. exact (MK_COMB (@lem1919981) (@lem1919980)). Qed.
Lemma lem1919983 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1919984 (y : real) : (term180 y) = (term187 y).
Proof. exact (MK_COMB (@lem1919982) (@lem1919983 y)). Qed.
Lemma lem1919985 (y : real) : (term179 y) = (term187 y).
Proof. exact (TRANS (@lem1919972 y) (@lem1919984 y)). Qed.
Lemma lem1919986 (y : real) : (term187 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1919987 (y : real) : (term179 y) = y.
Proof. exact (TRANS (@lem1919985 y) (@lem1919986 y)). Qed.
Lemma lem1919988 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1919991 (x : real) (y : real) : (term178 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1919988 x) (@lem1919987 y)). Qed.
Lemma lem1919992 (x : real) (y : real) : (term177 x y) = (real_add x y).
Proof. exact (TRANS (@lem1919971 x y) (@lem1919991 x y)). Qed.
Lemma lem1919993 (x : real) (y : real) : (term176 x y) = (real_add x y).
Proof. exact (TRANS (@lem1919970 x y) (@lem1919992 x y)). Qed.
Lemma lem1920006 (x : real) (y : real) : (real_sub x y) = (term188 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1920007 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920008 (x : real) (y : real) : (term189 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1920007) (@lem1920006 x y)). Qed.
Lemma lem1920009 (x : real) (y : real) : (term169 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem1920008 x y) (@lem1919993 x y)). Qed.
Lemma lem1920010 (x : real) (y : real) : (term191 x y) = (term192 x y).
Proof. exact (@lem1483454 x (term4 y) (real_add x y)). Qed.
Lemma lem1920011 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (@lem1483508 x x y). Qed.
Lemma lem1920012 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1920013 (x : real) : (real_mul x x) = (term168 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1920014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920015 (x : real) : (term195 x) = (term196 x).
Proof. exact (MK_COMB (@lem1920014) (@lem1920013 x)). Qed.
Lemma lem1920016 (x : real) (y : real) : (term194 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1920015 x) (@lem1920012 x y)). Qed.
Lemma lem1920017 (x : real) (y : real) : (term193 x y) = (term197 x y).
Proof. exact (TRANS (@lem1920011 x y) (@lem1920016 x y)). Qed.
Lemma lem1920018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920019 (x : real) (y : real) : (term198 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem1920018) (@lem1920017 x y)). Qed.
Lemma lem1920020 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (@lem1483508 x (term4 y) y). Qed.
Lemma lem1920021 (y : real) : (term202 y) = (term203 y).
Proof. exact (@lem1483472 term10 y y). Qed.
Lemma lem1920022 (y : real) : (real_mul y y) = (term168 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1920023 : term204 = term204.
Proof. exact (eq_refl term204). Qed.
Lemma lem1920024 (y : real) : (term203 y) = (term205 y).
Proof. exact (MK_COMB (@lem1920023) (@lem1920022 y)). Qed.
Lemma lem1920025 (y : real) : (term202 y) = (term205 y).
Proof. exact (TRANS (@lem1920021 y) (@lem1920024 y)). Qed.
Lemma lem1920026 (y : real) (x : real) : (term206 y x) = (term207 y x).
Proof. exact (@lem1483472 term10 y x). Qed.
Lemma lem1920027 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1920028 : term204 = term204.
Proof. exact (eq_refl term204). Qed.
Lemma lem1920029 (x : real) (y : real) : (term207 y x) = (term207 x y).
Proof. exact (MK_COMB (@lem1920028) (@lem1920027 x y)). Qed.
Lemma lem1920030 (x : real) (y : real) : (term206 y x) = (term207 x y).
Proof. exact (TRANS (@lem1920026 y x) (@lem1920029 x y)). Qed.
Lemma lem1920031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920032 (x : real) (y : real) : (term208 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem1920031) (@lem1920030 x y)). Qed.
Lemma lem1920033 (x : real) (y : real) : (term201 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1920032 x y) (@lem1920025 y)). Qed.
Lemma lem1920034 (x : real) (y : real) : (term200 x y) = (term210 x y).
Proof. exact (TRANS (@lem1920020 x y) (@lem1920033 x y)). Qed.
Lemma lem1920035 (x : real) (y : real) : (term192 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1920019 x y) (@lem1920034 x y)). Qed.
Lemma lem1920036 (x : real) (y : real) : (term191 x y) = (term211 x y).
Proof. exact (TRANS (@lem1920010 x y) (@lem1920035 x y)). Qed.
Lemma lem1920037 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1483482 (term168 x) (real_mul x y) (term210 x y)). Qed.
Lemma lem1920038 (x : real) (y : real) : (term213 x y) = (term214 x y).
Proof. exact (@lem1483490 (real_mul x y) (term207 x y) (term205 y)). Qed.
Lemma lem1920039 (x : real) (y : real) : (term215 x y) = (term216 x y).
Proof. exact (@lem1483442 term10 (real_mul x y)). Qed.
Lemma lem1920041 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920042 : term217 = term2.
Proof. exact (@lem1920041 term13). Qed.
Lemma lem1920043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920044 : term218 = term112.
Proof. exact (MK_COMB (@lem1920043) (@lem1920042)). Qed.
Lemma lem1920045 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1920046 (x : real) (y : real) : (term216 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1920044) (@lem1920045 x y)). Qed.
Lemma lem1920047 (x : real) (y : real) : (term215 x y) = (term219 x y).
Proof. exact (TRANS (@lem1920039 x y) (@lem1920046 x y)). Qed.
Lemma lem1920048 (x : real) (y : real) : (term219 x y) = term2.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1920049 (x : real) (y : real) : (term215 x y) = term2.
Proof. exact (TRANS (@lem1920047 x y) (@lem1920048 x y)). Qed.
Lemma lem1920050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920051 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1920050) (@lem1920049 x y)). Qed.
Lemma lem1920052 (y : real) : (term205 y) = (term205 y).
Proof. exact (eq_refl (term205 y)). Qed.
Lemma lem1920053 (x : real) (y : real) : (term214 x y) = (term222 y).
Proof. exact (MK_COMB (@lem1920051 x y) (@lem1920052 y)). Qed.
Lemma lem1920054 (x : real) (y : real) : (term213 x y) = (term222 y).
Proof. exact (TRANS (@lem1920038 x y) (@lem1920053 x y)). Qed.
Lemma lem1920055 (y : real) : (term222 y) = (term205 y).
Proof. exact (@lem1483448 (term205 y)). Qed.
Lemma lem1920056 (x : real) (y : real) : (term213 x y) = (term205 y).
Proof. exact (TRANS (@lem1920054 x y) (@lem1920055 y)). Qed.
Lemma lem1920057 (x : real) : (term196 x) = (term196 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem1920058 (x : real) (y : real) : (term212 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1920057 x) (@lem1920056 x y)). Qed.
Lemma lem1920059 (x : real) (y : real) : (term211 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920037 x y) (@lem1920058 x y)). Qed.
Lemma lem1920060 (x : real) (y : real) : (term191 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920036 x y) (@lem1920059 x y)). Qed.
Lemma lem1920061 (x : real) (y : real) : (term169 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920009 x y) (@lem1920060 x y)). Qed.
Lemma lem1920062 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1920063 (x : real) (y : real) : (term223 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1920062) (@lem1920061 x y)). Qed.
Lemma lem1920064 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem1920063 x y) (@lem1919959)). Qed.
Lemma lem1920065 (x : real) (y : real) : (term226 x y) = (term227 x y).
Proof. exact (@lem1483519 (term171 x y) term2). Qed.
Lemma lem1920067 (x : nat) : (term30 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1920068 : term31 = term2.
Proof. exact (@lem1920067 term13). Qed.
Lemma lem1920069 (x : real) (y : real) : (term228 x y) = (term228 x y).
Proof. exact (eq_refl (term228 x y)). Qed.
Lemma lem1920070 (x : real) (y : real) : (term227 x y) = (term229 x y).
Proof. exact (MK_COMB (@lem1920069 x y) (@lem1920068)). Qed.
Lemma lem1920071 (x : real) (y : real) : (term229 x y) = (term171 x y).
Proof. exact (@lem1483450 (term171 x y)). Qed.
Lemma lem1920072 (x : real) (y : real) : (term227 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920070 x y) (@lem1920071 x y)). Qed.
Lemma lem1920073 (x : real) (y : real) : (term226 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920065 x y) (@lem1920072 x y)). Qed.
Lemma lem1920074 (x : real) (y : real) : (term225 x y) = (term171 x y).
Proof. exact (TRANS (@lem1920064 x y) (@lem1920073 x y)). Qed.
Lemma lem1920075 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920076 (x : real) (y : real) : (term264 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1920075) (@lem1920074 x y)). Qed.
Lemma lem1920077 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920078 (x : real) (y : real) : ((term225 x y) = term2) = ((term171 x y) = term2).
Proof. exact (MK_COMB (@lem1920076 x y) (@lem1920077)). Qed.
Lemma lem1920079 (x : real) (y : real) : ((term169 x y) = term2) = ((term171 x y) = term2).
Proof. exact (TRANS (@lem1919958 x y) (@lem1920078 x y)). Qed.
Lemma lem1920080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1920081 (x : real) (y : real) : (term265 x y) = (term266 x y).
Proof. exact (MK_COMB (@lem1920080) (@lem1919957 x y)). Qed.
Lemma lem1920082 (x : real) (y : real) : (term267 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1920081 x y) (@lem1920079 x y)). Qed.
Lemma lem1920083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1920084 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (MK_COMB (@lem1920083) (@lem1919890 x y)). Qed.
Lemma lem1920085 (x : real) (y : real) : (term167 x y) = (term271 x y).
Proof. exact (MK_COMB (@lem1920084 x y) (@lem1920082 x y)). Qed.
Lemma lem1920092 (x : real) (y : real) : (term166 x y) = (term271 x y).
Proof. exact (TRANS (@lem1919698 x y) (@lem1920085 x y)). Qed.
Lemma lem1920109 (x : real) (y : real) : (term268 x y) = (term272 x y).
Proof. exact (@lem19367 (term247 x y) (term243 x y) ((term171 x y) = term2)). Qed.
Lemma lem1920126 (x : real) (y : real) : (term254 x y) = (term273 x y).
Proof. exact (@lem19158 (term247 x y) ((term171 x y) = term2) (term243 x y)). Qed.
Lemma lem1920127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1920128 (x : real) (y : real) : (term270 x y) = (term274 x y).
Proof. exact (MK_COMB (@lem1920127) (@lem1920126 x y)). Qed.
Lemma lem1920129 (x : real) (y : real) : (term271 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem1920128 x y) (@lem1920109 x y)). Qed.
Lemma lem1920130 (x : real) (y : real) : (term166 x y) = (term275 x y).
Proof. exact (TRANS (@lem1920092 x y) (@lem1920129 x y)). Qed.
Lemma lem1920152 (x : real) (y : real) (h1 : term275 x y) : term275 x y.
Proof. exact (h1). Qed.
Lemma lem1920153 (x : real) (y : real) (h1 : term273 x y) : term273 x y.
Proof. exact (h1). Qed.
Lemma lem1920154 (x : real) (y : real) (h1 : term276 x y) : term276 x y.
Proof. exact (h1). Qed.
Lemma lem1920155 (x : real) (y : real) (h1 : term276 x y) : term247 x y.
Proof. exact (proj2 (@lem1920154 x y h1)). Qed.
Lemma lem1920156 (x : real) (y : real) (h1 : term276 x y) : (term171 x y) = term2.
Proof. exact (proj1 (@lem1920154 x y h1)). Qed.
Lemma lem1920158 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920159 : term146 = term147.
Proof. exact (@lem1920158 (NUMERAL 0) term13). Qed.
Lemma lem1920160 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1920161 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1920162 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1920161 h1) (fun h1 : term147 = True => @lem1920160)). Qed.
Lemma lem1920163 : term147 = True.
Proof. exact (EQ_MP (@lem1920162) (@lem1920160)). Qed.
Lemma lem1920164 : term146 = True.
Proof. exact (TRANS (@lem1920159) (@lem1920163)). Qed.
Lemma lem1920165 : True = term146.
Proof. exact (SYM (@lem1920164)). Qed.
Lemma lem1920166 : term146.
Proof. exact (EQ_MP (@lem1920165) (@lem0)). Qed.
Lemma lem1920167 (x : real) (y : real) (h1 : term276 x y) : term277 x y.
Proof. exact (conj (@lem1920166) (@lem1920155 x y h1)). Qed.
Lemma lem1920169 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1920170 (x : real) (y : real) : term278 x y.
Proof. exact (@lem1920169 term100 (term171 x y)). Qed.
Lemma lem1920171 (x : real) (y : real) (h1 : term276 x y) : term279 x y.
Proof. exact (@lem1920170 x y (@lem1920167 x y h1)). Qed.
Lemma lem1920172 (x : real) (y : real) : (term280 x y) = (term171 x y).
Proof. exact (@lem1483460 (term171 x y)). Qed.
Lemma lem1920173 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920174 (x : real) (y : real) : (term281 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1920173) (@lem1920172 x y)). Qed.
Lemma lem1920175 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920176 (x : real) (y : real) : (term279 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1920174 x y) (@lem1920175)). Qed.
Lemma lem1920177 (x : real) (y : real) (h1 : term276 x y) : term247 x y.
Proof. exact (EQ_MP (@lem1920176 x y) (@lem1920171 x y h1)). Qed.
Lemma lem1920179 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1920180 (x : real) (y : real) : term282 x y.
Proof. exact (@lem1920179 (term171 x y)). Qed.
Lemma lem1920181 (x : real) (y : real) (h1 : term276 x y) : term283 x y.
Proof. exact (@lem1920180 x y (@lem1920156 x y h1)). Qed.
Lemma lem1920182 (x : real) (y : real) (h1 : term276 x y) : term284 x y.
Proof. exact (@lem1920181 x y h1 term10). Qed.
Lemma lem1920183 (x : real) (y : real) : (term284 x y) = ((term232 x y) = term2).
Proof. exact (eq_refl (term284 x y)). Qed.
Lemma lem1920184 (x : real) (y : real) (h1 : term276 x y) : (term232 x y) = term2.
Proof. exact (EQ_MP (@lem1920183 x y) (@lem1920182 x y h1)). Qed.
Lemma lem1920185 (x : real) (y : real) : (term232 x y) = (term233 x y).
Proof. exact (@lem1483508 (term168 x) term10 (term205 y)). Qed.
Lemma lem1920186 (y : real) : (term234 y) = (term235 y).
Proof. exact (@lem1483476 term10 term10 (term168 y)). Qed.
Lemma lem1920188 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1920189 : term181 = term182.
Proof. exact (@lem1920188 term13 term13). Qed.
Lemma lem1920190 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1920191 : term184 = term13.
Proof. exact (EQ_MP (@lem1920190) (@lem940073)). Qed.
Lemma lem1920192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1920193 : term182 = term100.
Proof. exact (MK_COMB (@lem1920192) (@lem1920191)). Qed.
Lemma lem1920194 : term181 = term100.
Proof. exact (TRANS (@lem1920189) (@lem1920193)). Qed.
Lemma lem1920195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920196 : term185 = term186.
Proof. exact (MK_COMB (@lem1920195) (@lem1920194)). Qed.
Lemma lem1920197 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920198 (y : real) : (term235 y) = (term236 y).
Proof. exact (MK_COMB (@lem1920196) (@lem1920197 y)). Qed.
Lemma lem1920199 (y : real) : (term234 y) = (term236 y).
Proof. exact (TRANS (@lem1920186 y) (@lem1920198 y)). Qed.
Lemma lem1920200 (y : real) : (term236 y) = (term168 y).
Proof. exact (@lem1483436 (term168 y)). Qed.
Lemma lem1920201 (y : real) : (term234 y) = (term168 y).
Proof. exact (TRANS (@lem1920199 y) (@lem1920200 y)). Qed.
Lemma lem1920204 (x : real) : (term237 x) = (term237 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1920205 (x : real) (y : real) : (term233 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1920204 x) (@lem1920201 y)). Qed.
Lemma lem1920206 (x : real) (y : real) : (term232 x y) = (term238 x y).
Proof. exact (TRANS (@lem1920185 x y) (@lem1920205 x y)). Qed.
Lemma lem1920207 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920208 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1920207) (@lem1920206 x y)). Qed.
Lemma lem1920209 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920210 (x : real) (y : real) : ((term232 x y) = term2) = ((term238 x y) = term2).
Proof. exact (MK_COMB (@lem1920208 x y) (@lem1920209)). Qed.
Lemma lem1920211 (x : real) (y : real) (h1 : term276 x y) : (term238 x y) = term2.
Proof. exact (EQ_MP (@lem1920210 x y) (@lem1920184 x y h1)). Qed.
Lemma lem1920212 (x : real) (y : real) (h1 : term276 x y) : term287 x y.
Proof. exact (conj (@lem1920211 x y h1) (@lem1920177 x y h1)). Qed.
Lemma lem1920214 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1920215 (x : real) (y : real) : term288 x y.
Proof. exact (@lem1920214 (term238 x y) (term171 x y)). Qed.
Lemma lem1920216 (x : real) (y : real) (h1 : term276 x y) : term289 x y.
Proof. exact (@lem1920215 x y (@lem1920212 x y h1)). Qed.
Lemma lem1920217 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (@lem1483480 (term205 x) (term168 x) (term168 y) (term205 y)). Qed.
Lemma lem1920218 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1483440 term10 (term168 x)). Qed.
Lemma lem1920220 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920221 : term217 = term2.
Proof. exact (@lem1920220 term13). Qed.
Lemma lem1920222 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920223 : term218 = term112.
Proof. exact (MK_COMB (@lem1920222) (@lem1920221)). Qed.
Lemma lem1920224 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1920225 (x : real) : (term293 x) = (term294 x).
Proof. exact (MK_COMB (@lem1920223) (@lem1920224 x)). Qed.
Lemma lem1920226 (x : real) : (term292 x) = (term294 x).
Proof. exact (TRANS (@lem1920218 x) (@lem1920225 x)). Qed.
Lemma lem1920227 (x : real) : (term294 x) = term2.
Proof. exact (@lem1483446 (term168 x)). Qed.
Lemma lem1920228 (x : real) : (term292 x) = term2.
Proof. exact (TRANS (@lem1920226 x) (@lem1920227 x)). Qed.
Lemma lem1920229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920230 (x : real) : (term295 x) = term221.
Proof. exact (MK_COMB (@lem1920229) (@lem1920228 x)). Qed.
Lemma lem1920231 (y : real) : (term296 y) = (term293 y).
Proof. exact (@lem1483442 term10 (term168 y)). Qed.
Lemma lem1920233 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920234 : term217 = term2.
Proof. exact (@lem1920233 term13). Qed.
Lemma lem1920235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920236 : term218 = term112.
Proof. exact (MK_COMB (@lem1920235) (@lem1920234)). Qed.
Lemma lem1920237 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920238 (y : real) : (term293 y) = (term294 y).
Proof. exact (MK_COMB (@lem1920236) (@lem1920237 y)). Qed.
Lemma lem1920239 (y : real) : (term296 y) = (term294 y).
Proof. exact (TRANS (@lem1920231 y) (@lem1920238 y)). Qed.
Lemma lem1920240 (y : real) : (term294 y) = term2.
Proof. exact (@lem1483446 (term168 y)). Qed.
Lemma lem1920241 (y : real) : (term296 y) = term2.
Proof. exact (TRANS (@lem1920239 y) (@lem1920240 y)). Qed.
Lemma lem1920242 (x : real) (y : real) : (term291 x y) = term297.
Proof. exact (MK_COMB (@lem1920230 x) (@lem1920241 y)). Qed.
Lemma lem1920243 (x : real) (y : real) : (term290 x y) = term297.
Proof. exact (TRANS (@lem1920217 x y) (@lem1920242 x y)). Qed.
Lemma lem1920244 : term297 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1920245 (x : real) (y : real) : (term290 x y) = term2.
Proof. exact (TRANS (@lem1920243 x y) (@lem1920244)). Qed.
Lemma lem1920246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920247 (x : real) (y : real) : (term298 x y) = term115.
Proof. exact (MK_COMB (@lem1920246) (@lem1920245 x y)). Qed.
Lemma lem1920248 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920249 (x : real) (y : real) : (term289 x y) = term116.
Proof. exact (MK_COMB (@lem1920247 x y) (@lem1920248)). Qed.
Lemma lem1920250 (x : real) (y : real) (h1 : term276 x y) : term116.
Proof. exact (EQ_MP (@lem1920249 x y) (@lem1920216 x y h1)). Qed.
Lemma lem1920252 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920253 : term116 = term117.
Proof. exact (@lem1920252 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1920254 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1920255 : term116 = False.
Proof. exact (TRANS (@lem1920253) (@lem1920254)). Qed.
Lemma lem1920256 (x : real) (y : real) (h1 : term276 x y) : False.
Proof. exact (EQ_MP (@lem1920255) (@lem1920250 x y h1)). Qed.
Lemma lem1920257 (x : real) (y : real) (h1 : term299 x y) : term299 x y.
Proof. exact (h1). Qed.
Lemma lem1920258 (x : real) (y : real) (h1 : term299 x y) : term243 x y.
Proof. exact (proj2 (@lem1920257 x y h1)). Qed.
Lemma lem1920259 (x : real) (y : real) (h1 : term299 x y) : (term171 x y) = term2.
Proof. exact (proj1 (@lem1920257 x y h1)). Qed.
Lemma lem1920261 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920262 : term146 = term147.
Proof. exact (@lem1920261 (NUMERAL 0) term13). Qed.
Lemma lem1920263 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1920264 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1920265 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1920264 h1) (fun h1 : term147 = True => @lem1920263)). Qed.
Lemma lem1920266 : term147 = True.
Proof. exact (EQ_MP (@lem1920265) (@lem1920263)). Qed.
Lemma lem1920267 : term146 = True.
Proof. exact (TRANS (@lem1920262) (@lem1920266)). Qed.
Lemma lem1920268 : True = term146.
Proof. exact (SYM (@lem1920267)). Qed.
Lemma lem1920269 : term146.
Proof. exact (EQ_MP (@lem1920268) (@lem0)). Qed.
Lemma lem1920270 (x : real) (y : real) (h1 : term299 x y) : term300 x y.
Proof. exact (conj (@lem1920269) (@lem1920258 x y h1)). Qed.
Lemma lem1920272 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1920273 (x : real) (y : real) : term301 x y.
Proof. exact (@lem1920272 term100 (term238 x y)). Qed.
Lemma lem1920274 (x : real) (y : real) (h1 : term299 x y) : term302 x y.
Proof. exact (@lem1920273 x y (@lem1920270 x y h1)). Qed.
Lemma lem1920275 (x : real) (y : real) : (term303 x y) = (term238 x y).
Proof. exact (@lem1483460 (term238 x y)). Qed.
Lemma lem1920276 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920277 (x : real) (y : real) : (term304 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1920276) (@lem1920275 x y)). Qed.
Lemma lem1920278 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920279 (x : real) (y : real) : (term302 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1920277 x y) (@lem1920278)). Qed.
Lemma lem1920280 (x : real) (y : real) (h1 : term299 x y) : term243 x y.
Proof. exact (EQ_MP (@lem1920279 x y) (@lem1920274 x y h1)). Qed.
Lemma lem1920282 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1920283 (x : real) (y : real) : term282 x y.
Proof. exact (@lem1920282 (term171 x y)). Qed.
Lemma lem1920284 (x : real) (y : real) (h1 : term299 x y) : term283 x y.
Proof. exact (@lem1920283 x y (@lem1920259 x y h1)). Qed.
Lemma lem1920285 (x : real) (y : real) (h1 : term299 x y) : term305 x y.
Proof. exact (@lem1920284 x y h1 term100). Qed.
Lemma lem1920286 (x : real) (y : real) : (term305 x y) = ((term280 x y) = term2).
Proof. exact (eq_refl (term305 x y)). Qed.
Lemma lem1920287 (x : real) (y : real) (h1 : term299 x y) : (term280 x y) = term2.
Proof. exact (EQ_MP (@lem1920286 x y) (@lem1920285 x y h1)). Qed.
Lemma lem1920288 (x : real) (y : real) : (term280 x y) = (term171 x y).
Proof. exact (@lem1483460 (term171 x y)). Qed.
Lemma lem1920289 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920290 (x : real) (y : real) : (term306 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1920289) (@lem1920288 x y)). Qed.
Lemma lem1920291 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920292 (x : real) (y : real) : ((term280 x y) = term2) = ((term171 x y) = term2).
Proof. exact (MK_COMB (@lem1920290 x y) (@lem1920291)). Qed.
Lemma lem1920293 (x : real) (y : real) (h1 : term299 x y) : (term171 x y) = term2.
Proof. exact (EQ_MP (@lem1920292 x y) (@lem1920287 x y h1)). Qed.
Lemma lem1920294 (x : real) (y : real) (h1 : term299 x y) : term299 x y.
Proof. exact (conj (@lem1920293 x y h1) (@lem1920280 x y h1)). Qed.
Lemma lem1920296 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1920297 (x : real) (y : real) : term307 x y.
Proof. exact (@lem1920296 (term171 x y) (term238 x y)). Qed.
Lemma lem1920298 (x : real) (y : real) (h1 : term299 x y) : term308 x y.
Proof. exact (@lem1920297 x y (@lem1920294 x y h1)). Qed.
Lemma lem1920299 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (@lem1483480 (term168 x) (term205 x) (term205 y) (term168 y)). Qed.
Lemma lem1920300 (x : real) : (term296 x) = (term293 x).
Proof. exact (@lem1483442 term10 (term168 x)). Qed.
Lemma lem1920302 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920303 : term217 = term2.
Proof. exact (@lem1920302 term13). Qed.
Lemma lem1920304 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920305 : term218 = term112.
Proof. exact (MK_COMB (@lem1920304) (@lem1920303)). Qed.
Lemma lem1920306 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1920307 (x : real) : (term293 x) = (term294 x).
Proof. exact (MK_COMB (@lem1920305) (@lem1920306 x)). Qed.
Lemma lem1920308 (x : real) : (term296 x) = (term294 x).
Proof. exact (TRANS (@lem1920300 x) (@lem1920307 x)). Qed.
Lemma lem1920309 (x : real) : (term294 x) = term2.
Proof. exact (@lem1483446 (term168 x)). Qed.
Lemma lem1920310 (x : real) : (term296 x) = term2.
Proof. exact (TRANS (@lem1920308 x) (@lem1920309 x)). Qed.
Lemma lem1920311 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920312 (x : real) : (term311 x) = term221.
Proof. exact (MK_COMB (@lem1920311) (@lem1920310 x)). Qed.
Lemma lem1920313 (y : real) : (term292 y) = (term293 y).
Proof. exact (@lem1483440 term10 (term168 y)). Qed.
Lemma lem1920315 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920316 : term217 = term2.
Proof. exact (@lem1920315 term13). Qed.
Lemma lem1920317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920318 : term218 = term112.
Proof. exact (MK_COMB (@lem1920317) (@lem1920316)). Qed.
Lemma lem1920319 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920320 (y : real) : (term293 y) = (term294 y).
Proof. exact (MK_COMB (@lem1920318) (@lem1920319 y)). Qed.
Lemma lem1920321 (y : real) : (term292 y) = (term294 y).
Proof. exact (TRANS (@lem1920313 y) (@lem1920320 y)). Qed.
Lemma lem1920322 (y : real) : (term294 y) = term2.
Proof. exact (@lem1483446 (term168 y)). Qed.
Lemma lem1920323 (y : real) : (term292 y) = term2.
Proof. exact (TRANS (@lem1920321 y) (@lem1920322 y)). Qed.
Lemma lem1920324 (x : real) (y : real) : (term310 x y) = term297.
Proof. exact (MK_COMB (@lem1920312 x) (@lem1920323 y)). Qed.
Lemma lem1920325 (x : real) (y : real) : (term309 x y) = term297.
Proof. exact (TRANS (@lem1920299 x y) (@lem1920324 x y)). Qed.
Lemma lem1920326 : term297 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1920327 (x : real) (y : real) : (term309 x y) = term2.
Proof. exact (TRANS (@lem1920325 x y) (@lem1920326)). Qed.
Lemma lem1920328 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920329 (x : real) (y : real) : (term312 x y) = term115.
Proof. exact (MK_COMB (@lem1920328) (@lem1920327 x y)). Qed.
Lemma lem1920330 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920331 (x : real) (y : real) : (term308 x y) = term116.
Proof. exact (MK_COMB (@lem1920329 x y) (@lem1920330)). Qed.
Lemma lem1920332 (x : real) (y : real) (h1 : term299 x y) : term116.
Proof. exact (EQ_MP (@lem1920331 x y) (@lem1920298 x y h1)). Qed.
Lemma lem1920334 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920335 : term116 = term117.
Proof. exact (@lem1920334 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1920336 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1920337 : term116 = False.
Proof. exact (TRANS (@lem1920335) (@lem1920336)). Qed.
Lemma lem1920338 (x : real) (y : real) (h1 : term299 x y) : False.
Proof. exact (EQ_MP (@lem1920337) (@lem1920332 x y h1)). Qed.
Lemma lem1920339 (x : real) (y : real) (h1 : term273 x y) : False.
Proof. exact (or_elim (@lem1920153 x y h1) (fun h0 : term276 x y => @lem1920256 x y h0) (fun h0 : term299 x y => @lem1920338 x y h0)). Qed.
Lemma lem1920340 (x : real) (y : real) (h1 : term272 x y) : term272 x y.
Proof. exact (h1). Qed.
Lemma lem1920341 (x : real) (y : real) (h1 : term313 x y) : term313 x y.
Proof. exact (h1). Qed.
Lemma lem1920342 (x : real) (y : real) (h1 : term313 x y) : (term171 x y) = term2.
Proof. exact (proj2 (@lem1920341 x y h1)). Qed.
Lemma lem1920343 (x : real) (y : real) (h1 : term313 x y) : term247 x y.
Proof. exact (proj1 (@lem1920341 x y h1)). Qed.
Lemma lem1920345 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920346 : term146 = term147.
Proof. exact (@lem1920345 (NUMERAL 0) term13). Qed.
Lemma lem1920347 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1920348 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1920349 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1920348 h1) (fun h1 : term147 = True => @lem1920347)). Qed.
Lemma lem1920350 : term147 = True.
Proof. exact (EQ_MP (@lem1920349) (@lem1920347)). Qed.
Lemma lem1920351 : term146 = True.
Proof. exact (TRANS (@lem1920346) (@lem1920350)). Qed.
Lemma lem1920352 : True = term146.
Proof. exact (SYM (@lem1920351)). Qed.
Lemma lem1920353 : term146.
Proof. exact (EQ_MP (@lem1920352) (@lem0)). Qed.
Lemma lem1920354 (x : real) (y : real) (h1 : term313 x y) : term277 x y.
Proof. exact (conj (@lem1920353) (@lem1920343 x y h1)). Qed.
Lemma lem1920356 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1920357 (x : real) (y : real) : term278 x y.
Proof. exact (@lem1920356 term100 (term171 x y)). Qed.
Lemma lem1920358 (x : real) (y : real) (h1 : term313 x y) : term279 x y.
Proof. exact (@lem1920357 x y (@lem1920354 x y h1)). Qed.
Lemma lem1920359 (x : real) (y : real) : (term280 x y) = (term171 x y).
Proof. exact (@lem1483460 (term171 x y)). Qed.
Lemma lem1920360 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920361 (x : real) (y : real) : (term281 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1920360) (@lem1920359 x y)). Qed.
Lemma lem1920362 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920363 (x : real) (y : real) : (term279 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1920361 x y) (@lem1920362)). Qed.
Lemma lem1920364 (x : real) (y : real) (h1 : term313 x y) : term247 x y.
Proof. exact (EQ_MP (@lem1920363 x y) (@lem1920358 x y h1)). Qed.
Lemma lem1920366 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1920367 (x : real) (y : real) : term282 x y.
Proof. exact (@lem1920366 (term171 x y)). Qed.
Lemma lem1920368 (x : real) (y : real) (h1 : term313 x y) : term283 x y.
Proof. exact (@lem1920367 x y (@lem1920342 x y h1)). Qed.
Lemma lem1920369 (x : real) (y : real) (h1 : term313 x y) : term284 x y.
Proof. exact (@lem1920368 x y h1 term10). Qed.
Lemma lem1920370 (x : real) (y : real) : (term284 x y) = ((term232 x y) = term2).
Proof. exact (eq_refl (term284 x y)). Qed.
Lemma lem1920371 (x : real) (y : real) (h1 : term313 x y) : (term232 x y) = term2.
Proof. exact (EQ_MP (@lem1920370 x y) (@lem1920369 x y h1)). Qed.
Lemma lem1920372 (x : real) (y : real) : (term232 x y) = (term233 x y).
Proof. exact (@lem1483508 (term168 x) term10 (term205 y)). Qed.
Lemma lem1920373 (y : real) : (term234 y) = (term235 y).
Proof. exact (@lem1483476 term10 term10 (term168 y)). Qed.
Lemma lem1920375 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1920376 : term181 = term182.
Proof. exact (@lem1920375 term13 term13). Qed.
Lemma lem1920377 : (term183 = (BIT1 0)) = (term184 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1920378 : term184 = term13.
Proof. exact (EQ_MP (@lem1920377) (@lem940073)). Qed.
Lemma lem1920379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1920380 : term182 = term100.
Proof. exact (MK_COMB (@lem1920379) (@lem1920378)). Qed.
Lemma lem1920381 : term181 = term100.
Proof. exact (TRANS (@lem1920376) (@lem1920380)). Qed.
Lemma lem1920382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920383 : term185 = term186.
Proof. exact (MK_COMB (@lem1920382) (@lem1920381)). Qed.
Lemma lem1920384 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920385 (y : real) : (term235 y) = (term236 y).
Proof. exact (MK_COMB (@lem1920383) (@lem1920384 y)). Qed.
Lemma lem1920386 (y : real) : (term234 y) = (term236 y).
Proof. exact (TRANS (@lem1920373 y) (@lem1920385 y)). Qed.
Lemma lem1920387 (y : real) : (term236 y) = (term168 y).
Proof. exact (@lem1483436 (term168 y)). Qed.
Lemma lem1920388 (y : real) : (term234 y) = (term168 y).
Proof. exact (TRANS (@lem1920386 y) (@lem1920387 y)). Qed.
Lemma lem1920391 (x : real) : (term237 x) = (term237 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1920392 (x : real) (y : real) : (term233 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1920391 x) (@lem1920388 y)). Qed.
Lemma lem1920393 (x : real) (y : real) : (term232 x y) = (term238 x y).
Proof. exact (TRANS (@lem1920372 x y) (@lem1920392 x y)). Qed.
Lemma lem1920394 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920395 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1920394) (@lem1920393 x y)). Qed.
Lemma lem1920396 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920397 (x : real) (y : real) : ((term232 x y) = term2) = ((term238 x y) = term2).
Proof. exact (MK_COMB (@lem1920395 x y) (@lem1920396)). Qed.
Lemma lem1920398 (x : real) (y : real) (h1 : term313 x y) : (term238 x y) = term2.
Proof. exact (EQ_MP (@lem1920397 x y) (@lem1920371 x y h1)). Qed.
Lemma lem1920399 (x : real) (y : real) (h1 : term313 x y) : term287 x y.
Proof. exact (conj (@lem1920398 x y h1) (@lem1920364 x y h1)). Qed.
Lemma lem1920401 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1920402 (x : real) (y : real) : term288 x y.
Proof. exact (@lem1920401 (term238 x y) (term171 x y)). Qed.
Lemma lem1920403 (x : real) (y : real) (h1 : term313 x y) : term289 x y.
Proof. exact (@lem1920402 x y (@lem1920399 x y h1)). Qed.
Lemma lem1920404 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (@lem1483480 (term205 x) (term168 x) (term168 y) (term205 y)). Qed.
Lemma lem1920405 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1483440 term10 (term168 x)). Qed.
Lemma lem1920407 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920408 : term217 = term2.
Proof. exact (@lem1920407 term13). Qed.
Lemma lem1920409 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920410 : term218 = term112.
Proof. exact (MK_COMB (@lem1920409) (@lem1920408)). Qed.
Lemma lem1920411 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1920412 (x : real) : (term293 x) = (term294 x).
Proof. exact (MK_COMB (@lem1920410) (@lem1920411 x)). Qed.
Lemma lem1920413 (x : real) : (term292 x) = (term294 x).
Proof. exact (TRANS (@lem1920405 x) (@lem1920412 x)). Qed.
Lemma lem1920414 (x : real) : (term294 x) = term2.
Proof. exact (@lem1483446 (term168 x)). Qed.
Lemma lem1920415 (x : real) : (term292 x) = term2.
Proof. exact (TRANS (@lem1920413 x) (@lem1920414 x)). Qed.
Lemma lem1920416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920417 (x : real) : (term295 x) = term221.
Proof. exact (MK_COMB (@lem1920416) (@lem1920415 x)). Qed.
Lemma lem1920418 (y : real) : (term296 y) = (term293 y).
Proof. exact (@lem1483442 term10 (term168 y)). Qed.
Lemma lem1920420 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920421 : term217 = term2.
Proof. exact (@lem1920420 term13). Qed.
Lemma lem1920422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920423 : term218 = term112.
Proof. exact (MK_COMB (@lem1920422) (@lem1920421)). Qed.
Lemma lem1920424 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920425 (y : real) : (term293 y) = (term294 y).
Proof. exact (MK_COMB (@lem1920423) (@lem1920424 y)). Qed.
Lemma lem1920426 (y : real) : (term296 y) = (term294 y).
Proof. exact (TRANS (@lem1920418 y) (@lem1920425 y)). Qed.
Lemma lem1920427 (y : real) : (term294 y) = term2.
Proof. exact (@lem1483446 (term168 y)). Qed.
Lemma lem1920428 (y : real) : (term296 y) = term2.
Proof. exact (TRANS (@lem1920426 y) (@lem1920427 y)). Qed.
Lemma lem1920429 (x : real) (y : real) : (term291 x y) = term297.
Proof. exact (MK_COMB (@lem1920417 x) (@lem1920428 y)). Qed.
Lemma lem1920430 (x : real) (y : real) : (term290 x y) = term297.
Proof. exact (TRANS (@lem1920404 x y) (@lem1920429 x y)). Qed.
Lemma lem1920431 : term297 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1920432 (x : real) (y : real) : (term290 x y) = term2.
Proof. exact (TRANS (@lem1920430 x y) (@lem1920431)). Qed.
Lemma lem1920433 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920434 (x : real) (y : real) : (term298 x y) = term115.
Proof. exact (MK_COMB (@lem1920433) (@lem1920432 x y)). Qed.
Lemma lem1920435 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920436 (x : real) (y : real) : (term289 x y) = term116.
Proof. exact (MK_COMB (@lem1920434 x y) (@lem1920435)). Qed.
Lemma lem1920437 (x : real) (y : real) (h1 : term313 x y) : term116.
Proof. exact (EQ_MP (@lem1920436 x y) (@lem1920403 x y h1)). Qed.
Lemma lem1920439 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920440 : term116 = term117.
Proof. exact (@lem1920439 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1920441 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1920442 : term116 = False.
Proof. exact (TRANS (@lem1920440) (@lem1920441)). Qed.
Lemma lem1920443 (x : real) (y : real) (h1 : term313 x y) : False.
Proof. exact (EQ_MP (@lem1920442) (@lem1920437 x y h1)). Qed.
Lemma lem1920444 (x : real) (y : real) (h1 : term314 x y) : term314 x y.
Proof. exact (h1). Qed.
Lemma lem1920445 (x : real) (y : real) (h1 : term314 x y) : (term171 x y) = term2.
Proof. exact (proj2 (@lem1920444 x y h1)). Qed.
Lemma lem1920446 (x : real) (y : real) (h1 : term314 x y) : term243 x y.
Proof. exact (proj1 (@lem1920444 x y h1)). Qed.
Lemma lem1920448 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920449 : term146 = term147.
Proof. exact (@lem1920448 (NUMERAL 0) term13). Qed.
Lemma lem1920450 : term148 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1920451 (h1 : term148 = (BIT1 0)) : term147 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1920452 : (term148 = (BIT1 0)) = (term147 = True).
Proof. exact (prop_ext (fun h1 : term148 = (BIT1 0) => @lem1920451 h1) (fun h1 : term147 = True => @lem1920450)). Qed.
Lemma lem1920453 : term147 = True.
Proof. exact (EQ_MP (@lem1920452) (@lem1920450)). Qed.
Lemma lem1920454 : term146 = True.
Proof. exact (TRANS (@lem1920449) (@lem1920453)). Qed.
Lemma lem1920455 : True = term146.
Proof. exact (SYM (@lem1920454)). Qed.
Lemma lem1920456 : term146.
Proof. exact (EQ_MP (@lem1920455) (@lem0)). Qed.
Lemma lem1920457 (x : real) (y : real) (h1 : term314 x y) : term300 x y.
Proof. exact (conj (@lem1920456) (@lem1920446 x y h1)). Qed.
Lemma lem1920459 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1920460 (x : real) (y : real) : term301 x y.
Proof. exact (@lem1920459 term100 (term238 x y)). Qed.
Lemma lem1920461 (x : real) (y : real) (h1 : term314 x y) : term302 x y.
Proof. exact (@lem1920460 x y (@lem1920457 x y h1)). Qed.
Lemma lem1920462 (x : real) (y : real) : (term303 x y) = (term238 x y).
Proof. exact (@lem1483460 (term238 x y)). Qed.
Lemma lem1920463 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920464 (x : real) (y : real) : (term304 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1920463) (@lem1920462 x y)). Qed.
Lemma lem1920465 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920466 (x : real) (y : real) : (term302 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1920464 x y) (@lem1920465)). Qed.
Lemma lem1920467 (x : real) (y : real) (h1 : term314 x y) : term243 x y.
Proof. exact (EQ_MP (@lem1920466 x y) (@lem1920461 x y h1)). Qed.
Lemma lem1920469 (y : real) : term96 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1920470 (x : real) (y : real) : term282 x y.
Proof. exact (@lem1920469 (term171 x y)). Qed.
Lemma lem1920471 (x : real) (y : real) (h1 : term314 x y) : term283 x y.
Proof. exact (@lem1920470 x y (@lem1920445 x y h1)). Qed.
Lemma lem1920472 (x : real) (y : real) (h1 : term314 x y) : term305 x y.
Proof. exact (@lem1920471 x y h1 term100). Qed.
Lemma lem1920473 (x : real) (y : real) : (term305 x y) = ((term280 x y) = term2).
Proof. exact (eq_refl (term305 x y)). Qed.
Lemma lem1920474 (x : real) (y : real) (h1 : term314 x y) : (term280 x y) = term2.
Proof. exact (EQ_MP (@lem1920473 x y) (@lem1920472 x y h1)). Qed.
Lemma lem1920475 (x : real) (y : real) : (term280 x y) = (term171 x y).
Proof. exact (@lem1483460 (term171 x y)). Qed.
Lemma lem1920476 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920477 (x : real) (y : real) : (term306 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1920476) (@lem1920475 x y)). Qed.
Lemma lem1920478 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920479 (x : real) (y : real) : ((term280 x y) = term2) = ((term171 x y) = term2).
Proof. exact (MK_COMB (@lem1920477 x y) (@lem1920478)). Qed.
Lemma lem1920480 (x : real) (y : real) (h1 : term314 x y) : (term171 x y) = term2.
Proof. exact (EQ_MP (@lem1920479 x y) (@lem1920474 x y h1)). Qed.
Lemma lem1920481 (x : real) (y : real) (h1 : term314 x y) : term299 x y.
Proof. exact (conj (@lem1920480 x y h1) (@lem1920467 x y h1)). Qed.
Lemma lem1920483 (x : real) (y : real) : term104 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1920484 (x : real) (y : real) : term307 x y.
Proof. exact (@lem1920483 (term171 x y) (term238 x y)). Qed.
Lemma lem1920485 (x : real) (y : real) (h1 : term314 x y) : term308 x y.
Proof. exact (@lem1920484 x y (@lem1920481 x y h1)). Qed.
Lemma lem1920486 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (@lem1483480 (term168 x) (term205 x) (term205 y) (term168 y)). Qed.
Lemma lem1920487 (x : real) : (term296 x) = (term293 x).
Proof. exact (@lem1483442 term10 (term168 x)). Qed.
Lemma lem1920489 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920490 : term217 = term2.
Proof. exact (@lem1920489 term13). Qed.
Lemma lem1920491 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920492 : term218 = term112.
Proof. exact (MK_COMB (@lem1920491) (@lem1920490)). Qed.
Lemma lem1920493 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1920494 (x : real) : (term293 x) = (term294 x).
Proof. exact (MK_COMB (@lem1920492) (@lem1920493 x)). Qed.
Lemma lem1920495 (x : real) : (term296 x) = (term294 x).
Proof. exact (TRANS (@lem1920487 x) (@lem1920494 x)). Qed.
Lemma lem1920496 (x : real) : (term294 x) = term2.
Proof. exact (@lem1483446 (term168 x)). Qed.
Lemma lem1920497 (x : real) : (term296 x) = term2.
Proof. exact (TRANS (@lem1920495 x) (@lem1920496 x)). Qed.
Lemma lem1920498 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1920499 (x : real) : (term311 x) = term221.
Proof. exact (MK_COMB (@lem1920498) (@lem1920497 x)). Qed.
Lemma lem1920500 (y : real) : (term292 y) = (term293 y).
Proof. exact (@lem1483440 term10 (term168 y)). Qed.
Lemma lem1920502 (m : nat) : (term109 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1920503 : term217 = term2.
Proof. exact (@lem1920502 term13). Qed.
Lemma lem1920504 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1920505 : term218 = term112.
Proof. exact (MK_COMB (@lem1920504) (@lem1920503)). Qed.
Lemma lem1920506 (y : real) : (term168 y) = (term168 y).
Proof. exact (eq_refl (term168 y)). Qed.
Lemma lem1920507 (y : real) : (term293 y) = (term294 y).
Proof. exact (MK_COMB (@lem1920505) (@lem1920506 y)). Qed.
Lemma lem1920508 (y : real) : (term292 y) = (term294 y).
Proof. exact (TRANS (@lem1920500 y) (@lem1920507 y)). Qed.
Lemma lem1920509 (y : real) : (term294 y) = term2.
Proof. exact (@lem1483446 (term168 y)). Qed.
Lemma lem1920510 (y : real) : (term292 y) = term2.
Proof. exact (TRANS (@lem1920508 y) (@lem1920509 y)). Qed.
Lemma lem1920511 (x : real) (y : real) : (term310 x y) = term297.
Proof. exact (MK_COMB (@lem1920499 x) (@lem1920510 y)). Qed.
Lemma lem1920512 (x : real) (y : real) : (term309 x y) = term297.
Proof. exact (TRANS (@lem1920486 x y) (@lem1920511 x y)). Qed.
Lemma lem1920513 : term297 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1920514 (x : real) (y : real) : (term309 x y) = term2.
Proof. exact (TRANS (@lem1920512 x y) (@lem1920513)). Qed.
Lemma lem1920515 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1920516 (x : real) (y : real) : (term312 x y) = term115.
Proof. exact (MK_COMB (@lem1920515) (@lem1920514 x y)). Qed.
Lemma lem1920517 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1920518 (x : real) (y : real) : (term308 x y) = term116.
Proof. exact (MK_COMB (@lem1920516 x y) (@lem1920517)). Qed.
Lemma lem1920519 (x : real) (y : real) (h1 : term314 x y) : term116.
Proof. exact (EQ_MP (@lem1920518 x y) (@lem1920485 x y h1)). Qed.
Lemma lem1920521 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1920522 : term116 = term117.
Proof. exact (@lem1920521 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1920523 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1920524 : term116 = False.
Proof. exact (TRANS (@lem1920522) (@lem1920523)). Qed.
Lemma lem1920525 (x : real) (y : real) (h1 : term314 x y) : False.
Proof. exact (EQ_MP (@lem1920524) (@lem1920519 x y h1)). Qed.
Lemma lem1920526 (x : real) (y : real) (h1 : term272 x y) : False.
Proof. exact (or_elim (@lem1920340 x y h1) (fun h0 : term313 x y => @lem1920443 x y h0) (fun h0 : term314 x y => @lem1920525 x y h0)). Qed.
Lemma lem1920527 (x : real) (y : real) (h1 : term275 x y) : False.
Proof. exact (or_elim (@lem1920152 x y h1) (fun h0 : term273 x y => @lem1920339 x y h0) (fun h0 : term272 x y => @lem1920526 x y h0)). Qed.
Lemma lem1920529 (x : real) (y : real) (h1 : term275 x y) : term275 x y.
Proof. exact (h1). Qed.
Lemma lem1920530 (x : real) (y : real) (h1 : term275 x y) : (term275 x y) = False.
Proof. exact (prop_ext (fun h2 : term275 x y => @lem1920527 x y h1) (fun h2 : False => @lem1920529 x y h1)). Qed.
Lemma lem1920531 (x : real) (y : real) (h1 : term275 x y) : False.
Proof. exact (EQ_MP (@lem1920530 x y h1) (@lem1920529 x y h1)). Qed.
Lemma lem1920532 (x : real) (y : real) (h1 : term166 x y) : term166 x y.
Proof. exact (h1). Qed.
Lemma lem1920533 (x : real) (y : real) (h1 : term166 x y) : term275 x y.
Proof. exact (EQ_MP (@lem1920130 x y) (@lem1920532 x y h1)). Qed.
Lemma lem1920534 (x : real) (y : real) (h1 : term166 x y) : (term275 x y) = False.
Proof. exact (prop_ext (fun h2 : term275 x y => @lem1920531 x y h2) (fun h2 : False => @lem1920533 x y h1)). Qed.
Lemma lem1920535 (x : real) (y : real) (h1 : term166 x y) : False.
Proof. exact (EQ_MP (@lem1920534 x y h1) (@lem1920533 x y h1)). Qed.
Lemma lem1920536 (x : real) (y : real) : term315 x y.
Proof. exact (fun h0 : term166 x y => @lem1920535 x y h0). Qed.
Lemma lem1920537 (x : real) (y : real) : term316 x y.
Proof. exact (@lem1386578 (((term168 x) = (term168 y)) = ((term169 x y) = term2))). Qed.
Lemma lem1920539 (x : real) : term317 x.
Proof. exact (@lem1376695 x). Qed.
Lemma lem1920540 (x : real) : (term317 x) = (term318 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1920541 (x : real) : term318 x.
Proof. exact (EQ_MP (@lem1920540 x) (@lem1920539 x)). Qed.
Lemma lem1920542 (x : real) (y : real) : term319 x y.
Proof. exact (@lem1920541 x y). Qed.
Lemma lem1920543 (x : real) (y : real) : (term319 x y) = (((real_sub x y) = term2) = (x = y)).
Proof. exact (eq_refl (term319 x y)). Qed.
Lemma lem1920545 (x : real) : term320 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1920546 (x : real) : (term320 x) = (term321 x).
Proof. exact (eq_refl (term320 x)). Qed.
Lemma lem1920547 (x : real) : term321 x.
Proof. exact (EQ_MP (@lem1920546 x) (@lem1920545 x)). Qed.
Lemma lem1920548 (x : real) (y : real) : term322 x y.
Proof. exact (@lem1920547 x y). Qed.
Lemma lem1920549 (x : real) (y : real) : (term322 x y) = (((real_mul x y) = term2) = (term323 x y)).
Proof. exact (eq_refl (term322 x y)). Qed.
Lemma lem1920551 (x : real) : term324 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1920552 (x : real) : (term324 x) = (term325 x).
Proof. exact (eq_refl (term324 x)). Qed.
Lemma lem1920553 (x : real) : term325 x.
Proof. exact (EQ_MP (@lem1920552 x) (@lem1920551 x)). Qed.
Lemma lem1920555 (x : real) (h1 : (term326 x) = (real_sgn x)) : (term326 x) = (real_sgn x).
Proof. exact (h1). Qed.
Lemma lem1920556 (x : real) (h1 : (term326 x) = (real_sgn x)) : (real_sgn x) = (term326 x).
Proof. exact (SYM (@lem1920555 x h1)). Qed.
Lemma lem1920557 (x : real) (h1 : (real_sgn x) = (term326 x)) : (real_sgn x) = (term326 x).
Proof. exact (h1). Qed.
Lemma lem1920558 (x : real) (h1 : (real_sgn x) = (term326 x)) : (term326 x) = (real_sgn x).
Proof. exact (SYM (@lem1920557 x h1)). Qed.
Lemma lem1920559 (x : real) : ((term326 x) = (real_sgn x)) = ((real_sgn x) = (term326 x)).
Proof. exact (prop_ext (fun h1 : (term326 x) = (real_sgn x) => @lem1920556 x h1) (fun h1 : (real_sgn x) = (term326 x) => @lem1920558 x h1)). Qed.
Lemma lem1920560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1920561 (x : real) : (term327 x) = (term328 x).
Proof. exact (MK_COMB (@lem1920560) (@lem1920559 x)). Qed.
Lemma lem1920562 (x : real) (h1 : (term329 x) = (real_abs x)) : (term329 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1920563 (x : real) (h1 : (term329 x) = (real_abs x)) : (real_abs x) = (term329 x).
Proof. exact (SYM (@lem1920562 x h1)). Qed.
Lemma lem1920564 (x : real) (h1 : (real_abs x) = (term329 x)) : (real_abs x) = (term329 x).
Proof. exact (h1). Qed.
Lemma lem1920565 (x : real) (h1 : (real_abs x) = (term329 x)) : (term329 x) = (real_abs x).
Proof. exact (SYM (@lem1920564 x h1)). Qed.
Lemma lem1920566 (x : real) : ((term329 x) = (real_abs x)) = ((real_abs x) = (term329 x)).
Proof. exact (prop_ext (fun h1 : (term329 x) = (real_abs x) => @lem1920563 x h1) (fun h1 : (real_abs x) = (term329 x) => @lem1920565 x h1)). Qed.
Lemma lem1920567 (x : real) : (term325 x) = (term330 x).
Proof. exact (MK_COMB (@lem1920561 x) (@lem1920566 x)). Qed.
Lemma lem1920568 (x : real) : term330 x.
Proof. exact (EQ_MP (@lem1920567 x) (@lem1920553 x)). Qed.
Lemma lem1920572 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term331 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1920573 (p : Prop) (q : Prop) (p' : Prop) : term332 p q p'.
Proof. exact (fun q' : Prop => @lem1920572 p q p' q'). Qed.
Lemma lem1920574 (p : Prop) (q : Prop) : term333 p q.
Proof. exact (fun p' : Prop => @lem1920573 p q p'). Qed.
Lemma lem1920575 (x : real) (y : real) : term334 x y.
Proof. exact (@lem1920574 (term330 x) (term335 x y)). Qed.
Lemma lem1920576 (x : real) (y : real) (p' : Prop) : term336 x y p'.
Proof. exact (@lem1920575 x y p'). Qed.
Lemma lem1920577 (x : real) (y : real) (p' : Prop) : (term336 x y p') = (term337 x y p').
Proof. exact (eq_refl (term336 x y p')). Qed.
Lemma lem1920578 (x : real) (y : real) (p' : Prop) : term337 x y p'.
Proof. exact (EQ_MP (@lem1920577 x y p') (@lem1920576 x y p')). Qed.
Lemma lem1920579 (x : real) (y : real) (p' : Prop) (q' : Prop) : term338 x y p' q'.
Proof. exact (@lem1920578 x y p' q'). Qed.
Lemma lem1920580 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term338 x y p' q') = (term339 x y p' q').
Proof. exact (eq_refl (term338 x y p' q')). Qed.
Lemma lem1920581 (x : real) (y : real) (p' : Prop) (q' : Prop) : term339 x y p' q'.
Proof. exact (EQ_MP (@lem1920580 x y p' q') (@lem1920579 x y p' q')). Qed.
Lemma lem1920588 (x : real) : (term330 x) = (term330 x).
Proof. exact (eq_refl (term330 x)). Qed.
Lemma lem1920589 (y : real) (x : real) (q' : Prop) : term340 y x q'.
Proof. exact (@lem1920581 x y (term330 x) q'). Qed.
Lemma lem1920590 (y : real) (x : real) (q' : Prop) : term341 y x q'.
Proof. exact (@lem1920589 y x q' (@lem1920588 x)). Qed.
Lemma lem1920591 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1920597 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term331 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1920598 (p : Prop) (q : Prop) (p' : Prop) : term332 p q p'.
Proof. exact (fun q' : Prop => @lem1920597 p q p' q'). Qed.
Lemma lem1920599 (p : Prop) (q : Prop) : term333 p q.
Proof. exact (fun p' : Prop => @lem1920598 p q p'). Qed.
Lemma lem1920600 (x : real) (y : real) : term342 x y.
Proof. exact (@lem1920599 (term343 y x) ((sqrt x) = y)). Qed.
Lemma lem1920601 (x : real) (y : real) (p' : Prop) : term344 x y p'.
Proof. exact (@lem1920600 x y p'). Qed.
Lemma lem1920602 (x : real) (y : real) (p' : Prop) : (term344 x y p') = (term345 x y p').
Proof. exact (eq_refl (term344 x y p')). Qed.
Lemma lem1920603 (x : real) (y : real) (p' : Prop) : term345 x y p'.
Proof. exact (EQ_MP (@lem1920602 x y p') (@lem1920601 x y p')). Qed.
Lemma lem1920604 (x : real) (y : real) (p' : Prop) (q' : Prop) : term346 x y p' q'.
Proof. exact (@lem1920603 x y p' q'). Qed.
Lemma lem1920605 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term346 x y p' q') = (term347 x y p' q').
Proof. exact (eq_refl (term346 x y p' q')). Qed.
Lemma lem1920606 (x : real) (y : real) (p' : Prop) (q' : Prop) : term347 x y p' q'.
Proof. exact (EQ_MP (@lem1920605 x y p' q') (@lem1920604 x y p' q')). Qed.
Lemma lem1920612 (x : real) (h1 : term330 x) : (real_sgn x) = (term326 x).
Proof. exact (proj1 (@lem1920591 x h1)). Qed.
Lemma lem1920613 (y : real) : (term348 y) = (term348 y).
Proof. exact (eq_refl (term348 y)). Qed.
Lemma lem1920614 (y : real) (x : real) (h1 : term330 x) : ((real_sgn y) = (real_sgn x)) = ((real_sgn y) = (term326 x)).
Proof. exact (MK_COMB (@lem1920613 y) (@lem1920612 x h1)). Qed.
Lemma lem1920617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1920618 (y : real) (x : real) (h1 : term330 x) : (term349 y x) = (term350 y x).
Proof. exact (MK_COMB (@lem1920617) (@lem1920614 y x h1)). Qed.
Lemma lem1920624 (x : real) (h1 : term330 x) : (real_abs x) = (term329 x).
Proof. exact (proj2 (@lem1920591 x h1)). Qed.
Lemma lem1920625 (y : real) : (term351 y) = (term351 y).
Proof. exact (eq_refl (term351 y)). Qed.
Lemma lem1920626 (y : real) (x : real) (h1 : term330 x) : ((term168 y) = (real_abs x)) = ((term168 y) = (term329 x)).
Proof. exact (MK_COMB (@lem1920625 y) (@lem1920624 x h1)). Qed.
Lemma lem1920628 (x : real) (y : real) : ((term168 x) = (term168 y)) = ((term169 x y) = term2).
Proof. exact (@lem1920537 x y (@lem1920536 x y)). Qed.
Lemma lem1920629 (y : real) (x : real) : ((term168 y) = (term329 x)) = ((term352 y x) = term2).
Proof. exact (@lem1920628 y (sqrt x)). Qed.
Lemma lem1920631 (x : real) (y : real) : ((real_mul x y) = term2) = (term323 x y).
Proof. exact (EQ_MP (@lem1920549 x y) (@lem1920548 x y)). Qed.
Lemma lem1920632 (y : real) (x : real) : ((term352 y x) = term2) = (term353 y x).
Proof. exact (@lem1920631 (term354 y x) (term355 y x)). Qed.
Lemma lem1920636 (x : real) (y : real) : ((real_sub x y) = term2) = (x = y).
Proof. exact (EQ_MP (@lem1920543 x y) (@lem1920542 x y)). Qed.
Lemma lem1920637 (y : real) (x : real) : ((term354 y x) = term2) = (y = (sqrt x)).
Proof. exact (@lem1920636 y (sqrt x)). Qed.
Lemma lem1920640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1920641 (y : real) (x : real) : (term356 y x) = (term357 y x).
Proof. exact (MK_COMB (@lem1920640) (@lem1920637 y x)). Qed.
Lemma lem1920645 (x : real) (y : real) : ((real_sub x y) = term2) = (x = y).
Proof. exact (EQ_MP (@lem1920543 x y) (@lem1920542 x y)). Qed.
Lemma lem1920646 (y : real) (x : real) : ((term355 y x) = term2) = (y = (term358 x)).
Proof. exact (@lem1920645 y (term358 x)). Qed.
Lemma lem1920649 (y : real) (x : real) : (term353 y x) = (term359 y x).
Proof. exact (MK_COMB (@lem1920641 y x) (@lem1920646 y x)). Qed.
Lemma lem1920656 (y : real) (x : real) : ((term352 y x) = term2) = (term359 y x).
Proof. exact (TRANS (@lem1920632 y x) (@lem1920649 y x)). Qed.
Lemma lem1920657 (y : real) (x : real) : ((term168 y) = (term329 x)) = (term359 y x).
Proof. exact (TRANS (@lem1920629 y x) (@lem1920656 y x)). Qed.
Lemma lem1920658 (y : real) (x : real) (h1 : term330 x) : ((term168 y) = (real_abs x)) = (term359 y x).
Proof. exact (TRANS (@lem1920626 y x h1) (@lem1920657 y x)). Qed.
Lemma lem1920659 (y : real) (x : real) (h1 : term330 x) : (term343 y x) = (term360 y x).
Proof. exact (MK_COMB (@lem1920618 y x h1) (@lem1920658 y x h1)). Qed.
Lemma lem1920670 (y : real) (x : real) (q' : Prop) : term361 y x q'.
Proof. exact (@lem1920606 x y (term360 y x) q'). Qed.
Lemma lem1920671 (y : real) (q' : Prop) (x : real) (h1 : term330 x) : term362 y x q'.
Proof. exact (@lem1920670 y x q' (@lem1920659 y x h1)). Qed.
Lemma lem1920679 (x : real) (y : real) : ((sqrt x) = y) = ((sqrt x) = y).
Proof. exact (eq_refl ((sqrt x) = y)). Qed.
Lemma lem1920680 (x : real) (y : real) : term363 x y.
Proof. exact (fun h0 : term360 y x => @lem1920679 x y). Qed.
Lemma lem1920681 (y : real) (x : real) (h1 : term330 x) : term364 x y.
Proof. exact (@lem1920671 y ((sqrt x) = y) x h1). Qed.
Lemma lem1920682 (y : real) (x : real) (h1 : term330 x) : (term335 x y) = (term365 x y).
Proof. exact (@lem1920681 y x h1 (@lem1920680 x y)). Qed.
Lemma lem1920732 (x : real) (y : real) : term366 x y.
Proof. exact (fun h0 : term330 x => @lem1920682 y x h0). Qed.
Lemma lem1920733 (x : real) (y : real) : term367 x y.
Proof. exact (@lem1920590 y x (term365 x y)). Qed.
Lemma lem1920734 (x : real) (y : real) : (term368 x y) = (term369 x y).
Proof. exact (@lem1920733 x y (@lem1920732 x y)). Qed.
Lemma lem1920868 (x : real) (y : real) : (term369 x y) = (term368 x y).
Proof. exact (SYM (@lem1920734 x y)). Qed.
Lemma lem1920871 (q : Prop) (p : Prop) (r : Prop) : (term370 p q r) = (term371 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem1920872 (x : real) (y : real) : (term365 x y) = (term372 x y).
Proof. exact (@lem1920871 (term359 y x) ((real_sgn y) = (term326 x)) ((sqrt x) = y)). Qed.
Lemma lem1920889 (x : real) (y : real) : (term372 x y) = (term365 x y).
Proof. exact (SYM (@lem1920872 x y)). Qed.
Lemma lem1920890 (y : real) (x : real) (h1 : term359 y x) : term359 y x.
Proof. exact (h1). Qed.
Lemma lem1920891 (y : real) (x : real) (h1 : y = (sqrt x)) : y = (sqrt x).
Proof. exact (h1). Qed.
Lemma lem1920892 (y : real) (x : real) (h1 : y = (term358 x)) : y = (term358 x).
Proof. exact (h1). Qed.
Lemma lem1920903 (y : real) (x : real) (h1 : y = (sqrt x)) : y = (sqrt x).
Proof. exact (h1). Qed.
Lemma lem1920904 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem1920905 (y : real) (x : real) (h1 : y = (sqrt x)) : (real_sgn y) = (term326 x).
Proof. exact (MK_COMB (@lem1920904) (@lem1920903 y x h1)). Qed.
Lemma lem1920906 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920907 (y : real) (x : real) (h1 : y = (sqrt x)) : (term348 y) = (term373 x).
Proof. exact (MK_COMB (@lem1920906) (@lem1920905 y x h1)). Qed.
Lemma lem1920908 (x : real) : (term326 x) = (term326 x).
Proof. exact (eq_refl (term326 x)). Qed.
Lemma lem1920909 (y : real) (x : real) (h1 : y = (sqrt x)) : ((real_sgn y) = (term326 x)) = ((term326 x) = (term326 x)).
Proof. exact (MK_COMB (@lem1920907 y x h1) (@lem1920908 x)). Qed.
Lemma lem1920911 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1920912 (x : real) : (x = x) = True.
Proof. exact (@lem1920911 real x). Qed.
Lemma lem1920913 (x : real) : ((term326 x) = (term326 x)) = True.
Proof. exact (@lem1920912 (term326 x)). Qed.
Lemma lem1920914 (y : real) (x : real) (h1 : y = (sqrt x)) : ((real_sgn y) = (term326 x)) = True.
Proof. exact (TRANS (@lem1920909 y x h1) (@lem1920913 x)). Qed.
Lemma lem1920915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1920916 (y : real) (x : real) (h1 : y = (sqrt x)) : (term374 y x) = (imp True).
Proof. exact (MK_COMB (@lem1920915) (@lem1920914 y x h1)). Qed.
Lemma lem1920920 (y : real) (x : real) (h1 : y = (sqrt x)) : y = (sqrt x).
Proof. exact (h1). Qed.
Lemma lem1920921 (x : real) : (term375 x) = (term375 x).
Proof. exact (eq_refl (term375 x)). Qed.
Lemma lem1920922 (y : real) (x : real) (h1 : y = (sqrt x)) : ((sqrt x) = y) = ((sqrt x) = (sqrt x)).
Proof. exact (MK_COMB (@lem1920921 x) (@lem1920920 y x h1)). Qed.
Lemma lem1920924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1920925 (x : real) : (x = x) = True.
Proof. exact (@lem1920924 real x). Qed.
Lemma lem1920926 (x : real) : ((sqrt x) = (sqrt x)) = True.
Proof. exact (@lem1920925 (sqrt x)). Qed.
Lemma lem1920927 (y : real) (x : real) (h1 : y = (sqrt x)) : ((sqrt x) = y) = True.
Proof. exact (TRANS (@lem1920922 y x h1) (@lem1920926 x)). Qed.
Lemma lem1920928 (y : real) (x : real) (h1 : y = (sqrt x)) : (term376 x y) = (True -> True).
Proof. exact (MK_COMB (@lem1920916 y x h1) (@lem1920927 y x h1)). Qed.
Lemma lem1920930 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1920931 : (True -> True) = True.
Proof. exact (@lem1920930 True). Qed.
Lemma lem1920932 (y : real) (x : real) (h1 : y = (sqrt x)) : (term376 x y) = True.
Proof. exact (TRANS (@lem1920928 y x h1) (@lem1920931)). Qed.
Lemma lem1920933 (y : real) (x : real) (h1 : y = (sqrt x)) : True = (term376 x y).
Proof. exact (SYM (@lem1920932 y x h1)). Qed.
Lemma lem1920934 (y : real) (x : real) (h1 : y = (sqrt x)) : term376 x y.
Proof. exact (EQ_MP (@lem1920933 y x h1) (@lem0)). Qed.
Lemma lem1920935 (x : real) : term377 x.
Proof. exact (@lem1715400 x). Qed.
Lemma lem1920936 (x : real) : (term377 x) = ((term378 x) = (term379 x)).
Proof. exact (eq_refl (term377 x)). Qed.
Lemma lem1920945 (y : real) (x : real) (h1 : y = (term358 x)) : y = (term358 x).
Proof. exact (h1). Qed.
Lemma lem1920946 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem1920947 (y : real) (x : real) (h1 : y = (term358 x)) : (real_sgn y) = (term380 x).
Proof. exact (MK_COMB (@lem1920946) (@lem1920945 y x h1)). Qed.
Lemma lem1920949 (x : real) : (term378 x) = (term379 x).
Proof. exact (EQ_MP (@lem1920936 x) (@lem1920935 x)). Qed.
Lemma lem1920950 (x : real) : (term380 x) = (term381 x).
Proof. exact (@lem1920949 (sqrt x)). Qed.
Lemma lem1920951 (y : real) (x : real) (h1 : y = (term358 x)) : (real_sgn y) = (term381 x).
Proof. exact (TRANS (@lem1920947 y x h1) (@lem1920950 x)). Qed.
Lemma lem1920952 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1920953 (y : real) (x : real) (h1 : y = (term358 x)) : (term348 y) = (term382 x).
Proof. exact (MK_COMB (@lem1920952) (@lem1920951 y x h1)). Qed.
Lemma lem1920954 (x : real) : (term326 x) = (term326 x).
Proof. exact (eq_refl (term326 x)). Qed.
Lemma lem1920955 (y : real) (x : real) (h1 : y = (term358 x)) : ((real_sgn y) = (term326 x)) = ((term381 x) = (term326 x)).
Proof. exact (MK_COMB (@lem1920953 y x h1) (@lem1920954 x)). Qed.
Lemma lem1920958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1920959 (y : real) (x : real) (h1 : y = (term358 x)) : (term374 y x) = (term383 x).
Proof. exact (MK_COMB (@lem1920958) (@lem1920955 y x h1)). Qed.
Lemma lem1920963 (y : real) (x : real) (h1 : y = (term358 x)) : y = (term358 x).
Proof. exact (h1). Qed.
Lemma lem1920964 (x : real) : (term375 x) = (term375 x).
Proof. exact (eq_refl (term375 x)). Qed.
Lemma lem1920965 (y : real) (x : real) (h1 : y = (term358 x)) : ((sqrt x) = y) = ((sqrt x) = (term358 x)).
Proof. exact (MK_COMB (@lem1920964 x) (@lem1920963 y x h1)). Qed.
Lemma lem1920968 (y : real) (x : real) (h1 : y = (term358 x)) : (term376 x y) = (term384 x).
Proof. exact (MK_COMB (@lem1920959 y x h1) (@lem1920965 y x h1)). Qed.
Lemma lem1920973 (y : real) (x : real) (h1 : y = (term358 x)) : (term384 x) = (term376 x y).
Proof. exact (SYM (@lem1920968 y x h1)). Qed.
Lemma lem1920979 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term331 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1920980 (p : Prop) (q : Prop) (p' : Prop) : term332 p q p'.
Proof. exact (fun q' : Prop => @lem1920979 p q p' q'). Qed.
Lemma lem1920981 (p : Prop) (q : Prop) : term333 p q.
Proof. exact (fun p' : Prop => @lem1920980 p q p'). Qed.
Lemma lem1920982 (x : real) : term385 x.
Proof. exact (@lem1920981 ((term381 x) = (term326 x)) ((sqrt x) = (term358 x))). Qed.
Lemma lem1920983 (x : real) (p' : Prop) : term386 x p'.
Proof. exact (@lem1920982 x p'). Qed.
Lemma lem1920984 (x : real) (p' : Prop) : (term386 x p') = (term387 x p').
Proof. exact (eq_refl (term386 x p')). Qed.
Lemma lem1920985 (x : real) (p' : Prop) : term387 x p'.
Proof. exact (EQ_MP (@lem1920984 x p') (@lem1920983 x p')). Qed.
Lemma lem1920986 (x : real) (p' : Prop) (q' : Prop) : term388 x p' q'.
Proof. exact (@lem1920985 x p' q'). Qed.
Lemma lem1920987 (x : real) (p' : Prop) (q' : Prop) : (term388 x p' q') = (term389 x p' q').
Proof. exact (eq_refl (term388 x p' q')). Qed.
Lemma lem1920988 (x : real) (p' : Prop) (q' : Prop) : term389 x p' q'.
Proof. exact (EQ_MP (@lem1920987 x p' q') (@lem1920986 x p' q')). Qed.
Lemma lem1920990 (x : real) : ((real_neg x) = x) = (x = term2).
Proof. exact (@lem1919647 x (@lem1919646 x)). Qed.
Lemma lem1920991 (x : real) : ((term381 x) = (term326 x)) = ((term326 x) = term2).
Proof. exact (@lem1920990 (term326 x)). Qed.
Lemma lem1920993 (x : real) : ((real_sgn x) = term2) = (x = term2).
Proof. exact (EQ_MP (@lem1919660 x) (@lem1919659 x)). Qed.
Lemma lem1920994 (x : real) : ((term326 x) = term2) = ((sqrt x) = term2).
Proof. exact (@lem1920993 (sqrt x)). Qed.
Lemma lem1920997 (x : real) : ((term381 x) = (term326 x)) = ((sqrt x) = term2).
Proof. exact (TRANS (@lem1920991 x) (@lem1920994 x)). Qed.
Lemma lem1920998 (x : real) (q' : Prop) : term390 x q'.
Proof. exact (@lem1920988 x ((sqrt x) = term2) q'). Qed.
Lemma lem1920999 (x : real) (q' : Prop) : term391 x q'.
Proof. exact (@lem1920998 x q' (@lem1920997 x)). Qed.
Lemma lem1921004 (x : real) (h1 : (sqrt x) = term2) : (sqrt x) = term2.
Proof. exact (h1). Qed.
Lemma lem1921005 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921006 (x : real) (h1 : (sqrt x) = term2) : (term375 x) = term392.
Proof. exact (MK_COMB (@lem1921005) (@lem1921004 x h1)). Qed.
Lemma lem1921008 (x : real) (h1 : (sqrt x) = term2) : (sqrt x) = term2.
Proof. exact (h1). Qed.
Lemma lem1921009 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1921010 (x : real) (h1 : (sqrt x) = term2) : (term358 x) = term393.
Proof. exact (MK_COMB (@lem1921009) (@lem1921008 x h1)). Qed.
Lemma lem1921012 : term393 = term2.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
Lemma lem1921013 (x : real) (h1 : (sqrt x) = term2) : (term358 x) = term2.
Proof. exact (TRANS (@lem1921010 x h1) (@lem1921012)). Qed.
Lemma lem1921014 (x : real) (h1 : (sqrt x) = term2) : ((sqrt x) = (term358 x)) = (term2 = term2).
Proof. exact (MK_COMB (@lem1921006 x h1) (@lem1921013 x h1)). Qed.
Lemma lem1921016 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1921017 (x : real) : (x = x) = True.
Proof. exact (@lem1921016 real x). Qed.
Lemma lem1921018 : (term2 = term2) = True.
Proof. exact (@lem1921017 term2). Qed.
Lemma lem1921019 (x : real) (h1 : (sqrt x) = term2) : ((sqrt x) = (term358 x)) = True.
Proof. exact (TRANS (@lem1921014 x h1) (@lem1921018)). Qed.
Lemma lem1921020 (x : real) : term394 x.
Proof. exact (fun h0 : (sqrt x) = term2 => @lem1921019 x h0). Qed.
Lemma lem1921021 (x : real) : term395 x.
Proof. exact (@lem1920999 x True). Qed.
Lemma lem1921022 (x : real) : (term384 x) = (term396 x).
Proof. exact (@lem1921021 x (@lem1921020 x)). Qed.
Lemma lem1921026 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1921027 (x : real) : (term396 x) = True.
Proof. exact (@lem1921026 ((sqrt x) = term2)). Qed.
Lemma lem1921028 (x : real) : (term384 x) = True.
Proof. exact (TRANS (@lem1921022 x) (@lem1921027 x)). Qed.
Lemma lem1921029 (x : real) : True = (term384 x).
Proof. exact (SYM (@lem1921028 x)). Qed.
Lemma lem1921030 (x : real) : term384 x.
Proof. exact (EQ_MP (@lem1921029 x) (@lem0)). Qed.
Lemma lem1921031 (y : real) (x : real) (h1 : y = (term358 x)) : term376 x y.
Proof. exact (EQ_MP (@lem1920973 y x h1) (@lem1921030 x)). Qed.
Lemma lem1921032 (y : real) (x : real) (h1 : y = (term358 x)) : (y = (term358 x)) = (term376 x y).
Proof. exact (prop_ext (fun h2 : y = (term358 x) => @lem1921031 y x h1) (fun h2 : term376 x y => @lem1920892 y x h1)). Qed.
Lemma lem1921033 (y : real) (x : real) (h1 : y = (term358 x)) : term376 x y.
Proof. exact (EQ_MP (@lem1921032 y x h1) (@lem1920892 y x h1)). Qed.
Lemma lem1921034 (y : real) (x : real) (h1 : y = (sqrt x)) : (y = (sqrt x)) = (term376 x y).
Proof. exact (prop_ext (fun h2 : y = (sqrt x) => @lem1920934 y x h1) (fun h2 : term376 x y => @lem1920891 y x h1)). Qed.
Lemma lem1921035 (y : real) (x : real) (h1 : y = (sqrt x)) : term376 x y.
Proof. exact (EQ_MP (@lem1921034 y x h1) (@lem1920891 y x h1)). Qed.
Lemma lem1921036 (y : real) (x : real) (h1 : term359 y x) : term376 x y.
Proof. exact (or_elim (@lem1920890 y x h1) (fun h0 : y = (sqrt x) => @lem1921035 y x h0) (fun h0 : y = (term358 x) => @lem1921033 y x h0)). Qed.
Lemma lem1921037 (x : real) (y : real) : term372 x y.
Proof. exact (fun h0 : term359 y x => @lem1921036 y x h0). Qed.
Lemma lem1921038 (x : real) (y : real) : term365 x y.
Proof. exact (EQ_MP (@lem1920889 x y) (@lem1921037 x y)). Qed.
Lemma lem1921039 (x : real) (y : real) : term369 x y.
Proof. exact (fun h0 : term330 x => @lem1921038 x y). Qed.
Lemma lem1921040 (x : real) (y : real) : term368 x y.
Proof. exact (EQ_MP (@lem1920868 x y) (@lem1921039 x y)). Qed.
Lemma lem1921041 (x : real) (y : real) : term335 x y.
Proof. exact (@lem1921040 x y (@lem1920568 x)). Qed.
Lemma lem1921046 (x : real) : term397 x.
Proof. exact (fun y : real => @lem1921041 x y). Qed.
Lemma lem1921051 : term398.
Proof. exact (fun x : real => @lem1921046 x). Qed.
