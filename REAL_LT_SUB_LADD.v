Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_SUB_LADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
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
Lemma lem1514173 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1514174 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1514175 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1514174 (term8 x y)). Qed.
Lemma lem1514176 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1514177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1514178 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1514177) (@lem1514176 x z y)). Qed.
Lemma lem1514179 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1514178 x z y) (@lem1514173 x z y)). Qed.
Lemma lem1514180 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1514179 x z y)). Qed.
Lemma lem1514181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514182 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1514181) (@lem1514180 x y)). Qed.
Lemma lem1514183 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1514175 x y) (@lem1514182 x y)). Qed.
Lemma lem1514184 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1514185 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1514184 (term16 x)). Qed.
Lemma lem1514186 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1514187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1514188 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1514187) (@lem1514186 x y)). Qed.
Lemma lem1514189 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1514188 x y) (@lem1514183 x y)). Qed.
Lemma lem1514190 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1514189 x y)). Qed.
Lemma lem1514191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514192 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1514191) (@lem1514190 x)). Qed.
Lemma lem1514193 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1514185 x) (@lem1514192 x)). Qed.
Lemma lem1514194 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1514195 : term23 = term24.
Proof. exact (@lem1514194 term25). Qed.
Lemma lem1514196 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1514197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1514198 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1514197) (@lem1514196 x)). Qed.
Lemma lem1514199 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1514198 x) (@lem1514193 x)). Qed.
Lemma lem1514200 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1514199 x)). Qed.
Lemma lem1514201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514202 : term24 = term31.
Proof. exact (MK_COMB (@lem1514201) (@lem1514200)). Qed.
Lemma lem1514204 : term23 = term31.
Proof. exact (TRANS (@lem1514195) (@lem1514202)). Qed.
Lemma lem1514221 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1514222 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1514221 x z y)). Qed.
Lemma lem1514223 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514224 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1514223) (@lem1514222 x y)). Qed.
Lemma lem1514225 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1514224 x y)). Qed.
Lemma lem1514226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514227 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1514226) (@lem1514225 x)). Qed.
Lemma lem1514228 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1514227 x)). Qed.
Lemma lem1514229 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514230 : term31 = term31.
Proof. exact (MK_COMB (@lem1514229) (@lem1514228)). Qed.
Lemma lem1514231 : term23 = term31.
Proof. exact (TRANS (@lem1514204) (@lem1514230)). Qed.
Lemma lem1514232 (y : real) (z : real) (x : real) : (term2 x y z) = (term32 y z x).
Proof. exact (@lem1483521 (real_sub y z) x). Qed.
Lemma lem1514233 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1514246 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1514247 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1514248 (y : real) (z : real) : (term34 y z) = (term35 y z).
Proof. exact (MK_COMB (@lem1514247) (@lem1514246 y z)). Qed.
Lemma lem1514249 (y : real) (z : real) (x : real) : (term36 y z x) = (term37 y z x).
Proof. exact (MK_COMB (@lem1514248 y z) (@lem1514233 x)). Qed.
Lemma lem1514250 (y : real) (z : real) (x : real) : (term37 y z x) = (term38 y z x).
Proof. exact (@lem1483519 (term33 y z) x). Qed.
Lemma lem1514255 (x : real) (y : real) (z : real) : (term38 y z x) = (term39 x y z).
Proof. exact (@lem1483488 (term40 x) (term33 y z)). Qed.
Lemma lem1514256 (x : real) (y : real) (z : real) : (term37 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem1514250 y z x) (@lem1514255 x y z)). Qed.
Lemma lem1514257 (x : real) (y : real) (z : real) : (term36 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem1514249 y z x) (@lem1514256 x y z)). Qed.
Lemma lem1514258 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514259 (x : real) (y : real) (z : real) : (term41 y z x) = (term42 x y z).
Proof. exact (MK_COMB (@lem1514258) (@lem1514257 x y z)). Qed.
Lemma lem1514260 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514261 (x : real) (y : real) (z : real) : (term32 y z x) = (term44 x y z).
Proof. exact (MK_COMB (@lem1514259 x y z) (@lem1514260)). Qed.
Lemma lem1514262 (x : real) (y : real) (z : real) : (term2 x y z) = (term44 x y z).
Proof. exact (TRANS (@lem1514232 y z x) (@lem1514261 x y z)). Qed.
Lemma lem1514263 (x : real) (z : real) (y : real) : (term45 x z y) = (term46 x z y).
Proof. exact (@lem1483531 (real_add x z) y). Qed.
Lemma lem1514275 (x : real) (z : real) (y : real) : (term47 x z y) = (term48 x z y).
Proof. exact (@lem1483519 (real_add x z) y). Qed.
Lemma lem1514279 (x : real) (z : real) (y : real) : (term48 x z y) = (term49 x z y).
Proof. exact (@lem1483482 x z (term40 y)). Qed.
Lemma lem1514280 (y : real) (z : real) : (term33 z y) = (term50 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1514281 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1514282 (x : real) (y : real) (z : real) : (term49 x z y) = (term51 x y z).
Proof. exact (MK_COMB (@lem1514281 x) (@lem1514280 y z)). Qed.
Lemma lem1514284 (x : real) (y : real) (z : real) : (term48 x z y) = (term51 x y z).
Proof. exact (TRANS (@lem1514279 x z y) (@lem1514282 x y z)). Qed.
Lemma lem1514286 (x : real) (y : real) (z : real) : (term47 x z y) = (term51 x y z).
Proof. exact (TRANS (@lem1514275 x z y) (@lem1514284 x y z)). Qed.
Lemma lem1514287 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1514288 (x : real) (y : real) (z : real) : (term52 x z y) = (term53 x y z).
Proof. exact (MK_COMB (@lem1514287) (@lem1514286 x y z)). Qed.
Lemma lem1514289 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514290 (x : real) (y : real) (z : real) : (term46 x z y) = (term54 x y z).
Proof. exact (MK_COMB (@lem1514288 x y z) (@lem1514289)). Qed.
Lemma lem1514291 (x : real) (y : real) (z : real) : (term45 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1514263 x z y) (@lem1514290 x y z)). Qed.
Lemma lem1514292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1514293 (x : real) (y : real) (z : real) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1514292) (@lem1514262 x y z)). Qed.
Lemma lem1514294 (x : real) (y : real) (z : real) : (term57 x z y) = (term58 x y z).
Proof. exact (MK_COMB (@lem1514293 x y z) (@lem1514291 x y z)). Qed.
Lemma lem1514295 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483531 x (real_sub y z)). Qed.
Lemma lem1514308 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1514311 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1514312 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1514311 x) (@lem1514308 y z)). Qed.
Lemma lem1514313 (x : real) (y : real) (z : real) : (term62 x y z) = (term63 x y z).
Proof. exact (@lem1483519 x (term33 y z)). Qed.
Lemma lem1514314 (y : real) (z : real) : (term64 y z) = (term65 y z).
Proof. exact (@lem1483508 y term66 (term40 z)). Qed.
Lemma lem1514315 (z : real) : (term67 z) = (term68 z).
Proof. exact (@lem1483476 term66 term66 z). Qed.
Lemma lem1514317 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1514318 : term71 = term72.
Proof. exact (@lem1514317 term73 term73). Qed.
Lemma lem1514319 : (term74 = (BIT1 0)) = (term75 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1514320 : term75 = term73.
Proof. exact (EQ_MP (@lem1514319) (@lem940073)). Qed.
Lemma lem1514321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1514322 : term72 = term76.
Proof. exact (MK_COMB (@lem1514321) (@lem1514320)). Qed.
Lemma lem1514323 : term71 = term76.
Proof. exact (TRANS (@lem1514318) (@lem1514322)). Qed.
Lemma lem1514324 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1514325 : term77 = term78.
Proof. exact (MK_COMB (@lem1514324) (@lem1514323)). Qed.
Lemma lem1514326 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1514327 (z : real) : (term68 z) = (term79 z).
Proof. exact (MK_COMB (@lem1514325) (@lem1514326 z)). Qed.
Lemma lem1514328 (z : real) : (term67 z) = (term79 z).
Proof. exact (TRANS (@lem1514315 z) (@lem1514327 z)). Qed.
Lemma lem1514329 (z : real) : (term79 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1514330 (z : real) : (term67 z) = z.
Proof. exact (TRANS (@lem1514328 z) (@lem1514329 z)). Qed.
Lemma lem1514333 (y : real) : (term80 y) = (term80 y).
Proof. exact (eq_refl (term80 y)). Qed.
Lemma lem1514334 (y : real) (z : real) : (term65 y z) = (term50 y z).
Proof. exact (MK_COMB (@lem1514333 y) (@lem1514330 z)). Qed.
Lemma lem1514335 (y : real) (z : real) : (term64 y z) = (term50 y z).
Proof. exact (TRANS (@lem1514314 y z) (@lem1514334 y z)). Qed.
Lemma lem1514336 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1514339 (x : real) (y : real) (z : real) : (term63 x y z) = (term51 x y z).
Proof. exact (MK_COMB (@lem1514336 x) (@lem1514335 y z)). Qed.
Lemma lem1514340 (x : real) (y : real) (z : real) : (term62 x y z) = (term51 x y z).
Proof. exact (TRANS (@lem1514313 x y z) (@lem1514339 x y z)). Qed.
Lemma lem1514341 (x : real) (y : real) (z : real) : (term61 x y z) = (term51 x y z).
Proof. exact (TRANS (@lem1514312 x y z) (@lem1514340 x y z)). Qed.
Lemma lem1514342 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1514343 (x : real) (y : real) (z : real) : (term81 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1514342) (@lem1514341 x y z)). Qed.
Lemma lem1514344 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514345 (x : real) (y : real) (z : real) : (term60 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1514343 x y z) (@lem1514344)). Qed.
Lemma lem1514346 (x : real) (y : real) (z : real) : (term59 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1514295 x y z) (@lem1514345 x y z)). Qed.
Lemma lem1514347 (y : real) (x : real) (z : real) : (term3 x z y) = (term82 y x z).
Proof. exact (@lem1483521 y (real_add x z)). Qed.
Lemma lem1514359 (y : real) (x : real) (z : real) : (term83 y x z) = (term84 y x z).
Proof. exact (@lem1483519 y (real_add x z)). Qed.
Lemma lem1514366 (x : real) (z : real) : (term85 x z) = (term86 x z).
Proof. exact (@lem1483508 x term66 z). Qed.
Lemma lem1514367 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1514368 (y : real) (x : real) (z : real) : (term84 y x z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1514367 y) (@lem1514366 x z)). Qed.
Lemma lem1514373 (x : real) (y : real) (z : real) : (term87 y x z) = (term39 x y z).
Proof. exact (@lem1483484 (term40 x) y (term40 z)). Qed.
Lemma lem1514374 (x : real) (y : real) (z : real) : (term84 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem1514368 y x z) (@lem1514373 x y z)). Qed.
Lemma lem1514376 (x : real) (y : real) (z : real) : (term83 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem1514359 y x z) (@lem1514374 x y z)). Qed.
Lemma lem1514377 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514378 (x : real) (y : real) (z : real) : (term88 y x z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1514377) (@lem1514376 x y z)). Qed.
Lemma lem1514379 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514380 (x : real) (y : real) (z : real) : (term82 y x z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1514378 x y z) (@lem1514379)). Qed.
Lemma lem1514381 (x : real) (y : real) (z : real) : (term3 x z y) = (term44 x y z).
Proof. exact (TRANS (@lem1514347 y x z) (@lem1514380 x y z)). Qed.
Lemma lem1514382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1514383 (x : real) (y : real) (z : real) : (term89 x y z) = (term90 x y z).
Proof. exact (MK_COMB (@lem1514382) (@lem1514346 x y z)). Qed.
Lemma lem1514384 (x : real) (y : real) (z : real) : (term91 x z y) = (term92 x y z).
Proof. exact (MK_COMB (@lem1514383 x y z) (@lem1514381 x y z)). Qed.
Lemma lem1514385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514386 (x : real) (y : real) (z : real) : (term93 x z y) = (term94 x y z).
Proof. exact (MK_COMB (@lem1514385) (@lem1514294 x y z)). Qed.
Lemma lem1514387 (x : real) (y : real) (z : real) : (term1 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1514386 x y z) (@lem1514384 x y z)). Qed.
Lemma lem1514388 (x : real) (y : real) : (term12 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1514387 x y z)). Qed.
Lemma lem1514389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514390 (x : real) (y : real) : (term13 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1514389) (@lem1514388 x y)). Qed.
Lemma lem1514391 (x : real) : (term21 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1514390 x y)). Qed.
Lemma lem1514392 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514393 (x : real) : (term22 x) = (term99 x).
Proof. exact (MK_COMB (@lem1514392) (@lem1514391 x)). Qed.
Lemma lem1514394 : term30 = term100.
Proof. exact (fun_ext (fun x : real => @lem1514393 x)). Qed.
Lemma lem1514395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514396 : term31 = term101.
Proof. exact (MK_COMB (@lem1514395) (@lem1514394)). Qed.
Lemma lem1514397 : term23 = term101.
Proof. exact (TRANS (@lem1514231) (@lem1514396)). Qed.
Lemma lem1514407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1514408 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1514407 real P Q). Qed.
Lemma lem1514409 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1514408 (term108 x y) (term109 x y)). Qed.
Lemma lem1514410 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1514411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514412 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1514411) (@lem1514410 x y z)). Qed.
Lemma lem1514413 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1514414 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1514412 x y z) (@lem1514413 x y z)). Qed.
Lemma lem1514415 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1514414 x y z)). Qed.
Lemma lem1514416 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514417 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1514416) (@lem1514415 x y)). Qed.
Lemma lem1514418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514419 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1514418) (@lem1514417 x y)). Qed.
Lemma lem1514420 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1514421 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1514420 x y z)). Qed.
Lemma lem1514422 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514423 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1514422) (@lem1514421 x y)). Qed.
Lemma lem1514424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514425 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1514424) (@lem1514423 x y)). Qed.
Lemma lem1514426 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1514427 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1514426 x y z)). Qed.
Lemma lem1514428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514429 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1514428) (@lem1514427 x y)). Qed.
Lemma lem1514430 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1514425 x y) (@lem1514429 x y)). Qed.
Lemma lem1514431 (x : real) (y : real) : ((term106 x y) = (term107 x y)) = ((term97 x y) = (term125 x y)).
Proof. exact (MK_COMB (@lem1514419 x y) (@lem1514430 x y)). Qed.
Lemma lem1514432 (x : real) (y : real) : (term97 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1514431 x y) (@lem1514409 x y)). Qed.
Lemma lem1514529 (x : real) : (term98 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1514432 x y)). Qed.
Lemma lem1514530 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514531 (x : real) : (term99 x) = (term127 x).
Proof. exact (MK_COMB (@lem1514530) (@lem1514529 x)). Qed.
Lemma lem1514533 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1514534 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1514533 real P Q). Qed.
Lemma lem1514535 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1514534 (term130 x) (term131 x)). Qed.
Lemma lem1514536 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1514537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514538 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1514537) (@lem1514536 x y)). Qed.
Lemma lem1514539 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1514540 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1514538 x y) (@lem1514539 x y)). Qed.
Lemma lem1514541 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1514540 x y)). Qed.
Lemma lem1514542 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514543 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1514542) (@lem1514541 x)). Qed.
Lemma lem1514544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514545 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1514544) (@lem1514543 x)). Qed.
Lemma lem1514546 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1514547 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1514546 x y)). Qed.
Lemma lem1514548 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514549 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1514548) (@lem1514547 x)). Qed.
Lemma lem1514550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514551 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1514550) (@lem1514549 x)). Qed.
Lemma lem1514552 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1514553 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1514552 x y)). Qed.
Lemma lem1514554 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514555 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1514554) (@lem1514553 x)). Qed.
Lemma lem1514556 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1514551 x) (@lem1514555 x)). Qed.
Lemma lem1514557 (x : real) : ((term128 x) = (term129 x)) = ((term127 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1514545 x) (@lem1514556 x)). Qed.
Lemma lem1514558 (x : real) : (term127 x) = (term147 x).
Proof. exact (EQ_MP (@lem1514557 x) (@lem1514535 x)). Qed.
Lemma lem1514663 (x : real) : (term99 x) = (term147 x).
Proof. exact (TRANS (@lem1514531 x) (@lem1514558 x)). Qed.
Lemma lem1514664 : term100 = term148.
Proof. exact (fun_ext (fun x : real => @lem1514663 x)). Qed.
Lemma lem1514665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514666 : term101 = term149.
Proof. exact (MK_COMB (@lem1514665) (@lem1514664)). Qed.
Lemma lem1514668 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1514669 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1514668 real P Q). Qed.
Lemma lem1514670 : term150 = term151.
Proof. exact (@lem1514669 term152 term153). Qed.
Lemma lem1514671 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1514672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514673 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1514672) (@lem1514671 x)). Qed.
Lemma lem1514674 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1514675 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1514673 x) (@lem1514674 x)). Qed.
Lemma lem1514676 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1514675 x)). Qed.
Lemma lem1514677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514678 : term150 = term149.
Proof. exact (MK_COMB (@lem1514677) (@lem1514676)). Qed.
Lemma lem1514679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514680 : term159 = term160.
Proof. exact (MK_COMB (@lem1514679) (@lem1514678)). Qed.
Lemma lem1514681 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1514682 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1514681 x)). Qed.
Lemma lem1514683 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514684 : term162 = term163.
Proof. exact (MK_COMB (@lem1514683) (@lem1514682)). Qed.
Lemma lem1514685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514686 : term164 = term165.
Proof. exact (MK_COMB (@lem1514685) (@lem1514684)). Qed.
Lemma lem1514687 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1514688 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1514687 x)). Qed.
Lemma lem1514689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514690 : term167 = term168.
Proof. exact (MK_COMB (@lem1514689) (@lem1514688)). Qed.
Lemma lem1514691 : term151 = term169.
Proof. exact (MK_COMB (@lem1514686) (@lem1514690)). Qed.
Lemma lem1514692 : (term150 = term151) = (term149 = term169).
Proof. exact (MK_COMB (@lem1514680) (@lem1514691)). Qed.
Lemma lem1514693 : term149 = term169.
Proof. exact (EQ_MP (@lem1514692) (@lem1514670)). Qed.
Lemma lem1514806 : term101 = term169.
Proof. exact (TRANS (@lem1514666) (@lem1514693)). Qed.
Lemma lem1514808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1514809 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1514808 real P Q). Qed.
Lemma lem1514810 : term151 = term150.
Proof. exact (@lem1514809 term152 term153). Qed.
Lemma lem1514811 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1514812 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1514811 x)). Qed.
Lemma lem1514813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514814 : term162 = term163.
Proof. exact (MK_COMB (@lem1514813) (@lem1514812)). Qed.
Lemma lem1514815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514816 : term164 = term165.
Proof. exact (MK_COMB (@lem1514815) (@lem1514814)). Qed.
Lemma lem1514817 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1514818 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1514817 x)). Qed.
Lemma lem1514819 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514820 : term167 = term168.
Proof. exact (MK_COMB (@lem1514819) (@lem1514818)). Qed.
Lemma lem1514821 : term151 = term169.
Proof. exact (MK_COMB (@lem1514816) (@lem1514820)). Qed.
Lemma lem1514822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514823 : term170 = term171.
Proof. exact (MK_COMB (@lem1514822) (@lem1514821)). Qed.
Lemma lem1514824 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1514825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514826 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1514825) (@lem1514824 x)). Qed.
Lemma lem1514827 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1514828 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1514826 x) (@lem1514827 x)). Qed.
Lemma lem1514829 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1514828 x)). Qed.
Lemma lem1514830 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514831 : term150 = term149.
Proof. exact (MK_COMB (@lem1514830) (@lem1514829)). Qed.
Lemma lem1514832 : (term151 = term150) = (term169 = term149).
Proof. exact (MK_COMB (@lem1514823) (@lem1514831)). Qed.
Lemma lem1514833 : term169 = term149.
Proof. exact (EQ_MP (@lem1514832) (@lem1514810)). Qed.
Lemma lem1514835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1514836 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1514835 real P Q). Qed.
Lemma lem1514837 (x : real) : (term129 x) = (term128 x).
Proof. exact (@lem1514836 (term130 x) (term131 x)). Qed.
Lemma lem1514838 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1514839 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1514838 x y)). Qed.
Lemma lem1514840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514841 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1514840) (@lem1514839 x)). Qed.
Lemma lem1514842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514843 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1514842) (@lem1514841 x)). Qed.
Lemma lem1514844 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1514845 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1514844 x y)). Qed.
Lemma lem1514846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514847 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1514846) (@lem1514845 x)). Qed.
Lemma lem1514848 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1514843 x) (@lem1514847 x)). Qed.
Lemma lem1514849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514850 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1514849) (@lem1514848 x)). Qed.
Lemma lem1514851 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1514852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514853 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1514852) (@lem1514851 x y)). Qed.
Lemma lem1514854 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1514855 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1514853 x y) (@lem1514854 x y)). Qed.
Lemma lem1514856 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1514855 x y)). Qed.
Lemma lem1514857 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514858 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1514857) (@lem1514856 x)). Qed.
Lemma lem1514859 (x : real) : ((term129 x) = (term128 x)) = ((term147 x) = (term127 x)).
Proof. exact (MK_COMB (@lem1514850 x) (@lem1514858 x)). Qed.
Lemma lem1514860 (x : real) : (term147 x) = (term127 x).
Proof. exact (EQ_MP (@lem1514859 x) (@lem1514837 x)). Qed.
Lemma lem1514862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1514863 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1514862 real P Q). Qed.
Lemma lem1514864 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1514863 (term108 x y) (term109 x y)). Qed.
Lemma lem1514865 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1514866 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1514865 x y z)). Qed.
Lemma lem1514867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514868 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1514867) (@lem1514866 x y)). Qed.
Lemma lem1514869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514870 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1514869) (@lem1514868 x y)). Qed.
Lemma lem1514871 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1514872 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1514871 x y z)). Qed.
Lemma lem1514873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514874 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1514873) (@lem1514872 x y)). Qed.
Lemma lem1514875 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1514870 x y) (@lem1514874 x y)). Qed.
Lemma lem1514876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1514877 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1514876) (@lem1514875 x y)). Qed.
Lemma lem1514878 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1514879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1514880 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1514879) (@lem1514878 x y z)). Qed.
Lemma lem1514881 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1514882 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1514880 x y z) (@lem1514881 x y z)). Qed.
Lemma lem1514883 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1514882 x y z)). Qed.
Lemma lem1514884 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514885 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1514884) (@lem1514883 x y)). Qed.
Lemma lem1514886 (x : real) (y : real) : ((term107 x y) = (term106 x y)) = ((term125 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1514877 x y) (@lem1514885 x y)). Qed.
Lemma lem1514887 (x : real) (y : real) : (term125 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1514886 x y) (@lem1514864 x y)). Qed.
Lemma lem1514888 (x : real) : (term126 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1514887 x y)). Qed.
Lemma lem1514889 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514890 (x : real) : (term127 x) = (term99 x).
Proof. exact (MK_COMB (@lem1514889) (@lem1514888 x)). Qed.
Lemma lem1514891 (x : real) : (term147 x) = (term99 x).
Proof. exact (TRANS (@lem1514860 x) (@lem1514890 x)). Qed.
Lemma lem1514892 : term148 = term100.
Proof. exact (fun_ext (fun x : real => @lem1514891 x)). Qed.
Lemma lem1514893 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514894 : term149 = term101.
Proof. exact (MK_COMB (@lem1514893) (@lem1514892)). Qed.
Lemma lem1514895 : term169 = term101.
Proof. exact (TRANS (@lem1514833) (@lem1514894)). Qed.
Lemma lem1514896 : term101 = term101.
Proof. exact (TRANS (@lem1514806) (@lem1514895)). Qed.
Lemma lem1514899 : term23 = term101.
Proof. exact (TRANS (@lem1514397) (@lem1514896)). Qed.
Lemma lem1514916 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1514917 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1514916 x y z)). Qed.
Lemma lem1514918 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514919 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1514918) (@lem1514917 x y)). Qed.
Lemma lem1514920 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1514919 x y)). Qed.
Lemma lem1514921 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514922 (x : real) : (term99 x) = (term99 x).
Proof. exact (MK_COMB (@lem1514921) (@lem1514920 x)). Qed.
Lemma lem1514923 : term100 = term100.
Proof. exact (fun_ext (fun x : real => @lem1514922 x)). Qed.
Lemma lem1514924 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1514925 : term101 = term101.
Proof. exact (MK_COMB (@lem1514924) (@lem1514923)). Qed.
Lemma lem1514926 : term23 = term101.
Proof. exact (TRANS (@lem1514899) (@lem1514925)). Qed.
Lemma lem1514936 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1514937 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term58 x y z.
Proof. exact (h1). Qed.
Lemma lem1514938 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (proj2 (@lem1514937 x y z h1)). Qed.
Lemma lem1514939 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term44 x y z.
Proof. exact (proj1 (@lem1514937 x y z h1)). Qed.
Lemma lem1514941 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514942 : term177 = term178.
Proof. exact (@lem1514941 (NUMERAL 0) term73). Qed.
Lemma lem1514943 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1514944 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1514945 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1514944 h1) (fun h1 : term178 = True => @lem1514943)). Qed.
Lemma lem1514946 : term178 = True.
Proof. exact (EQ_MP (@lem1514945) (@lem1514943)). Qed.
Lemma lem1514947 : term177 = True.
Proof. exact (TRANS (@lem1514942) (@lem1514946)). Qed.
Lemma lem1514948 : True = term177.
Proof. exact (SYM (@lem1514947)). Qed.
Lemma lem1514949 : term177.
Proof. exact (EQ_MP (@lem1514948) (@lem0)). Qed.
Lemma lem1514950 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term180 x y z.
Proof. exact (conj (@lem1514949) (@lem1514938 x y z h1)). Qed.
Lemma lem1514952 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1514953 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1514952 term76 (term51 x y z)). Qed.
Lemma lem1514954 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term183 x y z.
Proof. exact (@lem1514953 x y z (@lem1514950 x y z h1)). Qed.
Lemma lem1514955 (x : real) (y : real) (z : real) : (term184 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1514956 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1514957 (x : real) (y : real) (z : real) : (term185 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1514956) (@lem1514955 x y z)). Qed.
Lemma lem1514958 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514959 (x : real) (y : real) (z : real) : (term183 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1514957 x y z) (@lem1514958)). Qed.
Lemma lem1514960 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1514959 x y z) (@lem1514954 x y z h1)). Qed.
Lemma lem1514962 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514963 : term177 = term178.
Proof. exact (@lem1514962 (NUMERAL 0) term73). Qed.
Lemma lem1514964 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1514965 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1514966 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1514965 h1) (fun h1 : term178 = True => @lem1514964)). Qed.
Lemma lem1514967 : term178 = True.
Proof. exact (EQ_MP (@lem1514966) (@lem1514964)). Qed.
Lemma lem1514968 : term177 = True.
Proof. exact (TRANS (@lem1514963) (@lem1514967)). Qed.
Lemma lem1514969 : True = term177.
Proof. exact (SYM (@lem1514968)). Qed.
Lemma lem1514970 : term177.
Proof. exact (EQ_MP (@lem1514969) (@lem0)). Qed.
Lemma lem1514971 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term186 x y z.
Proof. exact (conj (@lem1514970) (@lem1514939 x y z h1)). Qed.
Lemma lem1514973 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1514974 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1514973 term76 (term39 x y z)). Qed.
Lemma lem1514975 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term189 x y z.
Proof. exact (@lem1514974 x y z (@lem1514971 x y z h1)). Qed.
Lemma lem1514976 (x : real) (y : real) (z : real) : (term190 x y z) = (term39 x y z).
Proof. exact (@lem1483460 (term39 x y z)). Qed.
Lemma lem1514977 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514978 (x : real) (y : real) (z : real) : (term191 x y z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1514977) (@lem1514976 x y z)). Qed.
Lemma lem1514979 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1514980 (x : real) (y : real) (z : real) : (term189 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1514978 x y z) (@lem1514979)). Qed.
Lemma lem1514981 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term44 x y z.
Proof. exact (EQ_MP (@lem1514980 x y z) (@lem1514975 x y z h1)). Qed.
Lemma lem1514982 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term58 x y z.
Proof. exact (conj (@lem1514981 x y z h1) (@lem1514960 x y z h1)). Qed.
Lemma lem1514984 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1514985 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1514984 (term39 x y z) (term51 x y z)). Qed.
Lemma lem1514986 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term194 x y z.
Proof. exact (@lem1514985 x y z (@lem1514982 x y z h1)). Qed.
Lemma lem1514987 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 (term40 x) x (term33 y z) (term50 y z)). Qed.
Lemma lem1514988 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483440 term66 x). Qed.
Lemma lem1514990 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1514991 : term200 = term43.
Proof. exact (@lem1514990 term73). Qed.
Lemma lem1514992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1514993 : term201 = term202.
Proof. exact (MK_COMB (@lem1514992) (@lem1514991)). Qed.
Lemma lem1514994 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1514995 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1514993) (@lem1514994 x)). Qed.
Lemma lem1514996 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1514988 x) (@lem1514995 x)). Qed.
Lemma lem1514997 (x : real) : (term203 x) = term43.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1514998 (x : real) : (term197 x) = term43.
Proof. exact (TRANS (@lem1514996 x) (@lem1514997 x)). Qed.
Lemma lem1514999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1515000 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1514999) (@lem1514998 x)). Qed.
Lemma lem1515001 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 y (term40 y) (term40 z) z). Qed.
Lemma lem1515002 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483442 term66 y). Qed.
Lemma lem1515004 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1515005 : term200 = term43.
Proof. exact (@lem1515004 term73). Qed.
Lemma lem1515006 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515007 : term201 = term202.
Proof. exact (MK_COMB (@lem1515006) (@lem1515005)). Qed.
Lemma lem1515008 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1515009 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1515007) (@lem1515008 y)). Qed.
Lemma lem1515010 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1515002 y) (@lem1515009 y)). Qed.
Lemma lem1515011 (y : real) : (term203 y) = term43.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1515012 (y : real) : (term208 y) = term43.
Proof. exact (TRANS (@lem1515010 y) (@lem1515011 y)). Qed.
Lemma lem1515013 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1515014 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1515013) (@lem1515012 y)). Qed.
Lemma lem1515015 (z : real) : (term197 z) = (term198 z).
Proof. exact (@lem1483440 term66 z). Qed.
Lemma lem1515017 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1515018 : term200 = term43.
Proof. exact (@lem1515017 term73). Qed.
Lemma lem1515019 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515020 : term201 = term202.
Proof. exact (MK_COMB (@lem1515019) (@lem1515018)). Qed.
Lemma lem1515021 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1515022 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1515020) (@lem1515021 z)). Qed.
Lemma lem1515023 (z : real) : (term197 z) = (term203 z).
Proof. exact (TRANS (@lem1515015 z) (@lem1515022 z)). Qed.
Lemma lem1515024 (z : real) : (term203 z) = term43.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1515025 (z : real) : (term197 z) = term43.
Proof. exact (TRANS (@lem1515023 z) (@lem1515024 z)). Qed.
Lemma lem1515026 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1515014 y) (@lem1515025 z)). Qed.
Lemma lem1515027 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1515001 y z) (@lem1515026 y z)). Qed.
Lemma lem1515028 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1515029 (y : real) (z : real) : (term206 y z) = term43.
Proof. exact (TRANS (@lem1515027 y z) (@lem1515028)). Qed.
Lemma lem1515030 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1515000 x) (@lem1515029 y z)). Qed.
Lemma lem1515031 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1514987 x y z) (@lem1515030 x y z)). Qed.
Lemma lem1515032 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1515033 (x : real) (y : real) (z : real) : (term195 x y z) = term43.
Proof. exact (TRANS (@lem1515031 x y z) (@lem1515032)). Qed.
Lemma lem1515034 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1515035 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1515034) (@lem1515033 x y z)). Qed.
Lemma lem1515036 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515037 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1515035 x y z) (@lem1515036)). Qed.
Lemma lem1515038 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term213.
Proof. exact (EQ_MP (@lem1515037 x y z) (@lem1514986 x y z h1)). Qed.
Lemma lem1515040 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515041 : term213 = term214.
Proof. exact (@lem1515040 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1515042 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1515043 : term213 = False.
Proof. exact (TRANS (@lem1515041) (@lem1515042)). Qed.
Lemma lem1515044 (x : real) (y : real) (z : real) (h1 : term58 x y z) : False.
Proof. exact (EQ_MP (@lem1515043) (@lem1515038 x y z h1)). Qed.
Lemma lem1515045 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (h1). Qed.
Lemma lem1515046 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term44 x y z.
Proof. exact (proj2 (@lem1515045 x y z h1)). Qed.
Lemma lem1515047 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (proj1 (@lem1515045 x y z h1)). Qed.
Lemma lem1515049 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515050 : term177 = term178.
Proof. exact (@lem1515049 (NUMERAL 0) term73). Qed.
Lemma lem1515051 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1515052 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1515053 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1515052 h1) (fun h1 : term178 = True => @lem1515051)). Qed.
Lemma lem1515054 : term178 = True.
Proof. exact (EQ_MP (@lem1515053) (@lem1515051)). Qed.
Lemma lem1515055 : term177 = True.
Proof. exact (TRANS (@lem1515050) (@lem1515054)). Qed.
Lemma lem1515056 : True = term177.
Proof. exact (SYM (@lem1515055)). Qed.
Lemma lem1515057 : term177.
Proof. exact (EQ_MP (@lem1515056) (@lem0)). Qed.
Lemma lem1515058 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term180 x y z.
Proof. exact (conj (@lem1515057) (@lem1515047 x y z h1)). Qed.
Lemma lem1515060 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1515061 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1515060 term76 (term51 x y z)). Qed.
Lemma lem1515062 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term183 x y z.
Proof. exact (@lem1515061 x y z (@lem1515058 x y z h1)). Qed.
Lemma lem1515063 (x : real) (y : real) (z : real) : (term184 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1515064 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1515065 (x : real) (y : real) (z : real) : (term185 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1515064) (@lem1515063 x y z)). Qed.
Lemma lem1515066 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515067 (x : real) (y : real) (z : real) : (term183 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1515065 x y z) (@lem1515066)). Qed.
Lemma lem1515068 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1515067 x y z) (@lem1515062 x y z h1)). Qed.
Lemma lem1515070 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515071 : term177 = term178.
Proof. exact (@lem1515070 (NUMERAL 0) term73). Qed.
Lemma lem1515072 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1515073 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1515074 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1515073 h1) (fun h1 : term178 = True => @lem1515072)). Qed.
Lemma lem1515075 : term178 = True.
Proof. exact (EQ_MP (@lem1515074) (@lem1515072)). Qed.
Lemma lem1515076 : term177 = True.
Proof. exact (TRANS (@lem1515071) (@lem1515075)). Qed.
Lemma lem1515077 : True = term177.
Proof. exact (SYM (@lem1515076)). Qed.
Lemma lem1515078 : term177.
Proof. exact (EQ_MP (@lem1515077) (@lem0)). Qed.
Lemma lem1515079 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term186 x y z.
Proof. exact (conj (@lem1515078) (@lem1515046 x y z h1)). Qed.
Lemma lem1515081 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1515082 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1515081 term76 (term39 x y z)). Qed.
Lemma lem1515083 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term189 x y z.
Proof. exact (@lem1515082 x y z (@lem1515079 x y z h1)). Qed.
Lemma lem1515084 (x : real) (y : real) (z : real) : (term190 x y z) = (term39 x y z).
Proof. exact (@lem1483460 (term39 x y z)). Qed.
Lemma lem1515085 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1515086 (x : real) (y : real) (z : real) : (term191 x y z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1515085) (@lem1515084 x y z)). Qed.
Lemma lem1515087 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515088 (x : real) (y : real) (z : real) : (term189 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1515086 x y z) (@lem1515087)). Qed.
Lemma lem1515089 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term44 x y z.
Proof. exact (EQ_MP (@lem1515088 x y z) (@lem1515083 x y z h1)). Qed.
Lemma lem1515090 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term58 x y z.
Proof. exact (conj (@lem1515089 x y z h1) (@lem1515068 x y z h1)). Qed.
Lemma lem1515092 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1515093 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1515092 (term39 x y z) (term51 x y z)). Qed.
Lemma lem1515094 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term194 x y z.
Proof. exact (@lem1515093 x y z (@lem1515090 x y z h1)). Qed.
Lemma lem1515095 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 (term40 x) x (term33 y z) (term50 y z)). Qed.
Lemma lem1515096 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483440 term66 x). Qed.
Lemma lem1515098 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1515099 : term200 = term43.
Proof. exact (@lem1515098 term73). Qed.
Lemma lem1515100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515101 : term201 = term202.
Proof. exact (MK_COMB (@lem1515100) (@lem1515099)). Qed.
Lemma lem1515102 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1515103 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1515101) (@lem1515102 x)). Qed.
Lemma lem1515104 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1515096 x) (@lem1515103 x)). Qed.
Lemma lem1515105 (x : real) : (term203 x) = term43.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1515106 (x : real) : (term197 x) = term43.
Proof. exact (TRANS (@lem1515104 x) (@lem1515105 x)). Qed.
Lemma lem1515107 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1515108 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1515107) (@lem1515106 x)). Qed.
Lemma lem1515109 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 y (term40 y) (term40 z) z). Qed.
Lemma lem1515110 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483442 term66 y). Qed.
Lemma lem1515112 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1515113 : term200 = term43.
Proof. exact (@lem1515112 term73). Qed.
Lemma lem1515114 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515115 : term201 = term202.
Proof. exact (MK_COMB (@lem1515114) (@lem1515113)). Qed.
Lemma lem1515116 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1515117 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1515115) (@lem1515116 y)). Qed.
Lemma lem1515118 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1515110 y) (@lem1515117 y)). Qed.
Lemma lem1515119 (y : real) : (term203 y) = term43.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1515120 (y : real) : (term208 y) = term43.
Proof. exact (TRANS (@lem1515118 y) (@lem1515119 y)). Qed.
Lemma lem1515121 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1515122 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1515121) (@lem1515120 y)). Qed.
Lemma lem1515123 (z : real) : (term197 z) = (term198 z).
Proof. exact (@lem1483440 term66 z). Qed.
Lemma lem1515125 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1515126 : term200 = term43.
Proof. exact (@lem1515125 term73). Qed.
Lemma lem1515127 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515128 : term201 = term202.
Proof. exact (MK_COMB (@lem1515127) (@lem1515126)). Qed.
Lemma lem1515129 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1515130 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1515128) (@lem1515129 z)). Qed.
Lemma lem1515131 (z : real) : (term197 z) = (term203 z).
Proof. exact (TRANS (@lem1515123 z) (@lem1515130 z)). Qed.
Lemma lem1515132 (z : real) : (term203 z) = term43.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1515133 (z : real) : (term197 z) = term43.
Proof. exact (TRANS (@lem1515131 z) (@lem1515132 z)). Qed.
Lemma lem1515134 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1515122 y) (@lem1515133 z)). Qed.
Lemma lem1515135 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1515109 y z) (@lem1515134 y z)). Qed.
Lemma lem1515136 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1515137 (y : real) (z : real) : (term206 y z) = term43.
Proof. exact (TRANS (@lem1515135 y z) (@lem1515136)). Qed.
Lemma lem1515138 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1515108 x) (@lem1515137 y z)). Qed.
Lemma lem1515139 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1515095 x y z) (@lem1515138 x y z)). Qed.
Lemma lem1515140 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1515141 (x : real) (y : real) (z : real) : (term195 x y z) = term43.
Proof. exact (TRANS (@lem1515139 x y z) (@lem1515140)). Qed.
Lemma lem1515142 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1515143 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1515142) (@lem1515141 x y z)). Qed.
Lemma lem1515144 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515145 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1515143 x y z) (@lem1515144)). Qed.
Lemma lem1515146 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term213.
Proof. exact (EQ_MP (@lem1515145 x y z) (@lem1515094 x y z h1)). Qed.
Lemma lem1515148 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515149 : term213 = term214.
Proof. exact (@lem1515148 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1515150 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1515151 : term213 = False.
Proof. exact (TRANS (@lem1515149) (@lem1515150)). Qed.
Lemma lem1515152 (x : real) (y : real) (z : real) (h1 : term92 x y z) : False.
Proof. exact (EQ_MP (@lem1515151) (@lem1515146 x y z h1)). Qed.
Lemma lem1515153 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (or_elim (@lem1514936 x y z h1) (fun h0 : term58 x y z => @lem1515044 x y z h0) (fun h0 : term92 x y z => @lem1515152 x y z h0)). Qed.
Lemma lem1515155 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1515156 (x : real) (y : real) (z : real) (h1 : term95 x y z) : (term95 x y z) = False.
Proof. exact (prop_ext (fun h2 : term95 x y z => @lem1515153 x y z h1) (fun h2 : False => @lem1515155 x y z h1)). Qed.
Lemma lem1515157 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (EQ_MP (@lem1515156 x y z h1) (@lem1515155 x y z h1)). Qed.
Lemma lem1515158 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1515159 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (ex_elim (@lem1515158 x y h1) (fun z : real => fun h0 : term96 x y z => @lem1515157 x y z h0)). Qed.
Lemma lem1515160 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1515161 (x : real) (h1 : term99 x) : False.
Proof. exact (ex_elim (@lem1515160 x h1) (fun y : real => fun h0 : term98 x y => @lem1515159 x y h0)). Qed.
Lemma lem1515162 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1515163 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1515162 h1) (fun x : real => fun h0 : term100 x => @lem1515161 x h0)). Qed.
Lemma lem1515164 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1515165 (h1 : term23) : term101.
Proof. exact (EQ_MP (@lem1514926) (@lem1515164 h1)). Qed.
Lemma lem1515166 (h1 : term23) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1515163 h2) (fun h2 : False => @lem1515165 h1)). Qed.
Lemma lem1515167 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1515166 h1) (@lem1515165 h1)). Qed.
Lemma lem1515168 : term215.
Proof. exact (fun h0 : term23 => @lem1515167 h0). Qed.
Lemma lem1515169 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1515170 : term217.
Proof. exact (@lem1515169 (@lem1515168)). Qed.
