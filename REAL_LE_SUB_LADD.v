Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SUB_LADD_term_abbrevs.
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
Require Import thm1483523_spec.
Require Import thm1483533_spec.
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
Lemma lem1515200 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1515201 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1515202 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1515201 (term8 x y)). Qed.
Lemma lem1515203 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1515204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1515205 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1515204) (@lem1515203 x z y)). Qed.
Lemma lem1515206 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1515205 x z y) (@lem1515200 x z y)). Qed.
Lemma lem1515207 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1515206 x z y)). Qed.
Lemma lem1515208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515209 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1515208) (@lem1515207 x y)). Qed.
Lemma lem1515210 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1515202 x y) (@lem1515209 x y)). Qed.
Lemma lem1515211 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1515212 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1515211 (term16 x)). Qed.
Lemma lem1515213 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1515214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1515215 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1515214) (@lem1515213 x y)). Qed.
Lemma lem1515216 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1515215 x y) (@lem1515210 x y)). Qed.
Lemma lem1515217 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1515216 x y)). Qed.
Lemma lem1515218 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515219 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1515218) (@lem1515217 x)). Qed.
Lemma lem1515220 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1515212 x) (@lem1515219 x)). Qed.
Lemma lem1515221 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1515222 : term23 = term24.
Proof. exact (@lem1515221 term25). Qed.
Lemma lem1515223 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1515224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1515225 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1515224) (@lem1515223 x)). Qed.
Lemma lem1515226 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1515225 x) (@lem1515220 x)). Qed.
Lemma lem1515227 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1515226 x)). Qed.
Lemma lem1515228 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515229 : term24 = term31.
Proof. exact (MK_COMB (@lem1515228) (@lem1515227)). Qed.
Lemma lem1515231 : term23 = term31.
Proof. exact (TRANS (@lem1515222) (@lem1515229)). Qed.
Lemma lem1515248 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1515249 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1515248 x z y)). Qed.
Lemma lem1515250 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515251 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1515250) (@lem1515249 x y)). Qed.
Lemma lem1515252 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1515251 x y)). Qed.
Lemma lem1515253 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515254 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1515253) (@lem1515252 x)). Qed.
Lemma lem1515255 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1515254 x)). Qed.
Lemma lem1515256 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515257 : term31 = term31.
Proof. exact (MK_COMB (@lem1515256) (@lem1515255)). Qed.
Lemma lem1515258 : term23 = term31.
Proof. exact (TRANS (@lem1515231) (@lem1515257)). Qed.
Lemma lem1515259 (y : real) (z : real) (x : real) : (term2 x y z) = (term32 y z x).
Proof. exact (@lem1483523 (real_sub y z) x). Qed.
Lemma lem1515260 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1515273 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1515274 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1515275 (y : real) (z : real) : (term34 y z) = (term35 y z).
Proof. exact (MK_COMB (@lem1515274) (@lem1515273 y z)). Qed.
Lemma lem1515276 (y : real) (z : real) (x : real) : (term36 y z x) = (term37 y z x).
Proof. exact (MK_COMB (@lem1515275 y z) (@lem1515260 x)). Qed.
Lemma lem1515277 (y : real) (z : real) (x : real) : (term37 y z x) = (term38 y z x).
Proof. exact (@lem1483519 (term33 y z) x). Qed.
Lemma lem1515282 (x : real) (y : real) (z : real) : (term38 y z x) = (term39 x y z).
Proof. exact (@lem1483488 (term40 x) (term33 y z)). Qed.
Lemma lem1515283 (x : real) (y : real) (z : real) : (term37 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem1515277 y z x) (@lem1515282 x y z)). Qed.
Lemma lem1515284 (x : real) (y : real) (z : real) : (term36 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem1515276 y z x) (@lem1515283 x y z)). Qed.
Lemma lem1515285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1515286 (x : real) (y : real) (z : real) : (term41 y z x) = (term42 x y z).
Proof. exact (MK_COMB (@lem1515285) (@lem1515284 x y z)). Qed.
Lemma lem1515287 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515288 (x : real) (y : real) (z : real) : (term32 y z x) = (term44 x y z).
Proof. exact (MK_COMB (@lem1515286 x y z) (@lem1515287)). Qed.
Lemma lem1515289 (x : real) (y : real) (z : real) : (term2 x y z) = (term44 x y z).
Proof. exact (TRANS (@lem1515259 y z x) (@lem1515288 x y z)). Qed.
Lemma lem1515290 (x : real) (z : real) (y : real) : (term45 x z y) = (term46 x z y).
Proof. exact (@lem1483533 (real_add x z) y). Qed.
Lemma lem1515302 (x : real) (z : real) (y : real) : (term47 x z y) = (term48 x z y).
Proof. exact (@lem1483519 (real_add x z) y). Qed.
Lemma lem1515306 (x : real) (z : real) (y : real) : (term48 x z y) = (term49 x z y).
Proof. exact (@lem1483482 x z (term40 y)). Qed.
Lemma lem1515307 (y : real) (z : real) : (term33 z y) = (term50 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1515308 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1515309 (x : real) (y : real) (z : real) : (term49 x z y) = (term51 x y z).
Proof. exact (MK_COMB (@lem1515308 x) (@lem1515307 y z)). Qed.
Lemma lem1515311 (x : real) (y : real) (z : real) : (term48 x z y) = (term51 x y z).
Proof. exact (TRANS (@lem1515306 x z y) (@lem1515309 x y z)). Qed.
Lemma lem1515313 (x : real) (y : real) (z : real) : (term47 x z y) = (term51 x y z).
Proof. exact (TRANS (@lem1515302 x z y) (@lem1515311 x y z)). Qed.
Lemma lem1515314 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1515315 (x : real) (y : real) (z : real) : (term52 x z y) = (term53 x y z).
Proof. exact (MK_COMB (@lem1515314) (@lem1515313 x y z)). Qed.
Lemma lem1515316 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515317 (x : real) (y : real) (z : real) : (term46 x z y) = (term54 x y z).
Proof. exact (MK_COMB (@lem1515315 x y z) (@lem1515316)). Qed.
Lemma lem1515318 (x : real) (y : real) (z : real) : (term45 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1515290 x z y) (@lem1515317 x y z)). Qed.
Lemma lem1515319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1515320 (x : real) (y : real) (z : real) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1515319) (@lem1515289 x y z)). Qed.
Lemma lem1515321 (x : real) (y : real) (z : real) : (term57 x z y) = (term58 x y z).
Proof. exact (MK_COMB (@lem1515320 x y z) (@lem1515318 x y z)). Qed.
Lemma lem1515322 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483533 x (real_sub y z)). Qed.
Lemma lem1515335 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1515338 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1515339 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1515338 x) (@lem1515335 y z)). Qed.
Lemma lem1515340 (x : real) (y : real) (z : real) : (term62 x y z) = (term63 x y z).
Proof. exact (@lem1483519 x (term33 y z)). Qed.
Lemma lem1515341 (y : real) (z : real) : (term64 y z) = (term65 y z).
Proof. exact (@lem1483508 y term66 (term40 z)). Qed.
Lemma lem1515342 (z : real) : (term67 z) = (term68 z).
Proof. exact (@lem1483476 term66 term66 z). Qed.
Lemma lem1515344 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1515345 : term71 = term72.
Proof. exact (@lem1515344 term73 term73). Qed.
Lemma lem1515346 : (term74 = (BIT1 0)) = (term75 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1515347 : term75 = term73.
Proof. exact (EQ_MP (@lem1515346) (@lem940073)). Qed.
Lemma lem1515348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1515349 : term72 = term76.
Proof. exact (MK_COMB (@lem1515348) (@lem1515347)). Qed.
Lemma lem1515350 : term71 = term76.
Proof. exact (TRANS (@lem1515345) (@lem1515349)). Qed.
Lemma lem1515351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1515352 : term77 = term78.
Proof. exact (MK_COMB (@lem1515351) (@lem1515350)). Qed.
Lemma lem1515353 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1515354 (z : real) : (term68 z) = (term79 z).
Proof. exact (MK_COMB (@lem1515352) (@lem1515353 z)). Qed.
Lemma lem1515355 (z : real) : (term67 z) = (term79 z).
Proof. exact (TRANS (@lem1515342 z) (@lem1515354 z)). Qed.
Lemma lem1515356 (z : real) : (term79 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1515357 (z : real) : (term67 z) = z.
Proof. exact (TRANS (@lem1515355 z) (@lem1515356 z)). Qed.
Lemma lem1515360 (y : real) : (term80 y) = (term80 y).
Proof. exact (eq_refl (term80 y)). Qed.
Lemma lem1515361 (y : real) (z : real) : (term65 y z) = (term50 y z).
Proof. exact (MK_COMB (@lem1515360 y) (@lem1515357 z)). Qed.
Lemma lem1515362 (y : real) (z : real) : (term64 y z) = (term50 y z).
Proof. exact (TRANS (@lem1515341 y z) (@lem1515361 y z)). Qed.
Lemma lem1515363 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1515366 (x : real) (y : real) (z : real) : (term63 x y z) = (term51 x y z).
Proof. exact (MK_COMB (@lem1515363 x) (@lem1515362 y z)). Qed.
Lemma lem1515367 (x : real) (y : real) (z : real) : (term62 x y z) = (term51 x y z).
Proof. exact (TRANS (@lem1515340 x y z) (@lem1515366 x y z)). Qed.
Lemma lem1515368 (x : real) (y : real) (z : real) : (term61 x y z) = (term51 x y z).
Proof. exact (TRANS (@lem1515339 x y z) (@lem1515367 x y z)). Qed.
Lemma lem1515369 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1515370 (x : real) (y : real) (z : real) : (term81 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1515369) (@lem1515368 x y z)). Qed.
Lemma lem1515371 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515372 (x : real) (y : real) (z : real) : (term60 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1515370 x y z) (@lem1515371)). Qed.
Lemma lem1515373 (x : real) (y : real) (z : real) : (term59 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1515322 x y z) (@lem1515372 x y z)). Qed.
Lemma lem1515374 (y : real) (x : real) (z : real) : (term3 x z y) = (term82 y x z).
Proof. exact (@lem1483523 y (real_add x z)). Qed.
Lemma lem1515386 (y : real) (x : real) (z : real) : (term83 y x z) = (term84 y x z).
Proof. exact (@lem1483519 y (real_add x z)). Qed.
Lemma lem1515393 (x : real) (z : real) : (term85 x z) = (term86 x z).
Proof. exact (@lem1483508 x term66 z). Qed.
Lemma lem1515394 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1515395 (y : real) (x : real) (z : real) : (term84 y x z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1515394 y) (@lem1515393 x z)). Qed.
Lemma lem1515400 (x : real) (y : real) (z : real) : (term87 y x z) = (term39 x y z).
Proof. exact (@lem1483484 (term40 x) y (term40 z)). Qed.
Lemma lem1515401 (x : real) (y : real) (z : real) : (term84 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem1515395 y x z) (@lem1515400 x y z)). Qed.
Lemma lem1515403 (x : real) (y : real) (z : real) : (term83 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem1515386 y x z) (@lem1515401 x y z)). Qed.
Lemma lem1515404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1515405 (x : real) (y : real) (z : real) : (term88 y x z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1515404) (@lem1515403 x y z)). Qed.
Lemma lem1515406 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515407 (x : real) (y : real) (z : real) : (term82 y x z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1515405 x y z) (@lem1515406)). Qed.
Lemma lem1515408 (x : real) (y : real) (z : real) : (term3 x z y) = (term44 x y z).
Proof. exact (TRANS (@lem1515374 y x z) (@lem1515407 x y z)). Qed.
Lemma lem1515409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1515410 (x : real) (y : real) (z : real) : (term89 x y z) = (term90 x y z).
Proof. exact (MK_COMB (@lem1515409) (@lem1515373 x y z)). Qed.
Lemma lem1515411 (x : real) (y : real) (z : real) : (term91 x z y) = (term92 x y z).
Proof. exact (MK_COMB (@lem1515410 x y z) (@lem1515408 x y z)). Qed.
Lemma lem1515412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515413 (x : real) (y : real) (z : real) : (term93 x z y) = (term94 x y z).
Proof. exact (MK_COMB (@lem1515412) (@lem1515321 x y z)). Qed.
Lemma lem1515414 (x : real) (y : real) (z : real) : (term1 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1515413 x y z) (@lem1515411 x y z)). Qed.
Lemma lem1515415 (x : real) (y : real) : (term12 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1515414 x y z)). Qed.
Lemma lem1515416 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515417 (x : real) (y : real) : (term13 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1515416) (@lem1515415 x y)). Qed.
Lemma lem1515418 (x : real) : (term21 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1515417 x y)). Qed.
Lemma lem1515419 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515420 (x : real) : (term22 x) = (term99 x).
Proof. exact (MK_COMB (@lem1515419) (@lem1515418 x)). Qed.
Lemma lem1515421 : term30 = term100.
Proof. exact (fun_ext (fun x : real => @lem1515420 x)). Qed.
Lemma lem1515422 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515423 : term31 = term101.
Proof. exact (MK_COMB (@lem1515422) (@lem1515421)). Qed.
Lemma lem1515424 : term23 = term101.
Proof. exact (TRANS (@lem1515258) (@lem1515423)). Qed.
Lemma lem1515434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1515435 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1515434 real P Q). Qed.
Lemma lem1515436 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1515435 (term108 x y) (term109 x y)). Qed.
Lemma lem1515437 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1515438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515439 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1515438) (@lem1515437 x y z)). Qed.
Lemma lem1515440 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1515441 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1515439 x y z) (@lem1515440 x y z)). Qed.
Lemma lem1515442 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1515441 x y z)). Qed.
Lemma lem1515443 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515444 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1515443) (@lem1515442 x y)). Qed.
Lemma lem1515445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515446 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1515445) (@lem1515444 x y)). Qed.
Lemma lem1515447 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1515448 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1515447 x y z)). Qed.
Lemma lem1515449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515450 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1515449) (@lem1515448 x y)). Qed.
Lemma lem1515451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515452 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1515451) (@lem1515450 x y)). Qed.
Lemma lem1515453 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1515454 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1515453 x y z)). Qed.
Lemma lem1515455 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515456 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1515455) (@lem1515454 x y)). Qed.
Lemma lem1515457 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1515452 x y) (@lem1515456 x y)). Qed.
Lemma lem1515458 (x : real) (y : real) : ((term106 x y) = (term107 x y)) = ((term97 x y) = (term125 x y)).
Proof. exact (MK_COMB (@lem1515446 x y) (@lem1515457 x y)). Qed.
Lemma lem1515459 (x : real) (y : real) : (term97 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1515458 x y) (@lem1515436 x y)). Qed.
Lemma lem1515556 (x : real) : (term98 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1515459 x y)). Qed.
Lemma lem1515557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515558 (x : real) : (term99 x) = (term127 x).
Proof. exact (MK_COMB (@lem1515557) (@lem1515556 x)). Qed.
Lemma lem1515560 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1515561 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1515560 real P Q). Qed.
Lemma lem1515562 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1515561 (term130 x) (term131 x)). Qed.
Lemma lem1515563 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1515564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515565 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1515564) (@lem1515563 x y)). Qed.
Lemma lem1515566 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1515567 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1515565 x y) (@lem1515566 x y)). Qed.
Lemma lem1515568 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1515567 x y)). Qed.
Lemma lem1515569 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515570 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1515569) (@lem1515568 x)). Qed.
Lemma lem1515571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515572 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1515571) (@lem1515570 x)). Qed.
Lemma lem1515573 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1515574 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1515573 x y)). Qed.
Lemma lem1515575 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515576 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1515575) (@lem1515574 x)). Qed.
Lemma lem1515577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515578 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1515577) (@lem1515576 x)). Qed.
Lemma lem1515579 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1515580 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1515579 x y)). Qed.
Lemma lem1515581 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515582 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1515581) (@lem1515580 x)). Qed.
Lemma lem1515583 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1515578 x) (@lem1515582 x)). Qed.
Lemma lem1515584 (x : real) : ((term128 x) = (term129 x)) = ((term127 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1515572 x) (@lem1515583 x)). Qed.
Lemma lem1515585 (x : real) : (term127 x) = (term147 x).
Proof. exact (EQ_MP (@lem1515584 x) (@lem1515562 x)). Qed.
Lemma lem1515690 (x : real) : (term99 x) = (term147 x).
Proof. exact (TRANS (@lem1515558 x) (@lem1515585 x)). Qed.
Lemma lem1515691 : term100 = term148.
Proof. exact (fun_ext (fun x : real => @lem1515690 x)). Qed.
Lemma lem1515692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515693 : term101 = term149.
Proof. exact (MK_COMB (@lem1515692) (@lem1515691)). Qed.
Lemma lem1515695 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1515696 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1515695 real P Q). Qed.
Lemma lem1515697 : term150 = term151.
Proof. exact (@lem1515696 term152 term153). Qed.
Lemma lem1515698 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1515699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515700 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1515699) (@lem1515698 x)). Qed.
Lemma lem1515701 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1515702 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1515700 x) (@lem1515701 x)). Qed.
Lemma lem1515703 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1515702 x)). Qed.
Lemma lem1515704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515705 : term150 = term149.
Proof. exact (MK_COMB (@lem1515704) (@lem1515703)). Qed.
Lemma lem1515706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515707 : term159 = term160.
Proof. exact (MK_COMB (@lem1515706) (@lem1515705)). Qed.
Lemma lem1515708 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1515709 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1515708 x)). Qed.
Lemma lem1515710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515711 : term162 = term163.
Proof. exact (MK_COMB (@lem1515710) (@lem1515709)). Qed.
Lemma lem1515712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515713 : term164 = term165.
Proof. exact (MK_COMB (@lem1515712) (@lem1515711)). Qed.
Lemma lem1515714 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1515715 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1515714 x)). Qed.
Lemma lem1515716 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515717 : term167 = term168.
Proof. exact (MK_COMB (@lem1515716) (@lem1515715)). Qed.
Lemma lem1515718 : term151 = term169.
Proof. exact (MK_COMB (@lem1515713) (@lem1515717)). Qed.
Lemma lem1515719 : (term150 = term151) = (term149 = term169).
Proof. exact (MK_COMB (@lem1515707) (@lem1515718)). Qed.
Lemma lem1515720 : term149 = term169.
Proof. exact (EQ_MP (@lem1515719) (@lem1515697)). Qed.
Lemma lem1515833 : term101 = term169.
Proof. exact (TRANS (@lem1515693) (@lem1515720)). Qed.
Lemma lem1515835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1515836 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1515835 real P Q). Qed.
Lemma lem1515837 : term151 = term150.
Proof. exact (@lem1515836 term152 term153). Qed.
Lemma lem1515838 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1515839 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1515838 x)). Qed.
Lemma lem1515840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515841 : term162 = term163.
Proof. exact (MK_COMB (@lem1515840) (@lem1515839)). Qed.
Lemma lem1515842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515843 : term164 = term165.
Proof. exact (MK_COMB (@lem1515842) (@lem1515841)). Qed.
Lemma lem1515844 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1515845 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1515844 x)). Qed.
Lemma lem1515846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515847 : term167 = term168.
Proof. exact (MK_COMB (@lem1515846) (@lem1515845)). Qed.
Lemma lem1515848 : term151 = term169.
Proof. exact (MK_COMB (@lem1515843) (@lem1515847)). Qed.
Lemma lem1515849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515850 : term170 = term171.
Proof. exact (MK_COMB (@lem1515849) (@lem1515848)). Qed.
Lemma lem1515851 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1515852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515853 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1515852) (@lem1515851 x)). Qed.
Lemma lem1515854 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1515855 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1515853 x) (@lem1515854 x)). Qed.
Lemma lem1515856 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1515855 x)). Qed.
Lemma lem1515857 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515858 : term150 = term149.
Proof. exact (MK_COMB (@lem1515857) (@lem1515856)). Qed.
Lemma lem1515859 : (term151 = term150) = (term169 = term149).
Proof. exact (MK_COMB (@lem1515850) (@lem1515858)). Qed.
Lemma lem1515860 : term169 = term149.
Proof. exact (EQ_MP (@lem1515859) (@lem1515837)). Qed.
Lemma lem1515862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1515863 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1515862 real P Q). Qed.
Lemma lem1515864 (x : real) : (term129 x) = (term128 x).
Proof. exact (@lem1515863 (term130 x) (term131 x)). Qed.
Lemma lem1515865 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1515866 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1515865 x y)). Qed.
Lemma lem1515867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515868 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1515867) (@lem1515866 x)). Qed.
Lemma lem1515869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515870 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1515869) (@lem1515868 x)). Qed.
Lemma lem1515871 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1515872 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1515871 x y)). Qed.
Lemma lem1515873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515874 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1515873) (@lem1515872 x)). Qed.
Lemma lem1515875 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1515870 x) (@lem1515874 x)). Qed.
Lemma lem1515876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515877 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1515876) (@lem1515875 x)). Qed.
Lemma lem1515878 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1515879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515880 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1515879) (@lem1515878 x y)). Qed.
Lemma lem1515881 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1515882 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1515880 x y) (@lem1515881 x y)). Qed.
Lemma lem1515883 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1515882 x y)). Qed.
Lemma lem1515884 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515885 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1515884) (@lem1515883 x)). Qed.
Lemma lem1515886 (x : real) : ((term129 x) = (term128 x)) = ((term147 x) = (term127 x)).
Proof. exact (MK_COMB (@lem1515877 x) (@lem1515885 x)). Qed.
Lemma lem1515887 (x : real) : (term147 x) = (term127 x).
Proof. exact (EQ_MP (@lem1515886 x) (@lem1515864 x)). Qed.
Lemma lem1515889 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1515890 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1515889 real P Q). Qed.
Lemma lem1515891 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1515890 (term108 x y) (term109 x y)). Qed.
Lemma lem1515892 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1515893 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1515892 x y z)). Qed.
Lemma lem1515894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515895 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1515894) (@lem1515893 x y)). Qed.
Lemma lem1515896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515897 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1515896) (@lem1515895 x y)). Qed.
Lemma lem1515898 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1515899 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1515898 x y z)). Qed.
Lemma lem1515900 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515901 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1515900) (@lem1515899 x y)). Qed.
Lemma lem1515902 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1515897 x y) (@lem1515901 x y)). Qed.
Lemma lem1515903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1515904 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1515903) (@lem1515902 x y)). Qed.
Lemma lem1515905 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1515906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1515907 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1515906) (@lem1515905 x y z)). Qed.
Lemma lem1515908 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1515909 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1515907 x y z) (@lem1515908 x y z)). Qed.
Lemma lem1515910 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1515909 x y z)). Qed.
Lemma lem1515911 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515912 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1515911) (@lem1515910 x y)). Qed.
Lemma lem1515913 (x : real) (y : real) : ((term107 x y) = (term106 x y)) = ((term125 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1515904 x y) (@lem1515912 x y)). Qed.
Lemma lem1515914 (x : real) (y : real) : (term125 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1515913 x y) (@lem1515891 x y)). Qed.
Lemma lem1515915 (x : real) : (term126 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1515914 x y)). Qed.
Lemma lem1515916 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515917 (x : real) : (term127 x) = (term99 x).
Proof. exact (MK_COMB (@lem1515916) (@lem1515915 x)). Qed.
Lemma lem1515918 (x : real) : (term147 x) = (term99 x).
Proof. exact (TRANS (@lem1515887 x) (@lem1515917 x)). Qed.
Lemma lem1515919 : term148 = term100.
Proof. exact (fun_ext (fun x : real => @lem1515918 x)). Qed.
Lemma lem1515920 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515921 : term149 = term101.
Proof. exact (MK_COMB (@lem1515920) (@lem1515919)). Qed.
Lemma lem1515922 : term169 = term101.
Proof. exact (TRANS (@lem1515860) (@lem1515921)). Qed.
Lemma lem1515923 : term101 = term101.
Proof. exact (TRANS (@lem1515833) (@lem1515922)). Qed.
Lemma lem1515926 : term23 = term101.
Proof. exact (TRANS (@lem1515424) (@lem1515923)). Qed.
Lemma lem1515943 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1515944 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1515943 x y z)). Qed.
Lemma lem1515945 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515946 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1515945) (@lem1515944 x y)). Qed.
Lemma lem1515947 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1515946 x y)). Qed.
Lemma lem1515948 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515949 (x : real) : (term99 x) = (term99 x).
Proof. exact (MK_COMB (@lem1515948) (@lem1515947 x)). Qed.
Lemma lem1515950 : term100 = term100.
Proof. exact (fun_ext (fun x : real => @lem1515949 x)). Qed.
Lemma lem1515951 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1515952 : term101 = term101.
Proof. exact (MK_COMB (@lem1515951) (@lem1515950)). Qed.
Lemma lem1515953 : term23 = term101.
Proof. exact (TRANS (@lem1515926) (@lem1515952)). Qed.
Lemma lem1515963 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1515964 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term58 x y z.
Proof. exact (h1). Qed.
Lemma lem1515965 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (proj2 (@lem1515964 x y z h1)). Qed.
Lemma lem1515966 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term44 x y z.
Proof. exact (proj1 (@lem1515964 x y z h1)). Qed.
Lemma lem1515968 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515969 : term177 = term178.
Proof. exact (@lem1515968 (NUMERAL 0) term73). Qed.
Lemma lem1515970 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1515971 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1515972 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1515971 h1) (fun h1 : term178 = True => @lem1515970)). Qed.
Lemma lem1515973 : term178 = True.
Proof. exact (EQ_MP (@lem1515972) (@lem1515970)). Qed.
Lemma lem1515974 : term177 = True.
Proof. exact (TRANS (@lem1515969) (@lem1515973)). Qed.
Lemma lem1515975 : True = term177.
Proof. exact (SYM (@lem1515974)). Qed.
Lemma lem1515976 : term177.
Proof. exact (EQ_MP (@lem1515975) (@lem0)). Qed.
Lemma lem1515977 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term180 x y z.
Proof. exact (conj (@lem1515976) (@lem1515966 x y z h1)). Qed.
Lemma lem1515979 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1515980 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1515979 term76 (term39 x y z)). Qed.
Lemma lem1515981 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term183 x y z.
Proof. exact (@lem1515980 x y z (@lem1515977 x y z h1)). Qed.
Lemma lem1515982 (x : real) (y : real) (z : real) : (term184 x y z) = (term39 x y z).
Proof. exact (@lem1483460 (term39 x y z)). Qed.
Lemma lem1515983 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1515984 (x : real) (y : real) (z : real) : (term185 x y z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1515983) (@lem1515982 x y z)). Qed.
Lemma lem1515985 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1515986 (x : real) (y : real) (z : real) : (term183 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1515984 x y z) (@lem1515985)). Qed.
Lemma lem1515987 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term44 x y z.
Proof. exact (EQ_MP (@lem1515986 x y z) (@lem1515981 x y z h1)). Qed.
Lemma lem1515989 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1515990 : term177 = term178.
Proof. exact (@lem1515989 (NUMERAL 0) term73). Qed.
Lemma lem1515991 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1515992 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1515993 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1515992 h1) (fun h1 : term178 = True => @lem1515991)). Qed.
Lemma lem1515994 : term178 = True.
Proof. exact (EQ_MP (@lem1515993) (@lem1515991)). Qed.
Lemma lem1515995 : term177 = True.
Proof. exact (TRANS (@lem1515990) (@lem1515994)). Qed.
Lemma lem1515996 : True = term177.
Proof. exact (SYM (@lem1515995)). Qed.
Lemma lem1515997 : term177.
Proof. exact (EQ_MP (@lem1515996) (@lem0)). Qed.
Lemma lem1515998 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term186 x y z.
Proof. exact (conj (@lem1515997) (@lem1515965 x y z h1)). Qed.
Lemma lem1516000 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1516001 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1516000 term76 (term51 x y z)). Qed.
Lemma lem1516002 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term189 x y z.
Proof. exact (@lem1516001 x y z (@lem1515998 x y z h1)). Qed.
Lemma lem1516003 (x : real) (y : real) (z : real) : (term190 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1516004 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516005 (x : real) (y : real) (z : real) : (term191 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1516004) (@lem1516003 x y z)). Qed.
Lemma lem1516006 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1516007 (x : real) (y : real) (z : real) : (term189 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1516005 x y z) (@lem1516006)). Qed.
Lemma lem1516008 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1516007 x y z) (@lem1516002 x y z h1)). Qed.
Lemma lem1516009 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term92 x y z.
Proof. exact (conj (@lem1516008 x y z h1) (@lem1515987 x y z h1)). Qed.
Lemma lem1516011 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1516012 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1516011 (term51 x y z) (term39 x y z)). Qed.
Lemma lem1516013 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term194 x y z.
Proof. exact (@lem1516012 x y z (@lem1516009 x y z h1)). Qed.
Lemma lem1516014 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term40 x) (term50 y z) (term33 y z)). Qed.
Lemma lem1516015 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term66 x). Qed.
Lemma lem1516017 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516018 : term200 = term43.
Proof. exact (@lem1516017 term73). Qed.
Lemma lem1516019 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516020 : term201 = term202.
Proof. exact (MK_COMB (@lem1516019) (@lem1516018)). Qed.
Lemma lem1516021 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1516022 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1516020) (@lem1516021 x)). Qed.
Lemma lem1516023 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1516015 x) (@lem1516022 x)). Qed.
Lemma lem1516024 (x : real) : (term203 x) = term43.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1516025 (x : real) : (term197 x) = term43.
Proof. exact (TRANS (@lem1516023 x) (@lem1516024 x)). Qed.
Lemma lem1516026 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1516027 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1516026) (@lem1516025 x)). Qed.
Lemma lem1516028 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1516029 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term66 y). Qed.
Lemma lem1516031 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516032 : term200 = term43.
Proof. exact (@lem1516031 term73). Qed.
Lemma lem1516033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516034 : term201 = term202.
Proof. exact (MK_COMB (@lem1516033) (@lem1516032)). Qed.
Lemma lem1516035 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1516036 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1516034) (@lem1516035 y)). Qed.
Lemma lem1516037 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1516029 y) (@lem1516036 y)). Qed.
Lemma lem1516038 (y : real) : (term203 y) = term43.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1516039 (y : real) : (term208 y) = term43.
Proof. exact (TRANS (@lem1516037 y) (@lem1516038 y)). Qed.
Lemma lem1516040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1516041 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1516040) (@lem1516039 y)). Qed.
Lemma lem1516042 (z : real) : (term197 z) = (term198 z).
Proof. exact (@lem1483442 term66 z). Qed.
Lemma lem1516044 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516045 : term200 = term43.
Proof. exact (@lem1516044 term73). Qed.
Lemma lem1516046 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516047 : term201 = term202.
Proof. exact (MK_COMB (@lem1516046) (@lem1516045)). Qed.
Lemma lem1516048 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1516049 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1516047) (@lem1516048 z)). Qed.
Lemma lem1516050 (z : real) : (term197 z) = (term203 z).
Proof. exact (TRANS (@lem1516042 z) (@lem1516049 z)). Qed.
Lemma lem1516051 (z : real) : (term203 z) = term43.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1516052 (z : real) : (term197 z) = term43.
Proof. exact (TRANS (@lem1516050 z) (@lem1516051 z)). Qed.
Lemma lem1516053 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1516041 y) (@lem1516052 z)). Qed.
Lemma lem1516054 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1516028 y z) (@lem1516053 y z)). Qed.
Lemma lem1516055 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1516056 (y : real) (z : real) : (term206 y z) = term43.
Proof. exact (TRANS (@lem1516054 y z) (@lem1516055)). Qed.
Lemma lem1516057 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1516027 x) (@lem1516056 y z)). Qed.
Lemma lem1516058 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1516014 x y z) (@lem1516057 x y z)). Qed.
Lemma lem1516059 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1516060 (x : real) (y : real) (z : real) : (term195 x y z) = term43.
Proof. exact (TRANS (@lem1516058 x y z) (@lem1516059)). Qed.
Lemma lem1516061 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516062 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1516061) (@lem1516060 x y z)). Qed.
Lemma lem1516063 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1516064 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1516062 x y z) (@lem1516063)). Qed.
Lemma lem1516065 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term213.
Proof. exact (EQ_MP (@lem1516064 x y z) (@lem1516013 x y z h1)). Qed.
Lemma lem1516067 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1516068 : term213 = term214.
Proof. exact (@lem1516067 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1516069 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1516070 : term213 = False.
Proof. exact (TRANS (@lem1516068) (@lem1516069)). Qed.
Lemma lem1516071 (x : real) (y : real) (z : real) (h1 : term58 x y z) : False.
Proof. exact (EQ_MP (@lem1516070) (@lem1516065 x y z h1)). Qed.
Lemma lem1516072 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (h1). Qed.
Lemma lem1516073 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term44 x y z.
Proof. exact (proj2 (@lem1516072 x y z h1)). Qed.
Lemma lem1516074 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (proj1 (@lem1516072 x y z h1)). Qed.
Lemma lem1516076 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1516077 : term177 = term178.
Proof. exact (@lem1516076 (NUMERAL 0) term73). Qed.
Lemma lem1516078 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1516079 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1516080 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1516079 h1) (fun h1 : term178 = True => @lem1516078)). Qed.
Lemma lem1516081 : term178 = True.
Proof. exact (EQ_MP (@lem1516080) (@lem1516078)). Qed.
Lemma lem1516082 : term177 = True.
Proof. exact (TRANS (@lem1516077) (@lem1516081)). Qed.
Lemma lem1516083 : True = term177.
Proof. exact (SYM (@lem1516082)). Qed.
Lemma lem1516084 : term177.
Proof. exact (EQ_MP (@lem1516083) (@lem0)). Qed.
Lemma lem1516085 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term180 x y z.
Proof. exact (conj (@lem1516084) (@lem1516073 x y z h1)). Qed.
Lemma lem1516087 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1516088 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1516087 term76 (term39 x y z)). Qed.
Lemma lem1516089 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term183 x y z.
Proof. exact (@lem1516088 x y z (@lem1516085 x y z h1)). Qed.
Lemma lem1516090 (x : real) (y : real) (z : real) : (term184 x y z) = (term39 x y z).
Proof. exact (@lem1483460 (term39 x y z)). Qed.
Lemma lem1516091 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1516092 (x : real) (y : real) (z : real) : (term185 x y z) = (term42 x y z).
Proof. exact (MK_COMB (@lem1516091) (@lem1516090 x y z)). Qed.
Lemma lem1516093 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1516094 (x : real) (y : real) (z : real) : (term183 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1516092 x y z) (@lem1516093)). Qed.
Lemma lem1516095 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term44 x y z.
Proof. exact (EQ_MP (@lem1516094 x y z) (@lem1516089 x y z h1)). Qed.
Lemma lem1516097 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1516098 : term177 = term178.
Proof. exact (@lem1516097 (NUMERAL 0) term73). Qed.
Lemma lem1516099 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1516100 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1516101 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1516100 h1) (fun h1 : term178 = True => @lem1516099)). Qed.
Lemma lem1516102 : term178 = True.
Proof. exact (EQ_MP (@lem1516101) (@lem1516099)). Qed.
Lemma lem1516103 : term177 = True.
Proof. exact (TRANS (@lem1516098) (@lem1516102)). Qed.
Lemma lem1516104 : True = term177.
Proof. exact (SYM (@lem1516103)). Qed.
Lemma lem1516105 : term177.
Proof. exact (EQ_MP (@lem1516104) (@lem0)). Qed.
Lemma lem1516106 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term186 x y z.
Proof. exact (conj (@lem1516105) (@lem1516074 x y z h1)). Qed.
Lemma lem1516108 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1516109 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1516108 term76 (term51 x y z)). Qed.
Lemma lem1516110 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term189 x y z.
Proof. exact (@lem1516109 x y z (@lem1516106 x y z h1)). Qed.
Lemma lem1516111 (x : real) (y : real) (z : real) : (term190 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1516112 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516113 (x : real) (y : real) (z : real) : (term191 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1516112) (@lem1516111 x y z)). Qed.
Lemma lem1516114 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1516115 (x : real) (y : real) (z : real) : (term189 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1516113 x y z) (@lem1516114)). Qed.
Lemma lem1516116 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1516115 x y z) (@lem1516110 x y z h1)). Qed.
Lemma lem1516117 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (conj (@lem1516116 x y z h1) (@lem1516095 x y z h1)). Qed.
Lemma lem1516119 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1516120 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1516119 (term51 x y z) (term39 x y z)). Qed.
Lemma lem1516121 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term194 x y z.
Proof. exact (@lem1516120 x y z (@lem1516117 x y z h1)). Qed.
Lemma lem1516122 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term40 x) (term50 y z) (term33 y z)). Qed.
Lemma lem1516123 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term66 x). Qed.
Lemma lem1516125 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516126 : term200 = term43.
Proof. exact (@lem1516125 term73). Qed.
Lemma lem1516127 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516128 : term201 = term202.
Proof. exact (MK_COMB (@lem1516127) (@lem1516126)). Qed.
Lemma lem1516129 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1516130 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1516128) (@lem1516129 x)). Qed.
Lemma lem1516131 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1516123 x) (@lem1516130 x)). Qed.
Lemma lem1516132 (x : real) : (term203 x) = term43.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1516133 (x : real) : (term197 x) = term43.
Proof. exact (TRANS (@lem1516131 x) (@lem1516132 x)). Qed.
Lemma lem1516134 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1516135 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1516134) (@lem1516133 x)). Qed.
Lemma lem1516136 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1516137 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term66 y). Qed.
Lemma lem1516139 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516140 : term200 = term43.
Proof. exact (@lem1516139 term73). Qed.
Lemma lem1516141 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516142 : term201 = term202.
Proof. exact (MK_COMB (@lem1516141) (@lem1516140)). Qed.
Lemma lem1516143 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1516144 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1516142) (@lem1516143 y)). Qed.
Lemma lem1516145 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1516137 y) (@lem1516144 y)). Qed.
Lemma lem1516146 (y : real) : (term203 y) = term43.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1516147 (y : real) : (term208 y) = term43.
Proof. exact (TRANS (@lem1516145 y) (@lem1516146 y)). Qed.
Lemma lem1516148 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1516149 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1516148) (@lem1516147 y)). Qed.
Lemma lem1516150 (z : real) : (term197 z) = (term198 z).
Proof. exact (@lem1483442 term66 z). Qed.
Lemma lem1516152 (m : nat) : (term199 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1516153 : term200 = term43.
Proof. exact (@lem1516152 term73). Qed.
Lemma lem1516154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516155 : term201 = term202.
Proof. exact (MK_COMB (@lem1516154) (@lem1516153)). Qed.
Lemma lem1516156 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1516157 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1516155) (@lem1516156 z)). Qed.
Lemma lem1516158 (z : real) : (term197 z) = (term203 z).
Proof. exact (TRANS (@lem1516150 z) (@lem1516157 z)). Qed.
Lemma lem1516159 (z : real) : (term203 z) = term43.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1516160 (z : real) : (term197 z) = term43.
Proof. exact (TRANS (@lem1516158 z) (@lem1516159 z)). Qed.
Lemma lem1516161 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1516149 y) (@lem1516160 z)). Qed.
Lemma lem1516162 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1516136 y z) (@lem1516161 y z)). Qed.
Lemma lem1516163 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1516164 (y : real) (z : real) : (term206 y z) = term43.
Proof. exact (TRANS (@lem1516162 y z) (@lem1516163)). Qed.
Lemma lem1516165 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1516135 x) (@lem1516164 y z)). Qed.
Lemma lem1516166 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1516122 x y z) (@lem1516165 x y z)). Qed.
Lemma lem1516167 : term210 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1516168 (x : real) (y : real) (z : real) : (term195 x y z) = term43.
Proof. exact (TRANS (@lem1516166 x y z) (@lem1516167)). Qed.
Lemma lem1516169 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516170 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1516169) (@lem1516168 x y z)). Qed.
Lemma lem1516171 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1516172 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1516170 x y z) (@lem1516171)). Qed.
Lemma lem1516173 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term213.
Proof. exact (EQ_MP (@lem1516172 x y z) (@lem1516121 x y z h1)). Qed.
Lemma lem1516175 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1516176 : term213 = term214.
Proof. exact (@lem1516175 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1516177 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1516178 : term213 = False.
Proof. exact (TRANS (@lem1516176) (@lem1516177)). Qed.
Lemma lem1516179 (x : real) (y : real) (z : real) (h1 : term92 x y z) : False.
Proof. exact (EQ_MP (@lem1516178) (@lem1516173 x y z h1)). Qed.
Lemma lem1516180 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (or_elim (@lem1515963 x y z h1) (fun h0 : term58 x y z => @lem1516071 x y z h0) (fun h0 : term92 x y z => @lem1516179 x y z h0)). Qed.
Lemma lem1516182 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1516183 (x : real) (y : real) (z : real) (h1 : term95 x y z) : (term95 x y z) = False.
Proof. exact (prop_ext (fun h2 : term95 x y z => @lem1516180 x y z h1) (fun h2 : False => @lem1516182 x y z h1)). Qed.
Lemma lem1516184 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (EQ_MP (@lem1516183 x y z h1) (@lem1516182 x y z h1)). Qed.
Lemma lem1516185 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1516186 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (ex_elim (@lem1516185 x y h1) (fun z : real => fun h0 : term96 x y z => @lem1516184 x y z h0)). Qed.
Lemma lem1516187 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1516188 (x : real) (h1 : term99 x) : False.
Proof. exact (ex_elim (@lem1516187 x h1) (fun y : real => fun h0 : term98 x y => @lem1516186 x y h0)). Qed.
Lemma lem1516189 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1516190 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1516189 h1) (fun x : real => fun h0 : term100 x => @lem1516188 x h0)). Qed.
Lemma lem1516191 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1516192 (h1 : term23) : term101.
Proof. exact (EQ_MP (@lem1515953) (@lem1516191 h1)). Qed.
Lemma lem1516193 (h1 : term23) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1516190 h2) (fun h2 : False => @lem1516192 h1)). Qed.
Lemma lem1516194 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1516193 h1) (@lem1516192 h1)). Qed.
Lemma lem1516195 : term215.
Proof. exact (fun h0 : term23 => @lem1516194 h0). Qed.
Lemma lem1516196 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1516197 : term217.
Proof. exact (@lem1516196 (@lem1516195)). Qed.
