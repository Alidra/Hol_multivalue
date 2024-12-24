Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SUB_RADD_term_abbrevs.
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
Lemma lem1516227 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1516228 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1516229 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1516228 (term8 x y)). Qed.
Lemma lem1516230 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1516231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1516232 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1516231) (@lem1516230 x z y)). Qed.
Lemma lem1516233 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1516232 x z y) (@lem1516227 x z y)). Qed.
Lemma lem1516234 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1516233 x z y)). Qed.
Lemma lem1516235 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516236 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1516235) (@lem1516234 x y)). Qed.
Lemma lem1516237 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1516229 x y) (@lem1516236 x y)). Qed.
Lemma lem1516238 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1516239 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1516238 (term16 x)). Qed.
Lemma lem1516240 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1516241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1516242 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1516241) (@lem1516240 x y)). Qed.
Lemma lem1516243 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1516242 x y) (@lem1516237 x y)). Qed.
Lemma lem1516244 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1516243 x y)). Qed.
Lemma lem1516245 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516246 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1516245) (@lem1516244 x)). Qed.
Lemma lem1516247 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1516239 x) (@lem1516246 x)). Qed.
Lemma lem1516248 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1516249 : term23 = term24.
Proof. exact (@lem1516248 term25). Qed.
Lemma lem1516250 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1516251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1516252 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1516251) (@lem1516250 x)). Qed.
Lemma lem1516253 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1516252 x) (@lem1516247 x)). Qed.
Lemma lem1516254 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1516253 x)). Qed.
Lemma lem1516255 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516256 : term24 = term31.
Proof. exact (MK_COMB (@lem1516255) (@lem1516254)). Qed.
Lemma lem1516258 : term23 = term31.
Proof. exact (TRANS (@lem1516249) (@lem1516256)). Qed.
Lemma lem1516275 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1516276 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1516275 x z y)). Qed.
Lemma lem1516277 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516278 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1516277) (@lem1516276 x y)). Qed.
Lemma lem1516279 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1516278 x y)). Qed.
Lemma lem1516280 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516281 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1516280) (@lem1516279 x)). Qed.
Lemma lem1516282 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1516281 x)). Qed.
Lemma lem1516283 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516284 : term31 = term31.
Proof. exact (MK_COMB (@lem1516283) (@lem1516282)). Qed.
Lemma lem1516285 : term23 = term31.
Proof. exact (TRANS (@lem1516258) (@lem1516284)). Qed.
Lemma lem1516286 (z : real) (x : real) (y : real) : (term2 x y z) = (term32 z x y).
Proof. exact (@lem1483523 z (real_sub x y)). Qed.
Lemma lem1516299 (x : real) (y : real) : (real_sub x y) = (term33 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1516302 (z : real) : (real_sub z) = (real_sub z).
Proof. exact (eq_refl (real_sub z)). Qed.
Lemma lem1516303 (z : real) (x : real) (y : real) : (term34 z x y) = (term35 z x y).
Proof. exact (MK_COMB (@lem1516302 z) (@lem1516299 x y)). Qed.
Lemma lem1516304 (z : real) (x : real) (y : real) : (term35 z x y) = (term36 z x y).
Proof. exact (@lem1483519 z (term33 x y)). Qed.
Lemma lem1516305 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem1483508 x term39 (term40 y)). Qed.
Lemma lem1516306 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483476 term39 term39 y). Qed.
Lemma lem1516308 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1516309 : term45 = term46.
Proof. exact (@lem1516308 term47 term47). Qed.
Lemma lem1516310 : (term48 = (BIT1 0)) = (term49 = term47).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1516311 : term49 = term47.
Proof. exact (EQ_MP (@lem1516310) (@lem940073)). Qed.
Lemma lem1516312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1516313 : term46 = term50.
Proof. exact (MK_COMB (@lem1516312) (@lem1516311)). Qed.
Lemma lem1516314 : term45 = term50.
Proof. exact (TRANS (@lem1516309) (@lem1516313)). Qed.
Lemma lem1516315 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1516316 : term51 = term52.
Proof. exact (MK_COMB (@lem1516315) (@lem1516314)). Qed.
Lemma lem1516317 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1516318 (y : real) : (term42 y) = (term53 y).
Proof. exact (MK_COMB (@lem1516316) (@lem1516317 y)). Qed.
Lemma lem1516319 (y : real) : (term41 y) = (term53 y).
Proof. exact (TRANS (@lem1516306 y) (@lem1516318 y)). Qed.
Lemma lem1516320 (y : real) : (term53 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1516321 (y : real) : (term41 y) = y.
Proof. exact (TRANS (@lem1516319 y) (@lem1516320 y)). Qed.
Lemma lem1516324 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1516325 (x : real) (y : real) : (term38 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1516324 x) (@lem1516321 y)). Qed.
Lemma lem1516326 (x : real) (y : real) : (term37 x y) = (term55 x y).
Proof. exact (TRANS (@lem1516305 x y) (@lem1516325 x y)). Qed.
Lemma lem1516327 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1516328 (z : real) (x : real) (y : real) : (term36 z x y) = (term56 z x y).
Proof. exact (MK_COMB (@lem1516327 z) (@lem1516326 x y)). Qed.
Lemma lem1516329 (x : real) (z : real) (y : real) : (term56 z x y) = (term57 x z y).
Proof. exact (@lem1483484 (term40 x) z y). Qed.
Lemma lem1516330 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1516331 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1516332 (x : real) (y : real) (z : real) : (term57 x z y) = (term57 x y z).
Proof. exact (MK_COMB (@lem1516331 x) (@lem1516330 y z)). Qed.
Lemma lem1516333 (x : real) (y : real) (z : real) : (term56 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1516329 x z y) (@lem1516332 x y z)). Qed.
Lemma lem1516334 (x : real) (y : real) (z : real) : (term36 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1516328 z x y) (@lem1516333 x y z)). Qed.
Lemma lem1516335 (x : real) (y : real) (z : real) : (term35 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1516304 z x y) (@lem1516334 x y z)). Qed.
Lemma lem1516336 (x : real) (y : real) (z : real) : (term34 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1516303 z x y) (@lem1516335 x y z)). Qed.
Lemma lem1516337 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1516338 (x : real) (y : real) (z : real) : (term58 z x y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1516337) (@lem1516336 x y z)). Qed.
Lemma lem1516339 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1516340 (x : real) (y : real) (z : real) : (term32 z x y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1516338 x y z) (@lem1516339)). Qed.
Lemma lem1516341 (x : real) (y : real) (z : real) : (term2 x y z) = (term61 x y z).
Proof. exact (TRANS (@lem1516286 z x y) (@lem1516340 x y z)). Qed.
Lemma lem1516342 (x : real) (z : real) (y : real) : (term62 x z y) = (term63 x z y).
Proof. exact (@lem1483533 x (real_add z y)). Qed.
Lemma lem1516349 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1516352 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1516353 (x : real) (y : real) (z : real) : (term64 x z y) = (term64 x y z).
Proof. exact (MK_COMB (@lem1516352 x) (@lem1516349 y z)). Qed.
Lemma lem1516354 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1516361 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 y term39 z). Qed.
Lemma lem1516362 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1516365 (x : real) (y : real) (z : real) : (term65 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1516362 x) (@lem1516361 y z)). Qed.
Lemma lem1516366 (x : real) (y : real) (z : real) : (term64 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1516354 x y z) (@lem1516365 x y z)). Qed.
Lemma lem1516367 (x : real) (y : real) (z : real) : (term64 x z y) = (term68 x y z).
Proof. exact (TRANS (@lem1516353 x y z) (@lem1516366 x y z)). Qed.
Lemma lem1516368 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516369 (x : real) (y : real) (z : real) : (term69 x z y) = (term70 x y z).
Proof. exact (MK_COMB (@lem1516368) (@lem1516367 x y z)). Qed.
Lemma lem1516370 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1516371 (x : real) (y : real) (z : real) : (term63 x z y) = (term71 x y z).
Proof. exact (MK_COMB (@lem1516369 x y z) (@lem1516370)). Qed.
Lemma lem1516372 (x : real) (y : real) (z : real) : (term62 x z y) = (term71 x y z).
Proof. exact (TRANS (@lem1516342 x z y) (@lem1516371 x y z)). Qed.
Lemma lem1516373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1516374 (x : real) (y : real) (z : real) : (term72 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1516373) (@lem1516341 x y z)). Qed.
Lemma lem1516375 (x : real) (y : real) (z : real) : (term74 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1516374 x y z) (@lem1516372 x y z)). Qed.
Lemma lem1516376 (x : real) (y : real) (z : real) : (term76 x y z) = (term77 x y z).
Proof. exact (@lem1483533 (real_sub x y) z). Qed.
Lemma lem1516377 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1516390 (x : real) (y : real) : (real_sub x y) = (term33 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1516391 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1516392 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1516391) (@lem1516390 x y)). Qed.
Lemma lem1516393 (x : real) (y : real) (z : real) : (term80 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1516392 x y) (@lem1516377 z)). Qed.
Lemma lem1516394 (x : real) (y : real) (z : real) : (term81 x y z) = (term82 x y z).
Proof. exact (@lem1483519 (term33 x y) z). Qed.
Lemma lem1516403 (x : real) (y : real) (z : real) : (term82 x y z) = (term68 x y z).
Proof. exact (@lem1483482 x (term40 y) (term40 z)). Qed.
Lemma lem1516404 (x : real) (y : real) (z : real) : (term81 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1516394 x y z) (@lem1516403 x y z)). Qed.
Lemma lem1516405 (x : real) (y : real) (z : real) : (term80 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1516393 x y z) (@lem1516404 x y z)). Qed.
Lemma lem1516406 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1516407 (x : real) (y : real) (z : real) : (term83 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1516406) (@lem1516405 x y z)). Qed.
Lemma lem1516408 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1516409 (x : real) (y : real) (z : real) : (term77 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1516407 x y z) (@lem1516408)). Qed.
Lemma lem1516410 (x : real) (y : real) (z : real) : (term76 x y z) = (term71 x y z).
Proof. exact (TRANS (@lem1516376 x y z) (@lem1516409 x y z)). Qed.
Lemma lem1516411 (z : real) (y : real) (x : real) : (term3 x z y) = (term84 z y x).
Proof. exact (@lem1483523 (real_add z y) x). Qed.
Lemma lem1516412 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1516419 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1516420 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1516421 (y : real) (z : real) : (term85 z y) = (term85 y z).
Proof. exact (MK_COMB (@lem1516420) (@lem1516419 y z)). Qed.
Lemma lem1516422 (y : real) (z : real) (x : real) : (term86 z y x) = (term86 y z x).
Proof. exact (MK_COMB (@lem1516421 y z) (@lem1516412 x)). Qed.
Lemma lem1516423 (y : real) (z : real) (x : real) : (term86 y z x) = (term87 y z x).
Proof. exact (@lem1483519 (real_add y z) x). Qed.
Lemma lem1516428 (x : real) (y : real) (z : real) : (term87 y z x) = (term57 x y z).
Proof. exact (@lem1483488 (term40 x) (real_add y z)). Qed.
Lemma lem1516429 (x : real) (y : real) (z : real) : (term86 y z x) = (term57 x y z).
Proof. exact (TRANS (@lem1516423 y z x) (@lem1516428 x y z)). Qed.
Lemma lem1516430 (x : real) (y : real) (z : real) : (term86 z y x) = (term57 x y z).
Proof. exact (TRANS (@lem1516422 y z x) (@lem1516429 x y z)). Qed.
Lemma lem1516431 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1516432 (x : real) (y : real) (z : real) : (term88 z y x) = (term59 x y z).
Proof. exact (MK_COMB (@lem1516431) (@lem1516430 x y z)). Qed.
Lemma lem1516433 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1516434 (x : real) (y : real) (z : real) : (term84 z y x) = (term61 x y z).
Proof. exact (MK_COMB (@lem1516432 x y z) (@lem1516433)). Qed.
Lemma lem1516435 (x : real) (y : real) (z : real) : (term3 x z y) = (term61 x y z).
Proof. exact (TRANS (@lem1516411 z y x) (@lem1516434 x y z)). Qed.
Lemma lem1516436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1516437 (x : real) (y : real) (z : real) : (term89 x y z) = (term90 x y z).
Proof. exact (MK_COMB (@lem1516436) (@lem1516410 x y z)). Qed.
Lemma lem1516438 (x : real) (y : real) (z : real) : (term91 x z y) = (term92 x y z).
Proof. exact (MK_COMB (@lem1516437 x y z) (@lem1516435 x y z)). Qed.
Lemma lem1516439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516440 (x : real) (y : real) (z : real) : (term93 x z y) = (term94 x y z).
Proof. exact (MK_COMB (@lem1516439) (@lem1516375 x y z)). Qed.
Lemma lem1516441 (x : real) (y : real) (z : real) : (term1 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1516440 x y z) (@lem1516438 x y z)). Qed.
Lemma lem1516442 (x : real) (y : real) : (term12 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1516441 x y z)). Qed.
Lemma lem1516443 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516444 (x : real) (y : real) : (term13 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1516443) (@lem1516442 x y)). Qed.
Lemma lem1516445 (x : real) : (term21 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1516444 x y)). Qed.
Lemma lem1516446 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516447 (x : real) : (term22 x) = (term99 x).
Proof. exact (MK_COMB (@lem1516446) (@lem1516445 x)). Qed.
Lemma lem1516448 : term30 = term100.
Proof. exact (fun_ext (fun x : real => @lem1516447 x)). Qed.
Lemma lem1516449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516450 : term31 = term101.
Proof. exact (MK_COMB (@lem1516449) (@lem1516448)). Qed.
Lemma lem1516451 : term23 = term101.
Proof. exact (TRANS (@lem1516285) (@lem1516450)). Qed.
Lemma lem1516461 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1516462 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1516461 real P Q). Qed.
Lemma lem1516463 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1516462 (term108 x y) (term109 x y)). Qed.
Lemma lem1516464 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1516465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516466 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1516465) (@lem1516464 x y z)). Qed.
Lemma lem1516467 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1516468 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1516466 x y z) (@lem1516467 x y z)). Qed.
Lemma lem1516469 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1516468 x y z)). Qed.
Lemma lem1516470 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516471 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1516470) (@lem1516469 x y)). Qed.
Lemma lem1516472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516473 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1516472) (@lem1516471 x y)). Qed.
Lemma lem1516474 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1516475 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1516474 x y z)). Qed.
Lemma lem1516476 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516477 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1516476) (@lem1516475 x y)). Qed.
Lemma lem1516478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516479 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1516478) (@lem1516477 x y)). Qed.
Lemma lem1516480 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1516481 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1516480 x y z)). Qed.
Lemma lem1516482 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516483 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1516482) (@lem1516481 x y)). Qed.
Lemma lem1516484 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1516479 x y) (@lem1516483 x y)). Qed.
Lemma lem1516485 (x : real) (y : real) : ((term106 x y) = (term107 x y)) = ((term97 x y) = (term125 x y)).
Proof. exact (MK_COMB (@lem1516473 x y) (@lem1516484 x y)). Qed.
Lemma lem1516486 (x : real) (y : real) : (term97 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1516485 x y) (@lem1516463 x y)). Qed.
Lemma lem1516583 (x : real) : (term98 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1516486 x y)). Qed.
Lemma lem1516584 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516585 (x : real) : (term99 x) = (term127 x).
Proof. exact (MK_COMB (@lem1516584) (@lem1516583 x)). Qed.
Lemma lem1516587 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1516588 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1516587 real P Q). Qed.
Lemma lem1516589 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1516588 (term130 x) (term131 x)). Qed.
Lemma lem1516590 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1516591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516592 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1516591) (@lem1516590 x y)). Qed.
Lemma lem1516593 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1516594 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1516592 x y) (@lem1516593 x y)). Qed.
Lemma lem1516595 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1516594 x y)). Qed.
Lemma lem1516596 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516597 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1516596) (@lem1516595 x)). Qed.
Lemma lem1516598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516599 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1516598) (@lem1516597 x)). Qed.
Lemma lem1516600 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1516601 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1516600 x y)). Qed.
Lemma lem1516602 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516603 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1516602) (@lem1516601 x)). Qed.
Lemma lem1516604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516605 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1516604) (@lem1516603 x)). Qed.
Lemma lem1516606 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1516607 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1516606 x y)). Qed.
Lemma lem1516608 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516609 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1516608) (@lem1516607 x)). Qed.
Lemma lem1516610 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1516605 x) (@lem1516609 x)). Qed.
Lemma lem1516611 (x : real) : ((term128 x) = (term129 x)) = ((term127 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1516599 x) (@lem1516610 x)). Qed.
Lemma lem1516612 (x : real) : (term127 x) = (term147 x).
Proof. exact (EQ_MP (@lem1516611 x) (@lem1516589 x)). Qed.
Lemma lem1516717 (x : real) : (term99 x) = (term147 x).
Proof. exact (TRANS (@lem1516585 x) (@lem1516612 x)). Qed.
Lemma lem1516718 : term100 = term148.
Proof. exact (fun_ext (fun x : real => @lem1516717 x)). Qed.
Lemma lem1516719 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516720 : term101 = term149.
Proof. exact (MK_COMB (@lem1516719) (@lem1516718)). Qed.
Lemma lem1516722 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1516723 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1516722 real P Q). Qed.
Lemma lem1516724 : term150 = term151.
Proof. exact (@lem1516723 term152 term153). Qed.
Lemma lem1516725 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1516726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516727 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1516726) (@lem1516725 x)). Qed.
Lemma lem1516728 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1516729 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1516727 x) (@lem1516728 x)). Qed.
Lemma lem1516730 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1516729 x)). Qed.
Lemma lem1516731 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516732 : term150 = term149.
Proof. exact (MK_COMB (@lem1516731) (@lem1516730)). Qed.
Lemma lem1516733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516734 : term159 = term160.
Proof. exact (MK_COMB (@lem1516733) (@lem1516732)). Qed.
Lemma lem1516735 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1516736 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1516735 x)). Qed.
Lemma lem1516737 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516738 : term162 = term163.
Proof. exact (MK_COMB (@lem1516737) (@lem1516736)). Qed.
Lemma lem1516739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516740 : term164 = term165.
Proof. exact (MK_COMB (@lem1516739) (@lem1516738)). Qed.
Lemma lem1516741 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1516742 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1516741 x)). Qed.
Lemma lem1516743 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516744 : term167 = term168.
Proof. exact (MK_COMB (@lem1516743) (@lem1516742)). Qed.
Lemma lem1516745 : term151 = term169.
Proof. exact (MK_COMB (@lem1516740) (@lem1516744)). Qed.
Lemma lem1516746 : (term150 = term151) = (term149 = term169).
Proof. exact (MK_COMB (@lem1516734) (@lem1516745)). Qed.
Lemma lem1516747 : term149 = term169.
Proof. exact (EQ_MP (@lem1516746) (@lem1516724)). Qed.
Lemma lem1516860 : term101 = term169.
Proof. exact (TRANS (@lem1516720) (@lem1516747)). Qed.
Lemma lem1516862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1516863 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1516862 real P Q). Qed.
Lemma lem1516864 : term151 = term150.
Proof. exact (@lem1516863 term152 term153). Qed.
Lemma lem1516865 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1516866 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1516865 x)). Qed.
Lemma lem1516867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516868 : term162 = term163.
Proof. exact (MK_COMB (@lem1516867) (@lem1516866)). Qed.
Lemma lem1516869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516870 : term164 = term165.
Proof. exact (MK_COMB (@lem1516869) (@lem1516868)). Qed.
Lemma lem1516871 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1516872 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1516871 x)). Qed.
Lemma lem1516873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516874 : term167 = term168.
Proof. exact (MK_COMB (@lem1516873) (@lem1516872)). Qed.
Lemma lem1516875 : term151 = term169.
Proof. exact (MK_COMB (@lem1516870) (@lem1516874)). Qed.
Lemma lem1516876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516877 : term170 = term171.
Proof. exact (MK_COMB (@lem1516876) (@lem1516875)). Qed.
Lemma lem1516878 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1516879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516880 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1516879) (@lem1516878 x)). Qed.
Lemma lem1516881 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1516882 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1516880 x) (@lem1516881 x)). Qed.
Lemma lem1516883 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1516882 x)). Qed.
Lemma lem1516884 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516885 : term150 = term149.
Proof. exact (MK_COMB (@lem1516884) (@lem1516883)). Qed.
Lemma lem1516886 : (term151 = term150) = (term169 = term149).
Proof. exact (MK_COMB (@lem1516877) (@lem1516885)). Qed.
Lemma lem1516887 : term169 = term149.
Proof. exact (EQ_MP (@lem1516886) (@lem1516864)). Qed.
Lemma lem1516889 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1516890 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1516889 real P Q). Qed.
Lemma lem1516891 (x : real) : (term129 x) = (term128 x).
Proof. exact (@lem1516890 (term130 x) (term131 x)). Qed.
Lemma lem1516892 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1516893 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1516892 x y)). Qed.
Lemma lem1516894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516895 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1516894) (@lem1516893 x)). Qed.
Lemma lem1516896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516897 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1516896) (@lem1516895 x)). Qed.
Lemma lem1516898 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1516899 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1516898 x y)). Qed.
Lemma lem1516900 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516901 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1516900) (@lem1516899 x)). Qed.
Lemma lem1516902 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1516897 x) (@lem1516901 x)). Qed.
Lemma lem1516903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516904 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1516903) (@lem1516902 x)). Qed.
Lemma lem1516905 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1516906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516907 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1516906) (@lem1516905 x y)). Qed.
Lemma lem1516908 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1516909 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1516907 x y) (@lem1516908 x y)). Qed.
Lemma lem1516910 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1516909 x y)). Qed.
Lemma lem1516911 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516912 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1516911) (@lem1516910 x)). Qed.
Lemma lem1516913 (x : real) : ((term129 x) = (term128 x)) = ((term147 x) = (term127 x)).
Proof. exact (MK_COMB (@lem1516904 x) (@lem1516912 x)). Qed.
Lemma lem1516914 (x : real) : (term147 x) = (term127 x).
Proof. exact (EQ_MP (@lem1516913 x) (@lem1516891 x)). Qed.
Lemma lem1516916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1516917 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1516916 real P Q). Qed.
Lemma lem1516918 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1516917 (term108 x y) (term109 x y)). Qed.
Lemma lem1516919 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1516920 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1516919 x y z)). Qed.
Lemma lem1516921 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516922 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1516921) (@lem1516920 x y)). Qed.
Lemma lem1516923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516924 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1516923) (@lem1516922 x y)). Qed.
Lemma lem1516925 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1516926 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1516925 x y z)). Qed.
Lemma lem1516927 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516928 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1516927) (@lem1516926 x y)). Qed.
Lemma lem1516929 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1516924 x y) (@lem1516928 x y)). Qed.
Lemma lem1516930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1516931 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1516930) (@lem1516929 x y)). Qed.
Lemma lem1516932 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1516933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1516934 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1516933) (@lem1516932 x y z)). Qed.
Lemma lem1516935 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1516936 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1516934 x y z) (@lem1516935 x y z)). Qed.
Lemma lem1516937 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1516936 x y z)). Qed.
Lemma lem1516938 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516939 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1516938) (@lem1516937 x y)). Qed.
Lemma lem1516940 (x : real) (y : real) : ((term107 x y) = (term106 x y)) = ((term125 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1516931 x y) (@lem1516939 x y)). Qed.
Lemma lem1516941 (x : real) (y : real) : (term125 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1516940 x y) (@lem1516918 x y)). Qed.
Lemma lem1516942 (x : real) : (term126 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1516941 x y)). Qed.
Lemma lem1516943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516944 (x : real) : (term127 x) = (term99 x).
Proof. exact (MK_COMB (@lem1516943) (@lem1516942 x)). Qed.
Lemma lem1516945 (x : real) : (term147 x) = (term99 x).
Proof. exact (TRANS (@lem1516914 x) (@lem1516944 x)). Qed.
Lemma lem1516946 : term148 = term100.
Proof. exact (fun_ext (fun x : real => @lem1516945 x)). Qed.
Lemma lem1516947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516948 : term149 = term101.
Proof. exact (MK_COMB (@lem1516947) (@lem1516946)). Qed.
Lemma lem1516949 : term169 = term101.
Proof. exact (TRANS (@lem1516887) (@lem1516948)). Qed.
Lemma lem1516950 : term101 = term101.
Proof. exact (TRANS (@lem1516860) (@lem1516949)). Qed.
Lemma lem1516953 : term23 = term101.
Proof. exact (TRANS (@lem1516451) (@lem1516950)). Qed.
Lemma lem1516970 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1516971 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1516970 x y z)). Qed.
Lemma lem1516972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516973 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1516972) (@lem1516971 x y)). Qed.
Lemma lem1516974 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1516973 x y)). Qed.
Lemma lem1516975 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516976 (x : real) : (term99 x) = (term99 x).
Proof. exact (MK_COMB (@lem1516975) (@lem1516974 x)). Qed.
Lemma lem1516977 : term100 = term100.
Proof. exact (fun_ext (fun x : real => @lem1516976 x)). Qed.
Lemma lem1516978 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1516979 : term101 = term101.
Proof. exact (MK_COMB (@lem1516978) (@lem1516977)). Qed.
Lemma lem1516980 : term23 = term101.
Proof. exact (TRANS (@lem1516953) (@lem1516979)). Qed.
Lemma lem1516990 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1516991 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term75 x y z.
Proof. exact (h1). Qed.
Lemma lem1516992 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term71 x y z.
Proof. exact (proj2 (@lem1516991 x y z h1)). Qed.
Lemma lem1516993 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term61 x y z.
Proof. exact (proj1 (@lem1516991 x y z h1)). Qed.
Lemma lem1516995 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1516996 : term177 = term178.
Proof. exact (@lem1516995 (NUMERAL 0) term47). Qed.
Lemma lem1516997 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1516998 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1516999 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1516998 h1) (fun h1 : term178 = True => @lem1516997)). Qed.
Lemma lem1517000 : term178 = True.
Proof. exact (EQ_MP (@lem1516999) (@lem1516997)). Qed.
Lemma lem1517001 : term177 = True.
Proof. exact (TRANS (@lem1516996) (@lem1517000)). Qed.
Lemma lem1517002 : True = term177.
Proof. exact (SYM (@lem1517001)). Qed.
Lemma lem1517003 : term177.
Proof. exact (EQ_MP (@lem1517002) (@lem0)). Qed.
Lemma lem1517004 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term180 x y z.
Proof. exact (conj (@lem1517003) (@lem1516993 x y z h1)). Qed.
Lemma lem1517006 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1517007 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1517006 term50 (term57 x y z)). Qed.
Lemma lem1517008 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term183 x y z.
Proof. exact (@lem1517007 x y z (@lem1517004 x y z h1)). Qed.
Lemma lem1517009 (x : real) (y : real) (z : real) : (term184 x y z) = (term57 x y z).
Proof. exact (@lem1483460 (term57 x y z)). Qed.
Lemma lem1517010 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1517011 (x : real) (y : real) (z : real) : (term185 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1517010) (@lem1517009 x y z)). Qed.
Lemma lem1517012 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517013 (x : real) (y : real) (z : real) : (term183 x y z) = (term61 x y z).
Proof. exact (MK_COMB (@lem1517011 x y z) (@lem1517012)). Qed.
Lemma lem1517014 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term61 x y z.
Proof. exact (EQ_MP (@lem1517013 x y z) (@lem1517008 x y z h1)). Qed.
Lemma lem1517016 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517017 : term177 = term178.
Proof. exact (@lem1517016 (NUMERAL 0) term47). Qed.
Lemma lem1517018 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1517019 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1517020 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1517019 h1) (fun h1 : term178 = True => @lem1517018)). Qed.
Lemma lem1517021 : term178 = True.
Proof. exact (EQ_MP (@lem1517020) (@lem1517018)). Qed.
Lemma lem1517022 : term177 = True.
Proof. exact (TRANS (@lem1517017) (@lem1517021)). Qed.
Lemma lem1517023 : True = term177.
Proof. exact (SYM (@lem1517022)). Qed.
Lemma lem1517024 : term177.
Proof. exact (EQ_MP (@lem1517023) (@lem0)). Qed.
Lemma lem1517025 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term186 x y z.
Proof. exact (conj (@lem1517024) (@lem1516992 x y z h1)). Qed.
Lemma lem1517027 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1517028 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1517027 term50 (term68 x y z)). Qed.
Lemma lem1517029 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term189 x y z.
Proof. exact (@lem1517028 x y z (@lem1517025 x y z h1)). Qed.
Lemma lem1517030 (x : real) (y : real) (z : real) : (term190 x y z) = (term68 x y z).
Proof. exact (@lem1483460 (term68 x y z)). Qed.
Lemma lem1517031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517032 (x : real) (y : real) (z : real) : (term191 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1517031) (@lem1517030 x y z)). Qed.
Lemma lem1517033 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517034 (x : real) (y : real) (z : real) : (term189 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1517032 x y z) (@lem1517033)). Qed.
Lemma lem1517035 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term71 x y z.
Proof. exact (EQ_MP (@lem1517034 x y z) (@lem1517029 x y z h1)). Qed.
Lemma lem1517036 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term92 x y z.
Proof. exact (conj (@lem1517035 x y z h1) (@lem1517014 x y z h1)). Qed.
Lemma lem1517038 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1517039 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1517038 (term68 x y z) (term57 x y z)). Qed.
Lemma lem1517040 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term194 x y z.
Proof. exact (@lem1517039 x y z (@lem1517036 x y z h1)). Qed.
Lemma lem1517041 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term40 x) (term67 y z) (real_add y z)). Qed.
Lemma lem1517042 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1517044 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517045 : term200 = term60.
Proof. exact (@lem1517044 term47). Qed.
Lemma lem1517046 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517047 : term201 = term202.
Proof. exact (MK_COMB (@lem1517046) (@lem1517045)). Qed.
Lemma lem1517048 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517049 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1517047) (@lem1517048 x)). Qed.
Lemma lem1517050 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1517042 x) (@lem1517049 x)). Qed.
Lemma lem1517051 (x : real) : (term203 x) = term60.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1517052 (x : real) : (term197 x) = term60.
Proof. exact (TRANS (@lem1517050 x) (@lem1517051 x)). Qed.
Lemma lem1517053 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517054 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1517053) (@lem1517052 x)). Qed.
Lemma lem1517055 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term40 y) y (term40 z) z). Qed.
Lemma lem1517056 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1517058 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517059 : term200 = term60.
Proof. exact (@lem1517058 term47). Qed.
Lemma lem1517060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517061 : term201 = term202.
Proof. exact (MK_COMB (@lem1517060) (@lem1517059)). Qed.
Lemma lem1517062 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1517063 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1517061) (@lem1517062 y)). Qed.
Lemma lem1517064 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1517056 y) (@lem1517063 y)). Qed.
Lemma lem1517065 (y : real) : (term203 y) = term60.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1517066 (y : real) : (term208 y) = term60.
Proof. exact (TRANS (@lem1517064 y) (@lem1517065 y)). Qed.
Lemma lem1517067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517068 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1517067) (@lem1517066 y)). Qed.
Lemma lem1517069 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483440 term39 z). Qed.
Lemma lem1517071 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517072 : term200 = term60.
Proof. exact (@lem1517071 term47). Qed.
Lemma lem1517073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517074 : term201 = term202.
Proof. exact (MK_COMB (@lem1517073) (@lem1517072)). Qed.
Lemma lem1517075 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1517076 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1517074) (@lem1517075 z)). Qed.
Lemma lem1517077 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1517069 z) (@lem1517076 z)). Qed.
Lemma lem1517078 (z : real) : (term203 z) = term60.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1517079 (z : real) : (term208 z) = term60.
Proof. exact (TRANS (@lem1517077 z) (@lem1517078 z)). Qed.
Lemma lem1517080 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1517068 y) (@lem1517079 z)). Qed.
Lemma lem1517081 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1517055 y z) (@lem1517080 y z)). Qed.
Lemma lem1517082 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1517083 (y : real) (z : real) : (term206 y z) = term60.
Proof. exact (TRANS (@lem1517081 y z) (@lem1517082)). Qed.
Lemma lem1517084 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1517054 x) (@lem1517083 y z)). Qed.
Lemma lem1517085 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1517041 x y z) (@lem1517084 x y z)). Qed.
Lemma lem1517086 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1517087 (x : real) (y : real) (z : real) : (term195 x y z) = term60.
Proof. exact (TRANS (@lem1517085 x y z) (@lem1517086)). Qed.
Lemma lem1517088 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517089 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1517088) (@lem1517087 x y z)). Qed.
Lemma lem1517090 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517091 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1517089 x y z) (@lem1517090)). Qed.
Lemma lem1517092 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term213.
Proof. exact (EQ_MP (@lem1517091 x y z) (@lem1517040 x y z h1)). Qed.
Lemma lem1517094 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517095 : term213 = term214.
Proof. exact (@lem1517094 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517096 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517097 : term213 = False.
Proof. exact (TRANS (@lem1517095) (@lem1517096)). Qed.
Lemma lem1517098 (x : real) (y : real) (z : real) (h1 : term75 x y z) : False.
Proof. exact (EQ_MP (@lem1517097) (@lem1517092 x y z h1)). Qed.
Lemma lem1517099 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (h1). Qed.
Lemma lem1517100 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term61 x y z.
Proof. exact (proj2 (@lem1517099 x y z h1)). Qed.
Lemma lem1517101 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term71 x y z.
Proof. exact (proj1 (@lem1517099 x y z h1)). Qed.
Lemma lem1517103 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517104 : term177 = term178.
Proof. exact (@lem1517103 (NUMERAL 0) term47). Qed.
Lemma lem1517105 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1517106 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1517107 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1517106 h1) (fun h1 : term178 = True => @lem1517105)). Qed.
Lemma lem1517108 : term178 = True.
Proof. exact (EQ_MP (@lem1517107) (@lem1517105)). Qed.
Lemma lem1517109 : term177 = True.
Proof. exact (TRANS (@lem1517104) (@lem1517108)). Qed.
Lemma lem1517110 : True = term177.
Proof. exact (SYM (@lem1517109)). Qed.
Lemma lem1517111 : term177.
Proof. exact (EQ_MP (@lem1517110) (@lem0)). Qed.
Lemma lem1517112 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term180 x y z.
Proof. exact (conj (@lem1517111) (@lem1517100 x y z h1)). Qed.
Lemma lem1517114 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1517115 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1517114 term50 (term57 x y z)). Qed.
Lemma lem1517116 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term183 x y z.
Proof. exact (@lem1517115 x y z (@lem1517112 x y z h1)). Qed.
Lemma lem1517117 (x : real) (y : real) (z : real) : (term184 x y z) = (term57 x y z).
Proof. exact (@lem1483460 (term57 x y z)). Qed.
Lemma lem1517118 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1517119 (x : real) (y : real) (z : real) : (term185 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1517118) (@lem1517117 x y z)). Qed.
Lemma lem1517120 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517121 (x : real) (y : real) (z : real) : (term183 x y z) = (term61 x y z).
Proof. exact (MK_COMB (@lem1517119 x y z) (@lem1517120)). Qed.
Lemma lem1517122 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term61 x y z.
Proof. exact (EQ_MP (@lem1517121 x y z) (@lem1517116 x y z h1)). Qed.
Lemma lem1517124 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517125 : term177 = term178.
Proof. exact (@lem1517124 (NUMERAL 0) term47). Qed.
Lemma lem1517126 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1517127 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1517128 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1517127 h1) (fun h1 : term178 = True => @lem1517126)). Qed.
Lemma lem1517129 : term178 = True.
Proof. exact (EQ_MP (@lem1517128) (@lem1517126)). Qed.
Lemma lem1517130 : term177 = True.
Proof. exact (TRANS (@lem1517125) (@lem1517129)). Qed.
Lemma lem1517131 : True = term177.
Proof. exact (SYM (@lem1517130)). Qed.
Lemma lem1517132 : term177.
Proof. exact (EQ_MP (@lem1517131) (@lem0)). Qed.
Lemma lem1517133 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term186 x y z.
Proof. exact (conj (@lem1517132) (@lem1517101 x y z h1)). Qed.
Lemma lem1517135 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1517136 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1517135 term50 (term68 x y z)). Qed.
Lemma lem1517137 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term189 x y z.
Proof. exact (@lem1517136 x y z (@lem1517133 x y z h1)). Qed.
Lemma lem1517138 (x : real) (y : real) (z : real) : (term190 x y z) = (term68 x y z).
Proof. exact (@lem1483460 (term68 x y z)). Qed.
Lemma lem1517139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517140 (x : real) (y : real) (z : real) : (term191 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1517139) (@lem1517138 x y z)). Qed.
Lemma lem1517141 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517142 (x : real) (y : real) (z : real) : (term189 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1517140 x y z) (@lem1517141)). Qed.
Lemma lem1517143 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term71 x y z.
Proof. exact (EQ_MP (@lem1517142 x y z) (@lem1517137 x y z h1)). Qed.
Lemma lem1517144 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (conj (@lem1517143 x y z h1) (@lem1517122 x y z h1)). Qed.
Lemma lem1517146 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1517147 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1517146 (term68 x y z) (term57 x y z)). Qed.
Lemma lem1517148 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term194 x y z.
Proof. exact (@lem1517147 x y z (@lem1517144 x y z h1)). Qed.
Lemma lem1517149 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term40 x) (term67 y z) (real_add y z)). Qed.
Lemma lem1517150 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1517152 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517153 : term200 = term60.
Proof. exact (@lem1517152 term47). Qed.
Lemma lem1517154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517155 : term201 = term202.
Proof. exact (MK_COMB (@lem1517154) (@lem1517153)). Qed.
Lemma lem1517156 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517157 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1517155) (@lem1517156 x)). Qed.
Lemma lem1517158 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1517150 x) (@lem1517157 x)). Qed.
Lemma lem1517159 (x : real) : (term203 x) = term60.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1517160 (x : real) : (term197 x) = term60.
Proof. exact (TRANS (@lem1517158 x) (@lem1517159 x)). Qed.
Lemma lem1517161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517162 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1517161) (@lem1517160 x)). Qed.
Lemma lem1517163 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term40 y) y (term40 z) z). Qed.
Lemma lem1517164 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1517166 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517167 : term200 = term60.
Proof. exact (@lem1517166 term47). Qed.
Lemma lem1517168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517169 : term201 = term202.
Proof. exact (MK_COMB (@lem1517168) (@lem1517167)). Qed.
Lemma lem1517170 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1517171 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1517169) (@lem1517170 y)). Qed.
Lemma lem1517172 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1517164 y) (@lem1517171 y)). Qed.
Lemma lem1517173 (y : real) : (term203 y) = term60.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1517174 (y : real) : (term208 y) = term60.
Proof. exact (TRANS (@lem1517172 y) (@lem1517173 y)). Qed.
Lemma lem1517175 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517176 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1517175) (@lem1517174 y)). Qed.
Lemma lem1517177 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483440 term39 z). Qed.
Lemma lem1517179 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517180 : term200 = term60.
Proof. exact (@lem1517179 term47). Qed.
Lemma lem1517181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517182 : term201 = term202.
Proof. exact (MK_COMB (@lem1517181) (@lem1517180)). Qed.
Lemma lem1517183 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1517184 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1517182) (@lem1517183 z)). Qed.
Lemma lem1517185 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1517177 z) (@lem1517184 z)). Qed.
Lemma lem1517186 (z : real) : (term203 z) = term60.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1517187 (z : real) : (term208 z) = term60.
Proof. exact (TRANS (@lem1517185 z) (@lem1517186 z)). Qed.
Lemma lem1517188 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1517176 y) (@lem1517187 z)). Qed.
Lemma lem1517189 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1517163 y z) (@lem1517188 y z)). Qed.
Lemma lem1517190 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1517191 (y : real) (z : real) : (term206 y z) = term60.
Proof. exact (TRANS (@lem1517189 y z) (@lem1517190)). Qed.
Lemma lem1517192 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1517162 x) (@lem1517191 y z)). Qed.
Lemma lem1517193 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1517149 x y z) (@lem1517192 x y z)). Qed.
Lemma lem1517194 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1517195 (x : real) (y : real) (z : real) : (term195 x y z) = term60.
Proof. exact (TRANS (@lem1517193 x y z) (@lem1517194)). Qed.
Lemma lem1517196 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517197 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1517196) (@lem1517195 x y z)). Qed.
Lemma lem1517198 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1517199 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1517197 x y z) (@lem1517198)). Qed.
Lemma lem1517200 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term213.
Proof. exact (EQ_MP (@lem1517199 x y z) (@lem1517148 x y z h1)). Qed.
Lemma lem1517202 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517203 : term213 = term214.
Proof. exact (@lem1517202 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517204 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517205 : term213 = False.
Proof. exact (TRANS (@lem1517203) (@lem1517204)). Qed.
Lemma lem1517206 (x : real) (y : real) (z : real) (h1 : term92 x y z) : False.
Proof. exact (EQ_MP (@lem1517205) (@lem1517200 x y z h1)). Qed.
Lemma lem1517207 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (or_elim (@lem1516990 x y z h1) (fun h0 : term75 x y z => @lem1517098 x y z h0) (fun h0 : term92 x y z => @lem1517206 x y z h0)). Qed.
Lemma lem1517209 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1517210 (x : real) (y : real) (z : real) (h1 : term95 x y z) : (term95 x y z) = False.
Proof. exact (prop_ext (fun h2 : term95 x y z => @lem1517207 x y z h1) (fun h2 : False => @lem1517209 x y z h1)). Qed.
Lemma lem1517211 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (EQ_MP (@lem1517210 x y z h1) (@lem1517209 x y z h1)). Qed.
Lemma lem1517212 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1517213 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (ex_elim (@lem1517212 x y h1) (fun z : real => fun h0 : term96 x y z => @lem1517211 x y z h0)). Qed.
Lemma lem1517214 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1517215 (x : real) (h1 : term99 x) : False.
Proof. exact (ex_elim (@lem1517214 x h1) (fun y : real => fun h0 : term98 x y => @lem1517213 x y h0)). Qed.
Lemma lem1517216 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1517217 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1517216 h1) (fun x : real => fun h0 : term100 x => @lem1517215 x h0)). Qed.
Lemma lem1517218 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1517219 (h1 : term23) : term101.
Proof. exact (EQ_MP (@lem1516980) (@lem1517218 h1)). Qed.
Lemma lem1517220 (h1 : term23) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1517217 h2) (fun h2 : False => @lem1517219 h1)). Qed.
Lemma lem1517221 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1517220 h1) (@lem1517219 h1)). Qed.
Lemma lem1517222 : term215.
Proof. exact (fun h0 : term23 => @lem1517221 h0). Qed.
Lemma lem1517223 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1517224 : term217.
Proof. exact (@lem1517223 (@lem1517222)). Qed.
