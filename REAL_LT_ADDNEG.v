Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADDNEG_term_abbrevs.
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
Lemma lem1502297 (y : real) (z : real) (x : real) : (term0 y z x) = (term1 y z x).
Proof. exact (@lem17646 (term2 y x z) (term3 y z x)). Qed.
Lemma lem1502298 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1502299 (y : real) (x : real) : (term6 y x) = (term7 y x).
Proof. exact (@lem1502298 (term8 y x)). Qed.
Lemma lem1502300 (y : real) (z : real) (x : real) : (term9 y x z) = ((term2 y x z) = (term3 y z x)).
Proof. exact (eq_refl (term9 y x z)). Qed.
Lemma lem1502301 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1502302 (y : real) (z : real) (x : real) : (term10 y x z) = (term0 y z x).
Proof. exact (MK_COMB (@lem1502301) (@lem1502300 y z x)). Qed.
Lemma lem1502303 (y : real) (z : real) (x : real) : (term10 y x z) = (term1 y z x).
Proof. exact (TRANS (@lem1502302 y z x) (@lem1502297 y z x)). Qed.
Lemma lem1502304 (y : real) (x : real) : (term11 y x) = (term12 y x).
Proof. exact (fun_ext (fun z : real => @lem1502303 y z x)). Qed.
Lemma lem1502305 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502306 (y : real) (x : real) : (term7 y x) = (term13 y x).
Proof. exact (MK_COMB (@lem1502305) (@lem1502304 y x)). Qed.
Lemma lem1502307 (y : real) (x : real) : (term6 y x) = (term13 y x).
Proof. exact (TRANS (@lem1502299 y x) (@lem1502306 y x)). Qed.
Lemma lem1502308 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1502309 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1502308 (term16 x)). Qed.
Lemma lem1502310 (y : real) (x : real) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1502311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1502312 (y : real) (x : real) : (term19 x y) = (term6 y x).
Proof. exact (MK_COMB (@lem1502311) (@lem1502310 y x)). Qed.
Lemma lem1502313 (y : real) (x : real) : (term19 x y) = (term13 y x).
Proof. exact (TRANS (@lem1502312 y x) (@lem1502307 y x)). Qed.
Lemma lem1502314 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1502313 y x)). Qed.
Lemma lem1502315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502316 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1502315) (@lem1502314 x)). Qed.
Lemma lem1502317 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1502309 x) (@lem1502316 x)). Qed.
Lemma lem1502318 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1502319 : term23 = term24.
Proof. exact (@lem1502318 term25). Qed.
Lemma lem1502320 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1502321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1502322 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1502321) (@lem1502320 x)). Qed.
Lemma lem1502323 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1502322 x) (@lem1502317 x)). Qed.
Lemma lem1502324 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1502323 x)). Qed.
Lemma lem1502325 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502326 : term24 = term31.
Proof. exact (MK_COMB (@lem1502325) (@lem1502324)). Qed.
Lemma lem1502328 : term23 = term31.
Proof. exact (TRANS (@lem1502319) (@lem1502326)). Qed.
Lemma lem1502345 (y : real) (z : real) (x : real) : (term1 y z x) = (term1 y z x).
Proof. exact (eq_refl (term1 y z x)). Qed.
Lemma lem1502346 (y : real) (x : real) : (term12 y x) = (term12 y x).
Proof. exact (fun_ext (fun z : real => @lem1502345 y z x)). Qed.
Lemma lem1502347 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502348 (y : real) (x : real) : (term13 y x) = (term13 y x).
Proof. exact (MK_COMB (@lem1502347) (@lem1502346 y x)). Qed.
Lemma lem1502349 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1502348 y x)). Qed.
Lemma lem1502350 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502351 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1502350) (@lem1502349 x)). Qed.
Lemma lem1502352 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1502351 x)). Qed.
Lemma lem1502353 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502354 : term31 = term31.
Proof. exact (MK_COMB (@lem1502353) (@lem1502352)). Qed.
Lemma lem1502355 : term23 = term31.
Proof. exact (TRANS (@lem1502328) (@lem1502354)). Qed.
Lemma lem1502356 (x : real) (z : real) (y : real) : (term2 y x z) = (term32 x z y).
Proof. exact (@lem1483521 (term33 x z) y). Qed.
Lemma lem1502357 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1502364 (z : real) : (real_neg z) = (term34 z).
Proof. exact (@lem1483512 z). Qed.
Lemma lem1502367 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1502370 (x : real) (z : real) : (term33 x z) = (term35 x z).
Proof. exact (MK_COMB (@lem1502367 x) (@lem1502364 z)). Qed.
Lemma lem1502371 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1502372 (x : real) (z : real) : (term36 x z) = (term37 x z).
Proof. exact (MK_COMB (@lem1502371) (@lem1502370 x z)). Qed.
Lemma lem1502373 (x : real) (z : real) (y : real) : (term38 x z y) = (term39 x z y).
Proof. exact (MK_COMB (@lem1502372 x z) (@lem1502357 y)). Qed.
Lemma lem1502374 (x : real) (z : real) (y : real) : (term39 x z y) = (term40 x z y).
Proof. exact (@lem1483519 (term35 x z) y). Qed.
Lemma lem1502378 (x : real) (z : real) (y : real) : (term40 x z y) = (term41 x z y).
Proof. exact (@lem1483482 x (term34 z) (term34 y)). Qed.
Lemma lem1502379 (y : real) (z : real) : (term42 z y) = (term42 y z).
Proof. exact (@lem1483488 (term34 y) (term34 z)). Qed.
Lemma lem1502380 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1502381 (x : real) (y : real) (z : real) : (term41 x z y) = (term41 x y z).
Proof. exact (MK_COMB (@lem1502380 x) (@lem1502379 y z)). Qed.
Lemma lem1502383 (x : real) (y : real) (z : real) : (term40 x z y) = (term41 x y z).
Proof. exact (TRANS (@lem1502378 x z y) (@lem1502381 x y z)). Qed.
Lemma lem1502384 (x : real) (y : real) (z : real) : (term39 x z y) = (term41 x y z).
Proof. exact (TRANS (@lem1502374 x z y) (@lem1502383 x y z)). Qed.
Lemma lem1502385 (x : real) (y : real) (z : real) : (term38 x z y) = (term41 x y z).
Proof. exact (TRANS (@lem1502373 x z y) (@lem1502384 x y z)). Qed.
Lemma lem1502386 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1502387 (x : real) (y : real) (z : real) : (term43 x z y) = (term44 x y z).
Proof. exact (MK_COMB (@lem1502386) (@lem1502385 x y z)). Qed.
Lemma lem1502388 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1502389 (x : real) (y : real) (z : real) : (term32 x z y) = (term46 x y z).
Proof. exact (MK_COMB (@lem1502387 x y z) (@lem1502388)). Qed.
Lemma lem1502390 (x : real) (y : real) (z : real) : (term2 y x z) = (term46 x y z).
Proof. exact (TRANS (@lem1502356 x z y) (@lem1502389 x y z)). Qed.
Lemma lem1502391 (y : real) (z : real) (x : real) : (term47 y z x) = (term48 y z x).
Proof. exact (@lem1483531 (real_add y z) x). Qed.
Lemma lem1502403 (y : real) (z : real) (x : real) : (term49 y z x) = (term50 y z x).
Proof. exact (@lem1483519 (real_add y z) x). Qed.
Lemma lem1502408 (x : real) (y : real) (z : real) : (term50 y z x) = (term51 x y z).
Proof. exact (@lem1483488 (term34 x) (real_add y z)). Qed.
Lemma lem1502410 (x : real) (y : real) (z : real) : (term49 y z x) = (term51 x y z).
Proof. exact (TRANS (@lem1502403 y z x) (@lem1502408 x y z)). Qed.
Lemma lem1502411 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1502412 (x : real) (y : real) (z : real) : (term52 y z x) = (term53 x y z).
Proof. exact (MK_COMB (@lem1502411) (@lem1502410 x y z)). Qed.
Lemma lem1502413 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1502414 (x : real) (y : real) (z : real) : (term48 y z x) = (term54 x y z).
Proof. exact (MK_COMB (@lem1502412 x y z) (@lem1502413)). Qed.
Lemma lem1502415 (x : real) (y : real) (z : real) : (term47 y z x) = (term54 x y z).
Proof. exact (TRANS (@lem1502391 y z x) (@lem1502414 x y z)). Qed.
Lemma lem1502416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1502417 (x : real) (y : real) (z : real) : (term55 y x z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1502416) (@lem1502390 x y z)). Qed.
Lemma lem1502418 (x : real) (y : real) (z : real) : (term57 y z x) = (term58 x y z).
Proof. exact (MK_COMB (@lem1502417 x y z) (@lem1502415 x y z)). Qed.
Lemma lem1502419 (y : real) (x : real) (z : real) : (term59 y x z) = (term60 y x z).
Proof. exact (@lem1483531 y (term33 x z)). Qed.
Lemma lem1502426 (z : real) : (real_neg z) = (term34 z).
Proof. exact (@lem1483512 z). Qed.
Lemma lem1502429 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1502432 (x : real) (z : real) : (term33 x z) = (term35 x z).
Proof. exact (MK_COMB (@lem1502429 x) (@lem1502426 z)). Qed.
Lemma lem1502435 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1502436 (y : real) (x : real) (z : real) : (term61 y x z) = (term62 y x z).
Proof. exact (MK_COMB (@lem1502435 y) (@lem1502432 x z)). Qed.
Lemma lem1502437 (y : real) (x : real) (z : real) : (term62 y x z) = (term63 y x z).
Proof. exact (@lem1483519 y (term35 x z)). Qed.
Lemma lem1502438 (x : real) (z : real) : (term64 x z) = (term65 x z).
Proof. exact (@lem1483508 x term66 (term34 z)). Qed.
Lemma lem1502439 (z : real) : (term67 z) = (term68 z).
Proof. exact (@lem1483476 term66 term66 z). Qed.
Lemma lem1502441 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1502442 : term71 = term72.
Proof. exact (@lem1502441 term73 term73). Qed.
Lemma lem1502443 : (term74 = (BIT1 0)) = (term75 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1502444 : term75 = term73.
Proof. exact (EQ_MP (@lem1502443) (@lem940073)). Qed.
Lemma lem1502445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1502446 : term72 = term76.
Proof. exact (MK_COMB (@lem1502445) (@lem1502444)). Qed.
Lemma lem1502447 : term71 = term76.
Proof. exact (TRANS (@lem1502442) (@lem1502446)). Qed.
Lemma lem1502448 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1502449 : term77 = term78.
Proof. exact (MK_COMB (@lem1502448) (@lem1502447)). Qed.
Lemma lem1502450 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1502451 (z : real) : (term68 z) = (term79 z).
Proof. exact (MK_COMB (@lem1502449) (@lem1502450 z)). Qed.
Lemma lem1502452 (z : real) : (term67 z) = (term79 z).
Proof. exact (TRANS (@lem1502439 z) (@lem1502451 z)). Qed.
Lemma lem1502453 (z : real) : (term79 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1502454 (z : real) : (term67 z) = z.
Proof. exact (TRANS (@lem1502452 z) (@lem1502453 z)). Qed.
Lemma lem1502457 (x : real) : (term80 x) = (term80 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1502458 (x : real) (z : real) : (term65 x z) = (term81 x z).
Proof. exact (MK_COMB (@lem1502457 x) (@lem1502454 z)). Qed.
Lemma lem1502459 (x : real) (z : real) : (term64 x z) = (term81 x z).
Proof. exact (TRANS (@lem1502438 x z) (@lem1502458 x z)). Qed.
Lemma lem1502460 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1502461 (y : real) (x : real) (z : real) : (term63 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem1502460 y) (@lem1502459 x z)). Qed.
Lemma lem1502466 (x : real) (y : real) (z : real) : (term82 y x z) = (term51 x y z).
Proof. exact (@lem1483484 (term34 x) y z). Qed.
Lemma lem1502467 (x : real) (y : real) (z : real) : (term63 y x z) = (term51 x y z).
Proof. exact (TRANS (@lem1502461 y x z) (@lem1502466 x y z)). Qed.
Lemma lem1502468 (x : real) (y : real) (z : real) : (term62 y x z) = (term51 x y z).
Proof. exact (TRANS (@lem1502437 y x z) (@lem1502467 x y z)). Qed.
Lemma lem1502469 (x : real) (y : real) (z : real) : (term61 y x z) = (term51 x y z).
Proof. exact (TRANS (@lem1502436 y x z) (@lem1502468 x y z)). Qed.
Lemma lem1502470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1502471 (x : real) (y : real) (z : real) : (term83 y x z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1502470) (@lem1502469 x y z)). Qed.
Lemma lem1502472 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1502473 (x : real) (y : real) (z : real) : (term60 y x z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1502471 x y z) (@lem1502472)). Qed.
Lemma lem1502474 (x : real) (y : real) (z : real) : (term59 y x z) = (term54 x y z).
Proof. exact (TRANS (@lem1502419 y x z) (@lem1502473 x y z)). Qed.
Lemma lem1502475 (x : real) (y : real) (z : real) : (term3 y z x) = (term84 x y z).
Proof. exact (@lem1483521 x (real_add y z)). Qed.
Lemma lem1502487 (x : real) (y : real) (z : real) : (term85 x y z) = (term86 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1502494 (y : real) (z : real) : (term87 y z) = (term42 y z).
Proof. exact (@lem1483508 y term66 z). Qed.
Lemma lem1502495 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1502498 (x : real) (y : real) (z : real) : (term86 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem1502495 x) (@lem1502494 y z)). Qed.
Lemma lem1502500 (x : real) (y : real) (z : real) : (term85 x y z) = (term41 x y z).
Proof. exact (TRANS (@lem1502487 x y z) (@lem1502498 x y z)). Qed.
Lemma lem1502501 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1502502 (x : real) (y : real) (z : real) : (term88 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1502501) (@lem1502500 x y z)). Qed.
Lemma lem1502503 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1502504 (x : real) (y : real) (z : real) : (term84 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1502502 x y z) (@lem1502503)). Qed.
Lemma lem1502505 (x : real) (y : real) (z : real) : (term3 y z x) = (term46 x y z).
Proof. exact (TRANS (@lem1502475 x y z) (@lem1502504 x y z)). Qed.
Lemma lem1502506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1502507 (x : real) (y : real) (z : real) : (term89 y x z) = (term90 x y z).
Proof. exact (MK_COMB (@lem1502506) (@lem1502474 x y z)). Qed.
Lemma lem1502508 (x : real) (y : real) (z : real) : (term91 y z x) = (term92 x y z).
Proof. exact (MK_COMB (@lem1502507 x y z) (@lem1502505 x y z)). Qed.
Lemma lem1502509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502510 (x : real) (y : real) (z : real) : (term93 y z x) = (term94 x y z).
Proof. exact (MK_COMB (@lem1502509) (@lem1502418 x y z)). Qed.
Lemma lem1502511 (x : real) (y : real) (z : real) : (term1 y z x) = (term95 x y z).
Proof. exact (MK_COMB (@lem1502510 x y z) (@lem1502508 x y z)). Qed.
Lemma lem1502512 (x : real) (y : real) : (term12 y x) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1502511 x y z)). Qed.
Lemma lem1502513 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502514 (x : real) (y : real) : (term13 y x) = (term97 x y).
Proof. exact (MK_COMB (@lem1502513) (@lem1502512 x y)). Qed.
Lemma lem1502515 (x : real) : (term21 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1502514 x y)). Qed.
Lemma lem1502516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502517 (x : real) : (term22 x) = (term99 x).
Proof. exact (MK_COMB (@lem1502516) (@lem1502515 x)). Qed.
Lemma lem1502518 : term30 = term100.
Proof. exact (fun_ext (fun x : real => @lem1502517 x)). Qed.
Lemma lem1502519 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502520 : term31 = term101.
Proof. exact (MK_COMB (@lem1502519) (@lem1502518)). Qed.
Lemma lem1502521 : term23 = term101.
Proof. exact (TRANS (@lem1502355) (@lem1502520)). Qed.
Lemma lem1502531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1502532 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1502531 real P Q). Qed.
Lemma lem1502533 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1502532 (term108 x y) (term109 x y)). Qed.
Lemma lem1502534 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1502535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502536 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1502535) (@lem1502534 x y z)). Qed.
Lemma lem1502537 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1502538 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1502536 x y z) (@lem1502537 x y z)). Qed.
Lemma lem1502539 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1502538 x y z)). Qed.
Lemma lem1502540 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502541 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1502540) (@lem1502539 x y)). Qed.
Lemma lem1502542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502543 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1502542) (@lem1502541 x y)). Qed.
Lemma lem1502544 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1502545 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1502544 x y z)). Qed.
Lemma lem1502546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502547 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1502546) (@lem1502545 x y)). Qed.
Lemma lem1502548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502549 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1502548) (@lem1502547 x y)). Qed.
Lemma lem1502550 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1502551 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1502550 x y z)). Qed.
Lemma lem1502552 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502553 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1502552) (@lem1502551 x y)). Qed.
Lemma lem1502554 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1502549 x y) (@lem1502553 x y)). Qed.
Lemma lem1502555 (x : real) (y : real) : ((term106 x y) = (term107 x y)) = ((term97 x y) = (term125 x y)).
Proof. exact (MK_COMB (@lem1502543 x y) (@lem1502554 x y)). Qed.
Lemma lem1502556 (x : real) (y : real) : (term97 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1502555 x y) (@lem1502533 x y)). Qed.
Lemma lem1502653 (x : real) : (term98 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1502556 x y)). Qed.
Lemma lem1502654 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502655 (x : real) : (term99 x) = (term127 x).
Proof. exact (MK_COMB (@lem1502654) (@lem1502653 x)). Qed.
Lemma lem1502657 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1502658 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1502657 real P Q). Qed.
Lemma lem1502659 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1502658 (term130 x) (term131 x)). Qed.
Lemma lem1502660 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1502661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502662 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1502661) (@lem1502660 x y)). Qed.
Lemma lem1502663 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1502664 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1502662 x y) (@lem1502663 x y)). Qed.
Lemma lem1502665 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1502664 x y)). Qed.
Lemma lem1502666 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502667 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1502666) (@lem1502665 x)). Qed.
Lemma lem1502668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502669 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1502668) (@lem1502667 x)). Qed.
Lemma lem1502670 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1502671 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1502670 x y)). Qed.
Lemma lem1502672 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502673 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1502672) (@lem1502671 x)). Qed.
Lemma lem1502674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502675 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1502674) (@lem1502673 x)). Qed.
Lemma lem1502676 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1502677 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1502676 x y)). Qed.
Lemma lem1502678 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502679 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1502678) (@lem1502677 x)). Qed.
Lemma lem1502680 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1502675 x) (@lem1502679 x)). Qed.
Lemma lem1502681 (x : real) : ((term128 x) = (term129 x)) = ((term127 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1502669 x) (@lem1502680 x)). Qed.
Lemma lem1502682 (x : real) : (term127 x) = (term147 x).
Proof. exact (EQ_MP (@lem1502681 x) (@lem1502659 x)). Qed.
Lemma lem1502787 (x : real) : (term99 x) = (term147 x).
Proof. exact (TRANS (@lem1502655 x) (@lem1502682 x)). Qed.
Lemma lem1502788 : term100 = term148.
Proof. exact (fun_ext (fun x : real => @lem1502787 x)). Qed.
Lemma lem1502789 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502790 : term101 = term149.
Proof. exact (MK_COMB (@lem1502789) (@lem1502788)). Qed.
Lemma lem1502792 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1502793 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1502792 real P Q). Qed.
Lemma lem1502794 : term150 = term151.
Proof. exact (@lem1502793 term152 term153). Qed.
Lemma lem1502795 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1502796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502797 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1502796) (@lem1502795 x)). Qed.
Lemma lem1502798 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1502799 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1502797 x) (@lem1502798 x)). Qed.
Lemma lem1502800 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1502799 x)). Qed.
Lemma lem1502801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502802 : term150 = term149.
Proof. exact (MK_COMB (@lem1502801) (@lem1502800)). Qed.
Lemma lem1502803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502804 : term159 = term160.
Proof. exact (MK_COMB (@lem1502803) (@lem1502802)). Qed.
Lemma lem1502805 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1502806 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1502805 x)). Qed.
Lemma lem1502807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502808 : term162 = term163.
Proof. exact (MK_COMB (@lem1502807) (@lem1502806)). Qed.
Lemma lem1502809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502810 : term164 = term165.
Proof. exact (MK_COMB (@lem1502809) (@lem1502808)). Qed.
Lemma lem1502811 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1502812 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1502811 x)). Qed.
Lemma lem1502813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502814 : term167 = term168.
Proof. exact (MK_COMB (@lem1502813) (@lem1502812)). Qed.
Lemma lem1502815 : term151 = term169.
Proof. exact (MK_COMB (@lem1502810) (@lem1502814)). Qed.
Lemma lem1502816 : (term150 = term151) = (term149 = term169).
Proof. exact (MK_COMB (@lem1502804) (@lem1502815)). Qed.
Lemma lem1502817 : term149 = term169.
Proof. exact (EQ_MP (@lem1502816) (@lem1502794)). Qed.
Lemma lem1502930 : term101 = term169.
Proof. exact (TRANS (@lem1502790) (@lem1502817)). Qed.
Lemma lem1502932 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1502933 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1502932 real P Q). Qed.
Lemma lem1502934 : term151 = term150.
Proof. exact (@lem1502933 term152 term153). Qed.
Lemma lem1502935 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1502936 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1502935 x)). Qed.
Lemma lem1502937 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502938 : term162 = term163.
Proof. exact (MK_COMB (@lem1502937) (@lem1502936)). Qed.
Lemma lem1502939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502940 : term164 = term165.
Proof. exact (MK_COMB (@lem1502939) (@lem1502938)). Qed.
Lemma lem1502941 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1502942 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1502941 x)). Qed.
Lemma lem1502943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502944 : term167 = term168.
Proof. exact (MK_COMB (@lem1502943) (@lem1502942)). Qed.
Lemma lem1502945 : term151 = term169.
Proof. exact (MK_COMB (@lem1502940) (@lem1502944)). Qed.
Lemma lem1502946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502947 : term170 = term171.
Proof. exact (MK_COMB (@lem1502946) (@lem1502945)). Qed.
Lemma lem1502948 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1502949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502950 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1502949) (@lem1502948 x)). Qed.
Lemma lem1502951 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1502952 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1502950 x) (@lem1502951 x)). Qed.
Lemma lem1502953 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1502952 x)). Qed.
Lemma lem1502954 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502955 : term150 = term149.
Proof. exact (MK_COMB (@lem1502954) (@lem1502953)). Qed.
Lemma lem1502956 : (term151 = term150) = (term169 = term149).
Proof. exact (MK_COMB (@lem1502947) (@lem1502955)). Qed.
Lemma lem1502957 : term169 = term149.
Proof. exact (EQ_MP (@lem1502956) (@lem1502934)). Qed.
Lemma lem1502959 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1502960 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1502959 real P Q). Qed.
Lemma lem1502961 (x : real) : (term129 x) = (term128 x).
Proof. exact (@lem1502960 (term130 x) (term131 x)). Qed.
Lemma lem1502962 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1502963 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1502962 x y)). Qed.
Lemma lem1502964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502965 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1502964) (@lem1502963 x)). Qed.
Lemma lem1502966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502967 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1502966) (@lem1502965 x)). Qed.
Lemma lem1502968 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1502969 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1502968 x y)). Qed.
Lemma lem1502970 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502971 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1502970) (@lem1502969 x)). Qed.
Lemma lem1502972 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1502967 x) (@lem1502971 x)). Qed.
Lemma lem1502973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502974 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1502973) (@lem1502972 x)). Qed.
Lemma lem1502975 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1502976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502977 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1502976) (@lem1502975 x y)). Qed.
Lemma lem1502978 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1502979 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1502977 x y) (@lem1502978 x y)). Qed.
Lemma lem1502980 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1502979 x y)). Qed.
Lemma lem1502981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502982 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1502981) (@lem1502980 x)). Qed.
Lemma lem1502983 (x : real) : ((term129 x) = (term128 x)) = ((term147 x) = (term127 x)).
Proof. exact (MK_COMB (@lem1502974 x) (@lem1502982 x)). Qed.
Lemma lem1502984 (x : real) : (term147 x) = (term127 x).
Proof. exact (EQ_MP (@lem1502983 x) (@lem1502961 x)). Qed.
Lemma lem1502986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1502987 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1502986 real P Q). Qed.
Lemma lem1502988 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1502987 (term108 x y) (term109 x y)). Qed.
Lemma lem1502989 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1502990 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1502989 x y z)). Qed.
Lemma lem1502991 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502992 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1502991) (@lem1502990 x y)). Qed.
Lemma lem1502993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1502994 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1502993) (@lem1502992 x y)). Qed.
Lemma lem1502995 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1502996 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1502995 x y z)). Qed.
Lemma lem1502997 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1502998 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1502997) (@lem1502996 x y)). Qed.
Lemma lem1502999 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1502994 x y) (@lem1502998 x y)). Qed.
Lemma lem1503000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1503001 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1503000) (@lem1502999 x y)). Qed.
Lemma lem1503002 (x : real) (y : real) (z : real) : (term110 x y z) = (term58 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1503003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503004 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1503003) (@lem1503002 x y z)). Qed.
Lemma lem1503005 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1503006 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1503004 x y z) (@lem1503005 x y z)). Qed.
Lemma lem1503007 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1503006 x y z)). Qed.
Lemma lem1503008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503009 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1503008) (@lem1503007 x y)). Qed.
Lemma lem1503010 (x : real) (y : real) : ((term107 x y) = (term106 x y)) = ((term125 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1503001 x y) (@lem1503009 x y)). Qed.
Lemma lem1503011 (x : real) (y : real) : (term125 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1503010 x y) (@lem1502988 x y)). Qed.
Lemma lem1503012 (x : real) : (term126 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1503011 x y)). Qed.
Lemma lem1503013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503014 (x : real) : (term127 x) = (term99 x).
Proof. exact (MK_COMB (@lem1503013) (@lem1503012 x)). Qed.
Lemma lem1503015 (x : real) : (term147 x) = (term99 x).
Proof. exact (TRANS (@lem1502984 x) (@lem1503014 x)). Qed.
Lemma lem1503016 : term148 = term100.
Proof. exact (fun_ext (fun x : real => @lem1503015 x)). Qed.
Lemma lem1503017 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503018 : term149 = term101.
Proof. exact (MK_COMB (@lem1503017) (@lem1503016)). Qed.
Lemma lem1503019 : term169 = term101.
Proof. exact (TRANS (@lem1502957) (@lem1503018)). Qed.
Lemma lem1503020 : term101 = term101.
Proof. exact (TRANS (@lem1502930) (@lem1503019)). Qed.
Lemma lem1503023 : term23 = term101.
Proof. exact (TRANS (@lem1502521) (@lem1503020)). Qed.
Lemma lem1503040 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1503041 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1503040 x y z)). Qed.
Lemma lem1503042 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503043 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1503042) (@lem1503041 x y)). Qed.
Lemma lem1503044 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1503043 x y)). Qed.
Lemma lem1503045 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503046 (x : real) : (term99 x) = (term99 x).
Proof. exact (MK_COMB (@lem1503045) (@lem1503044 x)). Qed.
Lemma lem1503047 : term100 = term100.
Proof. exact (fun_ext (fun x : real => @lem1503046 x)). Qed.
Lemma lem1503048 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503049 : term101 = term101.
Proof. exact (MK_COMB (@lem1503048) (@lem1503047)). Qed.
Lemma lem1503050 : term23 = term101.
Proof. exact (TRANS (@lem1503023) (@lem1503049)). Qed.
Lemma lem1503060 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1503061 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term58 x y z.
Proof. exact (h1). Qed.
Lemma lem1503062 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (proj2 (@lem1503061 x y z h1)). Qed.
Lemma lem1503063 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term46 x y z.
Proof. exact (proj1 (@lem1503061 x y z h1)). Qed.
Lemma lem1503065 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503066 : term177 = term178.
Proof. exact (@lem1503065 (NUMERAL 0) term73). Qed.
Lemma lem1503067 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1503068 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1503069 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1503068 h1) (fun h1 : term178 = True => @lem1503067)). Qed.
Lemma lem1503070 : term178 = True.
Proof. exact (EQ_MP (@lem1503069) (@lem1503067)). Qed.
Lemma lem1503071 : term177 = True.
Proof. exact (TRANS (@lem1503066) (@lem1503070)). Qed.
Lemma lem1503072 : True = term177.
Proof. exact (SYM (@lem1503071)). Qed.
Lemma lem1503073 : term177.
Proof. exact (EQ_MP (@lem1503072) (@lem0)). Qed.
Lemma lem1503074 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term180 x y z.
Proof. exact (conj (@lem1503073) (@lem1503062 x y z h1)). Qed.
Lemma lem1503076 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1503077 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1503076 term76 (term51 x y z)). Qed.
Lemma lem1503078 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term183 x y z.
Proof. exact (@lem1503077 x y z (@lem1503074 x y z h1)). Qed.
Lemma lem1503079 (x : real) (y : real) (z : real) : (term184 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1503080 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1503081 (x : real) (y : real) (z : real) : (term185 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1503080) (@lem1503079 x y z)). Qed.
Lemma lem1503082 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503083 (x : real) (y : real) (z : real) : (term183 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1503081 x y z) (@lem1503082)). Qed.
Lemma lem1503084 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1503083 x y z) (@lem1503078 x y z h1)). Qed.
Lemma lem1503086 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503087 : term177 = term178.
Proof. exact (@lem1503086 (NUMERAL 0) term73). Qed.
Lemma lem1503088 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1503089 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1503090 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1503089 h1) (fun h1 : term178 = True => @lem1503088)). Qed.
Lemma lem1503091 : term178 = True.
Proof. exact (EQ_MP (@lem1503090) (@lem1503088)). Qed.
Lemma lem1503092 : term177 = True.
Proof. exact (TRANS (@lem1503087) (@lem1503091)). Qed.
Lemma lem1503093 : True = term177.
Proof. exact (SYM (@lem1503092)). Qed.
Lemma lem1503094 : term177.
Proof. exact (EQ_MP (@lem1503093) (@lem0)). Qed.
Lemma lem1503095 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term186 x y z.
Proof. exact (conj (@lem1503094) (@lem1503063 x y z h1)). Qed.
Lemma lem1503097 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1503098 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1503097 term76 (term41 x y z)). Qed.
Lemma lem1503099 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term189 x y z.
Proof. exact (@lem1503098 x y z (@lem1503095 x y z h1)). Qed.
Lemma lem1503100 (x : real) (y : real) (z : real) : (term190 x y z) = (term41 x y z).
Proof. exact (@lem1483460 (term41 x y z)). Qed.
Lemma lem1503101 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503102 (x : real) (y : real) (z : real) : (term191 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1503101) (@lem1503100 x y z)). Qed.
Lemma lem1503103 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503104 (x : real) (y : real) (z : real) : (term189 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1503102 x y z) (@lem1503103)). Qed.
Lemma lem1503105 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term46 x y z.
Proof. exact (EQ_MP (@lem1503104 x y z) (@lem1503099 x y z h1)). Qed.
Lemma lem1503106 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term58 x y z.
Proof. exact (conj (@lem1503105 x y z h1) (@lem1503084 x y z h1)). Qed.
Lemma lem1503108 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1503109 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1503108 (term41 x y z) (term51 x y z)). Qed.
Lemma lem1503110 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term194 x y z.
Proof. exact (@lem1503109 x y z (@lem1503106 x y z h1)). Qed.
Lemma lem1503111 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term34 x) (term42 y z) (real_add y z)). Qed.
Lemma lem1503112 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term66 x). Qed.
Lemma lem1503114 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503115 : term200 = term45.
Proof. exact (@lem1503114 term73). Qed.
Lemma lem1503116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503117 : term201 = term202.
Proof. exact (MK_COMB (@lem1503116) (@lem1503115)). Qed.
Lemma lem1503118 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1503119 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1503117) (@lem1503118 x)). Qed.
Lemma lem1503120 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1503112 x) (@lem1503119 x)). Qed.
Lemma lem1503121 (x : real) : (term203 x) = term45.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1503122 (x : real) : (term197 x) = term45.
Proof. exact (TRANS (@lem1503120 x) (@lem1503121 x)). Qed.
Lemma lem1503123 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1503124 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1503123) (@lem1503122 x)). Qed.
Lemma lem1503125 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term34 y) y (term34 z) z). Qed.
Lemma lem1503126 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term66 y). Qed.
Lemma lem1503128 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503129 : term200 = term45.
Proof. exact (@lem1503128 term73). Qed.
Lemma lem1503130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503131 : term201 = term202.
Proof. exact (MK_COMB (@lem1503130) (@lem1503129)). Qed.
Lemma lem1503132 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1503133 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1503131) (@lem1503132 y)). Qed.
Lemma lem1503134 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1503126 y) (@lem1503133 y)). Qed.
Lemma lem1503135 (y : real) : (term203 y) = term45.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1503136 (y : real) : (term208 y) = term45.
Proof. exact (TRANS (@lem1503134 y) (@lem1503135 y)). Qed.
Lemma lem1503137 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1503138 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1503137) (@lem1503136 y)). Qed.
Lemma lem1503139 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483440 term66 z). Qed.
Lemma lem1503141 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503142 : term200 = term45.
Proof. exact (@lem1503141 term73). Qed.
Lemma lem1503143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503144 : term201 = term202.
Proof. exact (MK_COMB (@lem1503143) (@lem1503142)). Qed.
Lemma lem1503145 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1503146 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1503144) (@lem1503145 z)). Qed.
Lemma lem1503147 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1503139 z) (@lem1503146 z)). Qed.
Lemma lem1503148 (z : real) : (term203 z) = term45.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1503149 (z : real) : (term208 z) = term45.
Proof. exact (TRANS (@lem1503147 z) (@lem1503148 z)). Qed.
Lemma lem1503150 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1503138 y) (@lem1503149 z)). Qed.
Lemma lem1503151 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1503125 y z) (@lem1503150 y z)). Qed.
Lemma lem1503152 : term210 = term45.
Proof. exact (@lem1483448 term45). Qed.
Lemma lem1503153 (y : real) (z : real) : (term206 y z) = term45.
Proof. exact (TRANS (@lem1503151 y z) (@lem1503152)). Qed.
Lemma lem1503154 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1503124 x) (@lem1503153 y z)). Qed.
Lemma lem1503155 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1503111 x y z) (@lem1503154 x y z)). Qed.
Lemma lem1503156 : term210 = term45.
Proof. exact (@lem1483448 term45). Qed.
Lemma lem1503157 (x : real) (y : real) (z : real) : (term195 x y z) = term45.
Proof. exact (TRANS (@lem1503155 x y z) (@lem1503156)). Qed.
Lemma lem1503158 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503159 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1503158) (@lem1503157 x y z)). Qed.
Lemma lem1503160 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503161 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1503159 x y z) (@lem1503160)). Qed.
Lemma lem1503162 (x : real) (y : real) (z : real) (h1 : term58 x y z) : term213.
Proof. exact (EQ_MP (@lem1503161 x y z) (@lem1503110 x y z h1)). Qed.
Lemma lem1503164 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503165 : term213 = term214.
Proof. exact (@lem1503164 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1503166 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1503167 : term213 = False.
Proof. exact (TRANS (@lem1503165) (@lem1503166)). Qed.
Lemma lem1503168 (x : real) (y : real) (z : real) (h1 : term58 x y z) : False.
Proof. exact (EQ_MP (@lem1503167) (@lem1503162 x y z h1)). Qed.
Lemma lem1503169 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (h1). Qed.
Lemma lem1503170 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term46 x y z.
Proof. exact (proj2 (@lem1503169 x y z h1)). Qed.
Lemma lem1503171 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (proj1 (@lem1503169 x y z h1)). Qed.
Lemma lem1503173 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503174 : term177 = term178.
Proof. exact (@lem1503173 (NUMERAL 0) term73). Qed.
Lemma lem1503175 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1503176 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1503177 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1503176 h1) (fun h1 : term178 = True => @lem1503175)). Qed.
Lemma lem1503178 : term178 = True.
Proof. exact (EQ_MP (@lem1503177) (@lem1503175)). Qed.
Lemma lem1503179 : term177 = True.
Proof. exact (TRANS (@lem1503174) (@lem1503178)). Qed.
Lemma lem1503180 : True = term177.
Proof. exact (SYM (@lem1503179)). Qed.
Lemma lem1503181 : term177.
Proof. exact (EQ_MP (@lem1503180) (@lem0)). Qed.
Lemma lem1503182 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term180 x y z.
Proof. exact (conj (@lem1503181) (@lem1503171 x y z h1)). Qed.
Lemma lem1503184 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1503185 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1503184 term76 (term51 x y z)). Qed.
Lemma lem1503186 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term183 x y z.
Proof. exact (@lem1503185 x y z (@lem1503182 x y z h1)). Qed.
Lemma lem1503187 (x : real) (y : real) (z : real) : (term184 x y z) = (term51 x y z).
Proof. exact (@lem1483460 (term51 x y z)). Qed.
Lemma lem1503188 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1503189 (x : real) (y : real) (z : real) : (term185 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1503188) (@lem1503187 x y z)). Qed.
Lemma lem1503190 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503191 (x : real) (y : real) (z : real) : (term183 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1503189 x y z) (@lem1503190)). Qed.
Lemma lem1503192 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1503191 x y z) (@lem1503186 x y z h1)). Qed.
Lemma lem1503194 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503195 : term177 = term178.
Proof. exact (@lem1503194 (NUMERAL 0) term73). Qed.
Lemma lem1503196 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1503197 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1503198 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1503197 h1) (fun h1 : term178 = True => @lem1503196)). Qed.
Lemma lem1503199 : term178 = True.
Proof. exact (EQ_MP (@lem1503198) (@lem1503196)). Qed.
Lemma lem1503200 : term177 = True.
Proof. exact (TRANS (@lem1503195) (@lem1503199)). Qed.
Lemma lem1503201 : True = term177.
Proof. exact (SYM (@lem1503200)). Qed.
Lemma lem1503202 : term177.
Proof. exact (EQ_MP (@lem1503201) (@lem0)). Qed.
Lemma lem1503203 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term186 x y z.
Proof. exact (conj (@lem1503202) (@lem1503170 x y z h1)). Qed.
Lemma lem1503205 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1503206 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1503205 term76 (term41 x y z)). Qed.
Lemma lem1503207 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term189 x y z.
Proof. exact (@lem1503206 x y z (@lem1503203 x y z h1)). Qed.
Lemma lem1503208 (x : real) (y : real) (z : real) : (term190 x y z) = (term41 x y z).
Proof. exact (@lem1483460 (term41 x y z)). Qed.
Lemma lem1503209 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503210 (x : real) (y : real) (z : real) : (term191 x y z) = (term44 x y z).
Proof. exact (MK_COMB (@lem1503209) (@lem1503208 x y z)). Qed.
Lemma lem1503211 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503212 (x : real) (y : real) (z : real) : (term189 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1503210 x y z) (@lem1503211)). Qed.
Lemma lem1503213 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term46 x y z.
Proof. exact (EQ_MP (@lem1503212 x y z) (@lem1503207 x y z h1)). Qed.
Lemma lem1503214 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term58 x y z.
Proof. exact (conj (@lem1503213 x y z h1) (@lem1503192 x y z h1)). Qed.
Lemma lem1503216 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1503217 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1503216 (term41 x y z) (term51 x y z)). Qed.
Lemma lem1503218 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term194 x y z.
Proof. exact (@lem1503217 x y z (@lem1503214 x y z h1)). Qed.
Lemma lem1503219 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 x (term34 x) (term42 y z) (real_add y z)). Qed.
Lemma lem1503220 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483442 term66 x). Qed.
Lemma lem1503222 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503223 : term200 = term45.
Proof. exact (@lem1503222 term73). Qed.
Lemma lem1503224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503225 : term201 = term202.
Proof. exact (MK_COMB (@lem1503224) (@lem1503223)). Qed.
Lemma lem1503226 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1503227 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1503225) (@lem1503226 x)). Qed.
Lemma lem1503228 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1503220 x) (@lem1503227 x)). Qed.
Lemma lem1503229 (x : real) : (term203 x) = term45.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1503230 (x : real) : (term197 x) = term45.
Proof. exact (TRANS (@lem1503228 x) (@lem1503229 x)). Qed.
Lemma lem1503231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1503232 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1503231) (@lem1503230 x)). Qed.
Lemma lem1503233 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 (term34 y) y (term34 z) z). Qed.
Lemma lem1503234 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483440 term66 y). Qed.
Lemma lem1503236 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503237 : term200 = term45.
Proof. exact (@lem1503236 term73). Qed.
Lemma lem1503238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503239 : term201 = term202.
Proof. exact (MK_COMB (@lem1503238) (@lem1503237)). Qed.
Lemma lem1503240 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1503241 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1503239) (@lem1503240 y)). Qed.
Lemma lem1503242 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1503234 y) (@lem1503241 y)). Qed.
Lemma lem1503243 (y : real) : (term203 y) = term45.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1503244 (y : real) : (term208 y) = term45.
Proof. exact (TRANS (@lem1503242 y) (@lem1503243 y)). Qed.
Lemma lem1503245 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1503246 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1503245) (@lem1503244 y)). Qed.
Lemma lem1503247 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483440 term66 z). Qed.
Lemma lem1503249 (m : nat) : (term199 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1503250 : term200 = term45.
Proof. exact (@lem1503249 term73). Qed.
Lemma lem1503251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503252 : term201 = term202.
Proof. exact (MK_COMB (@lem1503251) (@lem1503250)). Qed.
Lemma lem1503253 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1503254 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1503252) (@lem1503253 z)). Qed.
Lemma lem1503255 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1503247 z) (@lem1503254 z)). Qed.
Lemma lem1503256 (z : real) : (term203 z) = term45.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1503257 (z : real) : (term208 z) = term45.
Proof. exact (TRANS (@lem1503255 z) (@lem1503256 z)). Qed.
Lemma lem1503258 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1503246 y) (@lem1503257 z)). Qed.
Lemma lem1503259 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1503233 y z) (@lem1503258 y z)). Qed.
Lemma lem1503260 : term210 = term45.
Proof. exact (@lem1483448 term45). Qed.
Lemma lem1503261 (y : real) (z : real) : (term206 y z) = term45.
Proof. exact (TRANS (@lem1503259 y z) (@lem1503260)). Qed.
Lemma lem1503262 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1503232 x) (@lem1503261 y z)). Qed.
Lemma lem1503263 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1503219 x y z) (@lem1503262 x y z)). Qed.
Lemma lem1503264 : term210 = term45.
Proof. exact (@lem1483448 term45). Qed.
Lemma lem1503265 (x : real) (y : real) (z : real) : (term195 x y z) = term45.
Proof. exact (TRANS (@lem1503263 x y z) (@lem1503264)). Qed.
Lemma lem1503266 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503267 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1503266) (@lem1503265 x y z)). Qed.
Lemma lem1503268 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1503269 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1503267 x y z) (@lem1503268)). Qed.
Lemma lem1503270 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term213.
Proof. exact (EQ_MP (@lem1503269 x y z) (@lem1503218 x y z h1)). Qed.
Lemma lem1503272 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1503273 : term213 = term214.
Proof. exact (@lem1503272 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1503274 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1503275 : term213 = False.
Proof. exact (TRANS (@lem1503273) (@lem1503274)). Qed.
Lemma lem1503276 (x : real) (y : real) (z : real) (h1 : term92 x y z) : False.
Proof. exact (EQ_MP (@lem1503275) (@lem1503270 x y z h1)). Qed.
Lemma lem1503277 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (or_elim (@lem1503060 x y z h1) (fun h0 : term58 x y z => @lem1503168 x y z h0) (fun h0 : term92 x y z => @lem1503276 x y z h0)). Qed.
Lemma lem1503279 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1503280 (x : real) (y : real) (z : real) (h1 : term95 x y z) : (term95 x y z) = False.
Proof. exact (prop_ext (fun h2 : term95 x y z => @lem1503277 x y z h1) (fun h2 : False => @lem1503279 x y z h1)). Qed.
Lemma lem1503281 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (EQ_MP (@lem1503280 x y z h1) (@lem1503279 x y z h1)). Qed.
Lemma lem1503282 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1503283 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (ex_elim (@lem1503282 x y h1) (fun z : real => fun h0 : term96 x y z => @lem1503281 x y z h0)). Qed.
Lemma lem1503284 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1503285 (x : real) (h1 : term99 x) : False.
Proof. exact (ex_elim (@lem1503284 x h1) (fun y : real => fun h0 : term98 x y => @lem1503283 x y h0)). Qed.
Lemma lem1503286 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1503287 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1503286 h1) (fun x : real => fun h0 : term100 x => @lem1503285 x h0)). Qed.
Lemma lem1503288 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1503289 (h1 : term23) : term101.
Proof. exact (EQ_MP (@lem1503050) (@lem1503288 h1)). Qed.
Lemma lem1503290 (h1 : term23) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1503287 h2) (fun h2 : False => @lem1503289 h1)). Qed.
Lemma lem1503291 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1503290 h1) (@lem1503289 h1)). Qed.
Lemma lem1503292 : term215.
Proof. exact (fun h0 : term23 => @lem1503291 h0). Qed.
Lemma lem1503293 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1503294 : term217.
Proof. exact (@lem1503293 (@lem1503292)). Qed.
