Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADDNEG2_term_abbrevs.
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
Lemma lem1503324 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1503325 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1503326 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1503325 (term8 x y)). Qed.
Lemma lem1503327 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1503328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1503329 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1503328) (@lem1503327 x z y)). Qed.
Lemma lem1503330 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1503329 x z y) (@lem1503324 x z y)). Qed.
Lemma lem1503331 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1503330 x z y)). Qed.
Lemma lem1503332 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503333 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1503332) (@lem1503331 x y)). Qed.
Lemma lem1503334 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1503326 x y) (@lem1503333 x y)). Qed.
Lemma lem1503335 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1503336 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1503335 (term16 x)). Qed.
Lemma lem1503337 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1503338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1503339 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1503338) (@lem1503337 x y)). Qed.
Lemma lem1503340 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1503339 x y) (@lem1503334 x y)). Qed.
Lemma lem1503341 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1503340 x y)). Qed.
Lemma lem1503342 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503343 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1503342) (@lem1503341 x)). Qed.
Lemma lem1503344 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1503336 x) (@lem1503343 x)). Qed.
Lemma lem1503345 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1503346 : term23 = term24.
Proof. exact (@lem1503345 term25). Qed.
Lemma lem1503347 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1503348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1503349 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1503348) (@lem1503347 x)). Qed.
Lemma lem1503350 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1503349 x) (@lem1503344 x)). Qed.
Lemma lem1503351 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1503350 x)). Qed.
Lemma lem1503352 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503353 : term24 = term31.
Proof. exact (MK_COMB (@lem1503352) (@lem1503351)). Qed.
Lemma lem1503355 : term23 = term31.
Proof. exact (TRANS (@lem1503346) (@lem1503353)). Qed.
Lemma lem1503372 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1503373 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1503372 x z y)). Qed.
Lemma lem1503374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503375 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1503374) (@lem1503373 x y)). Qed.
Lemma lem1503376 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1503375 x y)). Qed.
Lemma lem1503377 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503378 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1503377) (@lem1503376 x)). Qed.
Lemma lem1503379 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1503378 x)). Qed.
Lemma lem1503380 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503381 : term31 = term31.
Proof. exact (MK_COMB (@lem1503380) (@lem1503379)). Qed.
Lemma lem1503382 : term23 = term31.
Proof. exact (TRANS (@lem1503355) (@lem1503381)). Qed.
Lemma lem1503383 (z : real) (x : real) (y : real) : (term2 x y z) = (term32 z x y).
Proof. exact (@lem1483521 z (term33 x y)). Qed.
Lemma lem1503390 (y : real) : (real_neg y) = (term34 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1503393 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1503396 (x : real) (y : real) : (term33 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1503393 x) (@lem1503390 y)). Qed.
Lemma lem1503399 (z : real) : (real_sub z) = (real_sub z).
Proof. exact (eq_refl (real_sub z)). Qed.
Lemma lem1503400 (z : real) (x : real) (y : real) : (term36 z x y) = (term37 z x y).
Proof. exact (MK_COMB (@lem1503399 z) (@lem1503396 x y)). Qed.
Lemma lem1503401 (z : real) (x : real) (y : real) : (term37 z x y) = (term38 z x y).
Proof. exact (@lem1483519 z (term35 x y)). Qed.
Lemma lem1503402 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (@lem1483508 x term41 (term34 y)). Qed.
Lemma lem1503403 (y : real) : (term42 y) = (term43 y).
Proof. exact (@lem1483476 term41 term41 y). Qed.
Lemma lem1503405 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1503406 : term46 = term47.
Proof. exact (@lem1503405 term48 term48). Qed.
Lemma lem1503407 : (term49 = (BIT1 0)) = (term50 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1503408 : term50 = term48.
Proof. exact (EQ_MP (@lem1503407) (@lem940073)). Qed.
Lemma lem1503409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1503410 : term47 = term51.
Proof. exact (MK_COMB (@lem1503409) (@lem1503408)). Qed.
Lemma lem1503411 : term46 = term51.
Proof. exact (TRANS (@lem1503406) (@lem1503410)). Qed.
Lemma lem1503412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1503413 : term52 = term53.
Proof. exact (MK_COMB (@lem1503412) (@lem1503411)). Qed.
Lemma lem1503414 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1503415 (y : real) : (term43 y) = (term54 y).
Proof. exact (MK_COMB (@lem1503413) (@lem1503414 y)). Qed.
Lemma lem1503416 (y : real) : (term42 y) = (term54 y).
Proof. exact (TRANS (@lem1503403 y) (@lem1503415 y)). Qed.
Lemma lem1503417 (y : real) : (term54 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1503418 (y : real) : (term42 y) = y.
Proof. exact (TRANS (@lem1503416 y) (@lem1503417 y)). Qed.
Lemma lem1503421 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1503422 (x : real) (y : real) : (term40 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1503421 x) (@lem1503418 y)). Qed.
Lemma lem1503423 (x : real) (y : real) : (term39 x y) = (term56 x y).
Proof. exact (TRANS (@lem1503402 x y) (@lem1503422 x y)). Qed.
Lemma lem1503424 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1503425 (z : real) (x : real) (y : real) : (term38 z x y) = (term57 z x y).
Proof. exact (MK_COMB (@lem1503424 z) (@lem1503423 x y)). Qed.
Lemma lem1503426 (x : real) (z : real) (y : real) : (term57 z x y) = (term58 x z y).
Proof. exact (@lem1483484 (term34 x) z y). Qed.
Lemma lem1503427 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1503428 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1503429 (x : real) (y : real) (z : real) : (term58 x z y) = (term58 x y z).
Proof. exact (MK_COMB (@lem1503428 x) (@lem1503427 y z)). Qed.
Lemma lem1503430 (x : real) (y : real) (z : real) : (term57 z x y) = (term58 x y z).
Proof. exact (TRANS (@lem1503426 x z y) (@lem1503429 x y z)). Qed.
Lemma lem1503431 (x : real) (y : real) (z : real) : (term38 z x y) = (term58 x y z).
Proof. exact (TRANS (@lem1503425 z x y) (@lem1503430 x y z)). Qed.
Lemma lem1503432 (x : real) (y : real) (z : real) : (term37 z x y) = (term58 x y z).
Proof. exact (TRANS (@lem1503401 z x y) (@lem1503431 x y z)). Qed.
Lemma lem1503433 (x : real) (y : real) (z : real) : (term36 z x y) = (term58 x y z).
Proof. exact (TRANS (@lem1503400 z x y) (@lem1503432 x y z)). Qed.
Lemma lem1503434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503435 (x : real) (y : real) (z : real) : (term59 z x y) = (term60 x y z).
Proof. exact (MK_COMB (@lem1503434) (@lem1503433 x y z)). Qed.
Lemma lem1503436 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1503437 (x : real) (y : real) (z : real) : (term32 z x y) = (term62 x y z).
Proof. exact (MK_COMB (@lem1503435 x y z) (@lem1503436)). Qed.
Lemma lem1503438 (x : real) (y : real) (z : real) : (term2 x y z) = (term62 x y z).
Proof. exact (TRANS (@lem1503383 z x y) (@lem1503437 x y z)). Qed.
Lemma lem1503439 (x : real) (z : real) (y : real) : (term63 x z y) = (term64 x z y).
Proof. exact (@lem1483531 x (real_add z y)). Qed.
Lemma lem1503446 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1503449 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1503450 (x : real) (y : real) (z : real) : (term65 x z y) = (term65 x y z).
Proof. exact (MK_COMB (@lem1503449 x) (@lem1503446 y z)). Qed.
Lemma lem1503451 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1503458 (y : real) (z : real) : (term67 y z) = (term68 y z).
Proof. exact (@lem1483508 y term41 z). Qed.
Lemma lem1503459 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1503462 (x : real) (y : real) (z : real) : (term66 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1503459 x) (@lem1503458 y z)). Qed.
Lemma lem1503463 (x : real) (y : real) (z : real) : (term65 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1503451 x y z) (@lem1503462 x y z)). Qed.
Lemma lem1503464 (x : real) (y : real) (z : real) : (term65 x z y) = (term69 x y z).
Proof. exact (TRANS (@lem1503450 x y z) (@lem1503463 x y z)). Qed.
Lemma lem1503465 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1503466 (x : real) (y : real) (z : real) : (term70 x z y) = (term71 x y z).
Proof. exact (MK_COMB (@lem1503465) (@lem1503464 x y z)). Qed.
Lemma lem1503467 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1503468 (x : real) (y : real) (z : real) : (term64 x z y) = (term72 x y z).
Proof. exact (MK_COMB (@lem1503466 x y z) (@lem1503467)). Qed.
Lemma lem1503469 (x : real) (y : real) (z : real) : (term63 x z y) = (term72 x y z).
Proof. exact (TRANS (@lem1503439 x z y) (@lem1503468 x y z)). Qed.
Lemma lem1503470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1503471 (x : real) (y : real) (z : real) : (term73 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1503470) (@lem1503438 x y z)). Qed.
Lemma lem1503472 (x : real) (y : real) (z : real) : (term75 x z y) = (term76 x y z).
Proof. exact (MK_COMB (@lem1503471 x y z) (@lem1503469 x y z)). Qed.
Lemma lem1503473 (x : real) (y : real) (z : real) : (term77 x y z) = (term78 x y z).
Proof. exact (@lem1483531 (term33 x y) z). Qed.
Lemma lem1503474 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1503481 (y : real) : (real_neg y) = (term34 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1503484 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1503487 (x : real) (y : real) : (term33 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1503484 x) (@lem1503481 y)). Qed.
Lemma lem1503488 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1503489 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1503488) (@lem1503487 x y)). Qed.
Lemma lem1503490 (x : real) (y : real) (z : real) : (term81 x y z) = (term82 x y z).
Proof. exact (MK_COMB (@lem1503489 x y) (@lem1503474 z)). Qed.
Lemma lem1503491 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (@lem1483519 (term35 x y) z). Qed.
Lemma lem1503500 (x : real) (y : real) (z : real) : (term83 x y z) = (term69 x y z).
Proof. exact (@lem1483482 x (term34 y) (term34 z)). Qed.
Lemma lem1503501 (x : real) (y : real) (z : real) : (term82 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1503491 x y z) (@lem1503500 x y z)). Qed.
Lemma lem1503502 (x : real) (y : real) (z : real) : (term81 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1503490 x y z) (@lem1503501 x y z)). Qed.
Lemma lem1503503 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1503504 (x : real) (y : real) (z : real) : (term84 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1503503) (@lem1503502 x y z)). Qed.
Lemma lem1503505 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1503506 (x : real) (y : real) (z : real) : (term78 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1503504 x y z) (@lem1503505)). Qed.
Lemma lem1503507 (x : real) (y : real) (z : real) : (term77 x y z) = (term72 x y z).
Proof. exact (TRANS (@lem1503473 x y z) (@lem1503506 x y z)). Qed.
Lemma lem1503508 (z : real) (y : real) (x : real) : (term3 x z y) = (term85 z y x).
Proof. exact (@lem1483521 (real_add z y) x). Qed.
Lemma lem1503509 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1503516 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1503517 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1503518 (y : real) (z : real) : (term86 z y) = (term86 y z).
Proof. exact (MK_COMB (@lem1503517) (@lem1503516 y z)). Qed.
Lemma lem1503519 (y : real) (z : real) (x : real) : (term87 z y x) = (term87 y z x).
Proof. exact (MK_COMB (@lem1503518 y z) (@lem1503509 x)). Qed.
Lemma lem1503520 (y : real) (z : real) (x : real) : (term87 y z x) = (term88 y z x).
Proof. exact (@lem1483519 (real_add y z) x). Qed.
Lemma lem1503525 (x : real) (y : real) (z : real) : (term88 y z x) = (term58 x y z).
Proof. exact (@lem1483488 (term34 x) (real_add y z)). Qed.
Lemma lem1503526 (x : real) (y : real) (z : real) : (term87 y z x) = (term58 x y z).
Proof. exact (TRANS (@lem1503520 y z x) (@lem1503525 x y z)). Qed.
Lemma lem1503527 (x : real) (y : real) (z : real) : (term87 z y x) = (term58 x y z).
Proof. exact (TRANS (@lem1503519 y z x) (@lem1503526 x y z)). Qed.
Lemma lem1503528 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1503529 (x : real) (y : real) (z : real) : (term89 z y x) = (term60 x y z).
Proof. exact (MK_COMB (@lem1503528) (@lem1503527 x y z)). Qed.
Lemma lem1503530 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1503531 (x : real) (y : real) (z : real) : (term85 z y x) = (term62 x y z).
Proof. exact (MK_COMB (@lem1503529 x y z) (@lem1503530)). Qed.
Lemma lem1503532 (x : real) (y : real) (z : real) : (term3 x z y) = (term62 x y z).
Proof. exact (TRANS (@lem1503508 z y x) (@lem1503531 x y z)). Qed.
Lemma lem1503533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1503534 (x : real) (y : real) (z : real) : (term90 x y z) = (term91 x y z).
Proof. exact (MK_COMB (@lem1503533) (@lem1503507 x y z)). Qed.
Lemma lem1503535 (x : real) (y : real) (z : real) : (term92 x z y) = (term93 x y z).
Proof. exact (MK_COMB (@lem1503534 x y z) (@lem1503532 x y z)). Qed.
Lemma lem1503536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503537 (x : real) (y : real) (z : real) : (term94 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1503536) (@lem1503472 x y z)). Qed.
Lemma lem1503538 (x : real) (y : real) (z : real) : (term1 x z y) = (term96 x y z).
Proof. exact (MK_COMB (@lem1503537 x y z) (@lem1503535 x y z)). Qed.
Lemma lem1503539 (x : real) (y : real) : (term12 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1503538 x y z)). Qed.
Lemma lem1503540 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503541 (x : real) (y : real) : (term13 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1503540) (@lem1503539 x y)). Qed.
Lemma lem1503542 (x : real) : (term21 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1503541 x y)). Qed.
Lemma lem1503543 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503544 (x : real) : (term22 x) = (term100 x).
Proof. exact (MK_COMB (@lem1503543) (@lem1503542 x)). Qed.
Lemma lem1503545 : term30 = term101.
Proof. exact (fun_ext (fun x : real => @lem1503544 x)). Qed.
Lemma lem1503546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503547 : term31 = term102.
Proof. exact (MK_COMB (@lem1503546) (@lem1503545)). Qed.
Lemma lem1503548 : term23 = term102.
Proof. exact (TRANS (@lem1503382) (@lem1503547)). Qed.
Lemma lem1503558 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1503559 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1503558 real P Q). Qed.
Lemma lem1503560 (x : real) (y : real) : (term107 x y) = (term108 x y).
Proof. exact (@lem1503559 (term109 x y) (term110 x y)). Qed.
Lemma lem1503561 (x : real) (y : real) (z : real) : (term111 x y z) = (term76 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1503562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503563 (x : real) (y : real) (z : real) : (term112 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1503562) (@lem1503561 x y z)). Qed.
Lemma lem1503564 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1503565 (x : real) (y : real) (z : real) : (term114 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1503563 x y z) (@lem1503564 x y z)). Qed.
Lemma lem1503566 (x : real) (y : real) : (term115 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1503565 x y z)). Qed.
Lemma lem1503567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503568 (x : real) (y : real) : (term107 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1503567) (@lem1503566 x y)). Qed.
Lemma lem1503569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1503570 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1503569) (@lem1503568 x y)). Qed.
Lemma lem1503571 (x : real) (y : real) (z : real) : (term111 x y z) = (term76 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1503572 (x : real) (y : real) : (term118 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1503571 x y z)). Qed.
Lemma lem1503573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503574 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1503573) (@lem1503572 x y)). Qed.
Lemma lem1503575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503576 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1503575) (@lem1503574 x y)). Qed.
Lemma lem1503577 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1503578 (x : real) (y : real) : (term123 x y) = (term110 x y).
Proof. exact (fun_ext (fun z : real => @lem1503577 x y z)). Qed.
Lemma lem1503579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503580 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1503579) (@lem1503578 x y)). Qed.
Lemma lem1503581 (x : real) (y : real) : (term108 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1503576 x y) (@lem1503580 x y)). Qed.
Lemma lem1503582 (x : real) (y : real) : ((term107 x y) = (term108 x y)) = ((term98 x y) = (term126 x y)).
Proof. exact (MK_COMB (@lem1503570 x y) (@lem1503581 x y)). Qed.
Lemma lem1503583 (x : real) (y : real) : (term98 x y) = (term126 x y).
Proof. exact (EQ_MP (@lem1503582 x y) (@lem1503560 x y)). Qed.
Lemma lem1503680 (x : real) : (term99 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1503583 x y)). Qed.
Lemma lem1503681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503682 (x : real) : (term100 x) = (term128 x).
Proof. exact (MK_COMB (@lem1503681) (@lem1503680 x)). Qed.
Lemma lem1503684 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1503685 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1503684 real P Q). Qed.
Lemma lem1503686 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1503685 (term131 x) (term132 x)). Qed.
Lemma lem1503687 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1503688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503689 (x : real) (y : real) : (term134 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1503688) (@lem1503687 x y)). Qed.
Lemma lem1503690 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1503691 (x : real) (y : real) : (term136 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1503689 x y) (@lem1503690 x y)). Qed.
Lemma lem1503692 (x : real) : (term137 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1503691 x y)). Qed.
Lemma lem1503693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503694 (x : real) : (term129 x) = (term128 x).
Proof. exact (MK_COMB (@lem1503693) (@lem1503692 x)). Qed.
Lemma lem1503695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1503696 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1503695) (@lem1503694 x)). Qed.
Lemma lem1503697 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1503698 (x : real) : (term140 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1503697 x y)). Qed.
Lemma lem1503699 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503700 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1503699) (@lem1503698 x)). Qed.
Lemma lem1503701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503702 (x : real) : (term143 x) = (term144 x).
Proof. exact (MK_COMB (@lem1503701) (@lem1503700 x)). Qed.
Lemma lem1503703 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1503704 (x : real) : (term145 x) = (term132 x).
Proof. exact (fun_ext (fun y : real => @lem1503703 x y)). Qed.
Lemma lem1503705 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503706 (x : real) : (term146 x) = (term147 x).
Proof. exact (MK_COMB (@lem1503705) (@lem1503704 x)). Qed.
Lemma lem1503707 (x : real) : (term130 x) = (term148 x).
Proof. exact (MK_COMB (@lem1503702 x) (@lem1503706 x)). Qed.
Lemma lem1503708 (x : real) : ((term129 x) = (term130 x)) = ((term128 x) = (term148 x)).
Proof. exact (MK_COMB (@lem1503696 x) (@lem1503707 x)). Qed.
Lemma lem1503709 (x : real) : (term128 x) = (term148 x).
Proof. exact (EQ_MP (@lem1503708 x) (@lem1503686 x)). Qed.
Lemma lem1503814 (x : real) : (term100 x) = (term148 x).
Proof. exact (TRANS (@lem1503682 x) (@lem1503709 x)). Qed.
Lemma lem1503815 : term101 = term149.
Proof. exact (fun_ext (fun x : real => @lem1503814 x)). Qed.
Lemma lem1503816 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503817 : term102 = term150.
Proof. exact (MK_COMB (@lem1503816) (@lem1503815)). Qed.
Lemma lem1503819 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1503820 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1503819 real P Q). Qed.
Lemma lem1503821 : term151 = term152.
Proof. exact (@lem1503820 term153 term154). Qed.
Lemma lem1503822 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1503823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503824 (x : real) : (term156 x) = (term144 x).
Proof. exact (MK_COMB (@lem1503823) (@lem1503822 x)). Qed.
Lemma lem1503825 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1503826 (x : real) : (term158 x) = (term148 x).
Proof. exact (MK_COMB (@lem1503824 x) (@lem1503825 x)). Qed.
Lemma lem1503827 : term159 = term149.
Proof. exact (fun_ext (fun x : real => @lem1503826 x)). Qed.
Lemma lem1503828 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503829 : term151 = term150.
Proof. exact (MK_COMB (@lem1503828) (@lem1503827)). Qed.
Lemma lem1503830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1503831 : term160 = term161.
Proof. exact (MK_COMB (@lem1503830) (@lem1503829)). Qed.
Lemma lem1503832 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1503833 : term162 = term153.
Proof. exact (fun_ext (fun x : real => @lem1503832 x)). Qed.
Lemma lem1503834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503835 : term163 = term164.
Proof. exact (MK_COMB (@lem1503834) (@lem1503833)). Qed.
Lemma lem1503836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503837 : term165 = term166.
Proof. exact (MK_COMB (@lem1503836) (@lem1503835)). Qed.
Lemma lem1503838 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1503839 : term167 = term154.
Proof. exact (fun_ext (fun x : real => @lem1503838 x)). Qed.
Lemma lem1503840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503841 : term168 = term169.
Proof. exact (MK_COMB (@lem1503840) (@lem1503839)). Qed.
Lemma lem1503842 : term152 = term170.
Proof. exact (MK_COMB (@lem1503837) (@lem1503841)). Qed.
Lemma lem1503843 : (term151 = term152) = (term150 = term170).
Proof. exact (MK_COMB (@lem1503831) (@lem1503842)). Qed.
Lemma lem1503844 : term150 = term170.
Proof. exact (EQ_MP (@lem1503843) (@lem1503821)). Qed.
Lemma lem1503957 : term102 = term170.
Proof. exact (TRANS (@lem1503817) (@lem1503844)). Qed.
Lemma lem1503959 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1503960 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1503959 real P Q). Qed.
Lemma lem1503961 : term152 = term151.
Proof. exact (@lem1503960 term153 term154). Qed.
Lemma lem1503962 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1503963 : term162 = term153.
Proof. exact (fun_ext (fun x : real => @lem1503962 x)). Qed.
Lemma lem1503964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503965 : term163 = term164.
Proof. exact (MK_COMB (@lem1503964) (@lem1503963)). Qed.
Lemma lem1503966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503967 : term165 = term166.
Proof. exact (MK_COMB (@lem1503966) (@lem1503965)). Qed.
Lemma lem1503968 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1503969 : term167 = term154.
Proof. exact (fun_ext (fun x : real => @lem1503968 x)). Qed.
Lemma lem1503970 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503971 : term168 = term169.
Proof. exact (MK_COMB (@lem1503970) (@lem1503969)). Qed.
Lemma lem1503972 : term152 = term170.
Proof. exact (MK_COMB (@lem1503967) (@lem1503971)). Qed.
Lemma lem1503973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1503974 : term171 = term172.
Proof. exact (MK_COMB (@lem1503973) (@lem1503972)). Qed.
Lemma lem1503975 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1503976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503977 (x : real) : (term156 x) = (term144 x).
Proof. exact (MK_COMB (@lem1503976) (@lem1503975 x)). Qed.
Lemma lem1503978 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1503979 (x : real) : (term158 x) = (term148 x).
Proof. exact (MK_COMB (@lem1503977 x) (@lem1503978 x)). Qed.
Lemma lem1503980 : term159 = term149.
Proof. exact (fun_ext (fun x : real => @lem1503979 x)). Qed.
Lemma lem1503981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503982 : term151 = term150.
Proof. exact (MK_COMB (@lem1503981) (@lem1503980)). Qed.
Lemma lem1503983 : (term152 = term151) = (term170 = term150).
Proof. exact (MK_COMB (@lem1503974) (@lem1503982)). Qed.
Lemma lem1503984 : term170 = term150.
Proof. exact (EQ_MP (@lem1503983) (@lem1503961)). Qed.
Lemma lem1503986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1503987 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1503986 real P Q). Qed.
Lemma lem1503988 (x : real) : (term130 x) = (term129 x).
Proof. exact (@lem1503987 (term131 x) (term132 x)). Qed.
Lemma lem1503989 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1503990 (x : real) : (term140 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1503989 x y)). Qed.
Lemma lem1503991 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503992 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1503991) (@lem1503990 x)). Qed.
Lemma lem1503993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1503994 (x : real) : (term143 x) = (term144 x).
Proof. exact (MK_COMB (@lem1503993) (@lem1503992 x)). Qed.
Lemma lem1503995 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1503996 (x : real) : (term145 x) = (term132 x).
Proof. exact (fun_ext (fun y : real => @lem1503995 x y)). Qed.
Lemma lem1503997 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1503998 (x : real) : (term146 x) = (term147 x).
Proof. exact (MK_COMB (@lem1503997) (@lem1503996 x)). Qed.
Lemma lem1503999 (x : real) : (term130 x) = (term148 x).
Proof. exact (MK_COMB (@lem1503994 x) (@lem1503998 x)). Qed.
Lemma lem1504000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1504001 (x : real) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem1504000) (@lem1503999 x)). Qed.
Lemma lem1504002 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1504003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504004 (x : real) (y : real) : (term134 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1504003) (@lem1504002 x y)). Qed.
Lemma lem1504005 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1504006 (x : real) (y : real) : (term136 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1504004 x y) (@lem1504005 x y)). Qed.
Lemma lem1504007 (x : real) : (term137 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1504006 x y)). Qed.
Lemma lem1504008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504009 (x : real) : (term129 x) = (term128 x).
Proof. exact (MK_COMB (@lem1504008) (@lem1504007 x)). Qed.
Lemma lem1504010 (x : real) : ((term130 x) = (term129 x)) = ((term148 x) = (term128 x)).
Proof. exact (MK_COMB (@lem1504001 x) (@lem1504009 x)). Qed.
Lemma lem1504011 (x : real) : (term148 x) = (term128 x).
Proof. exact (EQ_MP (@lem1504010 x) (@lem1503988 x)). Qed.
Lemma lem1504013 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1504014 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1504013 real P Q). Qed.
Lemma lem1504015 (x : real) (y : real) : (term108 x y) = (term107 x y).
Proof. exact (@lem1504014 (term109 x y) (term110 x y)). Qed.
Lemma lem1504016 (x : real) (y : real) (z : real) : (term111 x y z) = (term76 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1504017 (x : real) (y : real) : (term118 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1504016 x y z)). Qed.
Lemma lem1504018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504019 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1504018) (@lem1504017 x y)). Qed.
Lemma lem1504020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504021 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1504020) (@lem1504019 x y)). Qed.
Lemma lem1504022 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1504023 (x : real) (y : real) : (term123 x y) = (term110 x y).
Proof. exact (fun_ext (fun z : real => @lem1504022 x y z)). Qed.
Lemma lem1504024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504025 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1504024) (@lem1504023 x y)). Qed.
Lemma lem1504026 (x : real) (y : real) : (term108 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1504021 x y) (@lem1504025 x y)). Qed.
Lemma lem1504027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1504028 (x : real) (y : real) : (term175 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1504027) (@lem1504026 x y)). Qed.
Lemma lem1504029 (x : real) (y : real) (z : real) : (term111 x y z) = (term76 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1504030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504031 (x : real) (y : real) (z : real) : (term112 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1504030) (@lem1504029 x y z)). Qed.
Lemma lem1504032 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1504033 (x : real) (y : real) (z : real) : (term114 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1504031 x y z) (@lem1504032 x y z)). Qed.
Lemma lem1504034 (x : real) (y : real) : (term115 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1504033 x y z)). Qed.
Lemma lem1504035 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504036 (x : real) (y : real) : (term107 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1504035) (@lem1504034 x y)). Qed.
Lemma lem1504037 (x : real) (y : real) : ((term108 x y) = (term107 x y)) = ((term126 x y) = (term98 x y)).
Proof. exact (MK_COMB (@lem1504028 x y) (@lem1504036 x y)). Qed.
Lemma lem1504038 (x : real) (y : real) : (term126 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem1504037 x y) (@lem1504015 x y)). Qed.
Lemma lem1504039 (x : real) : (term127 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1504038 x y)). Qed.
Lemma lem1504040 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504041 (x : real) : (term128 x) = (term100 x).
Proof. exact (MK_COMB (@lem1504040) (@lem1504039 x)). Qed.
Lemma lem1504042 (x : real) : (term148 x) = (term100 x).
Proof. exact (TRANS (@lem1504011 x) (@lem1504041 x)). Qed.
Lemma lem1504043 : term149 = term101.
Proof. exact (fun_ext (fun x : real => @lem1504042 x)). Qed.
Lemma lem1504044 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504045 : term150 = term102.
Proof. exact (MK_COMB (@lem1504044) (@lem1504043)). Qed.
Lemma lem1504046 : term170 = term102.
Proof. exact (TRANS (@lem1503984) (@lem1504045)). Qed.
Lemma lem1504047 : term102 = term102.
Proof. exact (TRANS (@lem1503957) (@lem1504046)). Qed.
Lemma lem1504050 : term23 = term102.
Proof. exact (TRANS (@lem1503548) (@lem1504047)). Qed.
Lemma lem1504067 (x : real) (y : real) (z : real) : (term96 x y z) = (term96 x y z).
Proof. exact (eq_refl (term96 x y z)). Qed.
Lemma lem1504068 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1504067 x y z)). Qed.
Lemma lem1504069 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504070 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1504069) (@lem1504068 x y)). Qed.
Lemma lem1504071 (x : real) : (term99 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1504070 x y)). Qed.
Lemma lem1504072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504073 (x : real) : (term100 x) = (term100 x).
Proof. exact (MK_COMB (@lem1504072) (@lem1504071 x)). Qed.
Lemma lem1504074 : term101 = term101.
Proof. exact (fun_ext (fun x : real => @lem1504073 x)). Qed.
Lemma lem1504075 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504076 : term102 = term102.
Proof. exact (MK_COMB (@lem1504075) (@lem1504074)). Qed.
Lemma lem1504077 : term23 = term102.
Proof. exact (TRANS (@lem1504050) (@lem1504076)). Qed.
Lemma lem1504087 (x : real) (y : real) (z : real) (h1 : term96 x y z) : term96 x y z.
Proof. exact (h1). Qed.
Lemma lem1504088 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term76 x y z.
Proof. exact (h1). Qed.
Lemma lem1504089 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term72 x y z.
Proof. exact (proj2 (@lem1504088 x y z h1)). Qed.
Lemma lem1504090 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term62 x y z.
Proof. exact (proj1 (@lem1504088 x y z h1)). Qed.
Lemma lem1504092 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504093 : term178 = term179.
Proof. exact (@lem1504092 (NUMERAL 0) term48). Qed.
Lemma lem1504094 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504095 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504096 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1504095 h1) (fun h1 : term179 = True => @lem1504094)). Qed.
Lemma lem1504097 : term179 = True.
Proof. exact (EQ_MP (@lem1504096) (@lem1504094)). Qed.
Lemma lem1504098 : term178 = True.
Proof. exact (TRANS (@lem1504093) (@lem1504097)). Qed.
Lemma lem1504099 : True = term178.
Proof. exact (SYM (@lem1504098)). Qed.
Lemma lem1504100 : term178.
Proof. exact (EQ_MP (@lem1504099) (@lem0)). Qed.
Lemma lem1504101 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term181 x y z.
Proof. exact (conj (@lem1504100) (@lem1504089 x y z h1)). Qed.
Lemma lem1504103 (x : real) (y : real) : term182 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1504104 (x : real) (y : real) (z : real) : term183 x y z.
Proof. exact (@lem1504103 term51 (term69 x y z)). Qed.
Lemma lem1504105 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term184 x y z.
Proof. exact (@lem1504104 x y z (@lem1504101 x y z h1)). Qed.
Lemma lem1504106 (x : real) (y : real) (z : real) : (term185 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1504107 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504108 (x : real) (y : real) (z : real) : (term186 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1504107) (@lem1504106 x y z)). Qed.
Lemma lem1504109 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504110 (x : real) (y : real) (z : real) : (term184 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1504108 x y z) (@lem1504109)). Qed.
Lemma lem1504111 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term72 x y z.
Proof. exact (EQ_MP (@lem1504110 x y z) (@lem1504105 x y z h1)). Qed.
Lemma lem1504113 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504114 : term178 = term179.
Proof. exact (@lem1504113 (NUMERAL 0) term48). Qed.
Lemma lem1504115 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504116 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504117 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1504116 h1) (fun h1 : term179 = True => @lem1504115)). Qed.
Lemma lem1504118 : term179 = True.
Proof. exact (EQ_MP (@lem1504117) (@lem1504115)). Qed.
Lemma lem1504119 : term178 = True.
Proof. exact (TRANS (@lem1504114) (@lem1504118)). Qed.
Lemma lem1504120 : True = term178.
Proof. exact (SYM (@lem1504119)). Qed.
Lemma lem1504121 : term178.
Proof. exact (EQ_MP (@lem1504120) (@lem0)). Qed.
Lemma lem1504122 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term187 x y z.
Proof. exact (conj (@lem1504121) (@lem1504090 x y z h1)). Qed.
Lemma lem1504124 (x : real) (y : real) : term188 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1504125 (x : real) (y : real) (z : real) : term189 x y z.
Proof. exact (@lem1504124 term51 (term58 x y z)). Qed.
Lemma lem1504126 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term190 x y z.
Proof. exact (@lem1504125 x y z (@lem1504122 x y z h1)). Qed.
Lemma lem1504127 (x : real) (y : real) (z : real) : (term191 x y z) = (term58 x y z).
Proof. exact (@lem1483460 (term58 x y z)). Qed.
Lemma lem1504128 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504129 (x : real) (y : real) (z : real) : (term192 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem1504128) (@lem1504127 x y z)). Qed.
Lemma lem1504130 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504131 (x : real) (y : real) (z : real) : (term190 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1504129 x y z) (@lem1504130)). Qed.
Lemma lem1504132 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term62 x y z.
Proof. exact (EQ_MP (@lem1504131 x y z) (@lem1504126 x y z h1)). Qed.
Lemma lem1504133 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term76 x y z.
Proof. exact (conj (@lem1504132 x y z h1) (@lem1504111 x y z h1)). Qed.
Lemma lem1504135 (x : real) (y : real) : term193 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1504136 (x : real) (y : real) (z : real) : term194 x y z.
Proof. exact (@lem1504135 (term58 x y z) (term69 x y z)). Qed.
Lemma lem1504137 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term195 x y z.
Proof. exact (@lem1504136 x y z (@lem1504133 x y z h1)). Qed.
Lemma lem1504138 (x : real) (y : real) (z : real) : (term196 x y z) = (term197 x y z).
Proof. exact (@lem1483480 (term34 x) x (real_add y z) (term68 y z)). Qed.
Lemma lem1504139 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1483440 term41 x). Qed.
Lemma lem1504141 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504142 : term201 = term61.
Proof. exact (@lem1504141 term48). Qed.
Lemma lem1504143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504144 : term202 = term203.
Proof. exact (MK_COMB (@lem1504143) (@lem1504142)). Qed.
Lemma lem1504145 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504146 (x : real) : (term199 x) = (term204 x).
Proof. exact (MK_COMB (@lem1504144) (@lem1504145 x)). Qed.
Lemma lem1504147 (x : real) : (term198 x) = (term204 x).
Proof. exact (TRANS (@lem1504139 x) (@lem1504146 x)). Qed.
Lemma lem1504148 (x : real) : (term204 x) = term61.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1504149 (x : real) : (term198 x) = term61.
Proof. exact (TRANS (@lem1504147 x) (@lem1504148 x)). Qed.
Lemma lem1504150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504151 (x : real) : (term205 x) = term206.
Proof. exact (MK_COMB (@lem1504150) (@lem1504149 x)). Qed.
Lemma lem1504152 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483480 y (term34 y) z (term34 z)). Qed.
Lemma lem1504153 (y : real) : (term209 y) = (term199 y).
Proof. exact (@lem1483442 term41 y). Qed.
Lemma lem1504155 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504156 : term201 = term61.
Proof. exact (@lem1504155 term48). Qed.
Lemma lem1504157 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504158 : term202 = term203.
Proof. exact (MK_COMB (@lem1504157) (@lem1504156)). Qed.
Lemma lem1504159 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504160 (y : real) : (term199 y) = (term204 y).
Proof. exact (MK_COMB (@lem1504158) (@lem1504159 y)). Qed.
Lemma lem1504161 (y : real) : (term209 y) = (term204 y).
Proof. exact (TRANS (@lem1504153 y) (@lem1504160 y)). Qed.
Lemma lem1504162 (y : real) : (term204 y) = term61.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1504163 (y : real) : (term209 y) = term61.
Proof. exact (TRANS (@lem1504161 y) (@lem1504162 y)). Qed.
Lemma lem1504164 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504165 (y : real) : (term210 y) = term206.
Proof. exact (MK_COMB (@lem1504164) (@lem1504163 y)). Qed.
Lemma lem1504166 (z : real) : (term209 z) = (term199 z).
Proof. exact (@lem1483442 term41 z). Qed.
Lemma lem1504168 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504169 : term201 = term61.
Proof. exact (@lem1504168 term48). Qed.
Lemma lem1504170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504171 : term202 = term203.
Proof. exact (MK_COMB (@lem1504170) (@lem1504169)). Qed.
Lemma lem1504172 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1504173 (z : real) : (term199 z) = (term204 z).
Proof. exact (MK_COMB (@lem1504171) (@lem1504172 z)). Qed.
Lemma lem1504174 (z : real) : (term209 z) = (term204 z).
Proof. exact (TRANS (@lem1504166 z) (@lem1504173 z)). Qed.
Lemma lem1504175 (z : real) : (term204 z) = term61.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1504176 (z : real) : (term209 z) = term61.
Proof. exact (TRANS (@lem1504174 z) (@lem1504175 z)). Qed.
Lemma lem1504177 (y : real) (z : real) : (term208 y z) = term211.
Proof. exact (MK_COMB (@lem1504165 y) (@lem1504176 z)). Qed.
Lemma lem1504178 (y : real) (z : real) : (term207 y z) = term211.
Proof. exact (TRANS (@lem1504152 y z) (@lem1504177 y z)). Qed.
Lemma lem1504179 : term211 = term61.
Proof. exact (@lem1483448 term61). Qed.
Lemma lem1504180 (y : real) (z : real) : (term207 y z) = term61.
Proof. exact (TRANS (@lem1504178 y z) (@lem1504179)). Qed.
Lemma lem1504181 (x : real) (y : real) (z : real) : (term197 x y z) = term211.
Proof. exact (MK_COMB (@lem1504151 x) (@lem1504180 y z)). Qed.
Lemma lem1504182 (x : real) (y : real) (z : real) : (term196 x y z) = term211.
Proof. exact (TRANS (@lem1504138 x y z) (@lem1504181 x y z)). Qed.
Lemma lem1504183 : term211 = term61.
Proof. exact (@lem1483448 term61). Qed.
Lemma lem1504184 (x : real) (y : real) (z : real) : (term196 x y z) = term61.
Proof. exact (TRANS (@lem1504182 x y z) (@lem1504183)). Qed.
Lemma lem1504185 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504186 (x : real) (y : real) (z : real) : (term212 x y z) = term213.
Proof. exact (MK_COMB (@lem1504185) (@lem1504184 x y z)). Qed.
Lemma lem1504187 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504188 (x : real) (y : real) (z : real) : (term195 x y z) = term214.
Proof. exact (MK_COMB (@lem1504186 x y z) (@lem1504187)). Qed.
Lemma lem1504189 (x : real) (y : real) (z : real) (h1 : term76 x y z) : term214.
Proof. exact (EQ_MP (@lem1504188 x y z) (@lem1504137 x y z h1)). Qed.
Lemma lem1504191 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504192 : term214 = term215.
Proof. exact (@lem1504191 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1504193 : term215 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1504194 : term214 = False.
Proof. exact (TRANS (@lem1504192) (@lem1504193)). Qed.
Lemma lem1504195 (x : real) (y : real) (z : real) (h1 : term76 x y z) : False.
Proof. exact (EQ_MP (@lem1504194) (@lem1504189 x y z h1)). Qed.
Lemma lem1504196 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term93 x y z.
Proof. exact (h1). Qed.
Lemma lem1504197 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term62 x y z.
Proof. exact (proj2 (@lem1504196 x y z h1)). Qed.
Lemma lem1504198 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term72 x y z.
Proof. exact (proj1 (@lem1504196 x y z h1)). Qed.
Lemma lem1504200 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504201 : term178 = term179.
Proof. exact (@lem1504200 (NUMERAL 0) term48). Qed.
Lemma lem1504202 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504203 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504204 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1504203 h1) (fun h1 : term179 = True => @lem1504202)). Qed.
Lemma lem1504205 : term179 = True.
Proof. exact (EQ_MP (@lem1504204) (@lem1504202)). Qed.
Lemma lem1504206 : term178 = True.
Proof. exact (TRANS (@lem1504201) (@lem1504205)). Qed.
Lemma lem1504207 : True = term178.
Proof. exact (SYM (@lem1504206)). Qed.
Lemma lem1504208 : term178.
Proof. exact (EQ_MP (@lem1504207) (@lem0)). Qed.
Lemma lem1504209 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term181 x y z.
Proof. exact (conj (@lem1504208) (@lem1504198 x y z h1)). Qed.
Lemma lem1504211 (x : real) (y : real) : term182 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1504212 (x : real) (y : real) (z : real) : term183 x y z.
Proof. exact (@lem1504211 term51 (term69 x y z)). Qed.
Lemma lem1504213 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term184 x y z.
Proof. exact (@lem1504212 x y z (@lem1504209 x y z h1)). Qed.
Lemma lem1504214 (x : real) (y : real) (z : real) : (term185 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1504215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504216 (x : real) (y : real) (z : real) : (term186 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1504215) (@lem1504214 x y z)). Qed.
Lemma lem1504217 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504218 (x : real) (y : real) (z : real) : (term184 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1504216 x y z) (@lem1504217)). Qed.
Lemma lem1504219 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term72 x y z.
Proof. exact (EQ_MP (@lem1504218 x y z) (@lem1504213 x y z h1)). Qed.
Lemma lem1504221 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504222 : term178 = term179.
Proof. exact (@lem1504221 (NUMERAL 0) term48). Qed.
Lemma lem1504223 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504224 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504225 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1504224 h1) (fun h1 : term179 = True => @lem1504223)). Qed.
Lemma lem1504226 : term179 = True.
Proof. exact (EQ_MP (@lem1504225) (@lem1504223)). Qed.
Lemma lem1504227 : term178 = True.
Proof. exact (TRANS (@lem1504222) (@lem1504226)). Qed.
Lemma lem1504228 : True = term178.
Proof. exact (SYM (@lem1504227)). Qed.
Lemma lem1504229 : term178.
Proof. exact (EQ_MP (@lem1504228) (@lem0)). Qed.
Lemma lem1504230 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term187 x y z.
Proof. exact (conj (@lem1504229) (@lem1504197 x y z h1)). Qed.
Lemma lem1504232 (x : real) (y : real) : term188 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1504233 (x : real) (y : real) (z : real) : term189 x y z.
Proof. exact (@lem1504232 term51 (term58 x y z)). Qed.
Lemma lem1504234 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term190 x y z.
Proof. exact (@lem1504233 x y z (@lem1504230 x y z h1)). Qed.
Lemma lem1504235 (x : real) (y : real) (z : real) : (term191 x y z) = (term58 x y z).
Proof. exact (@lem1483460 (term58 x y z)). Qed.
Lemma lem1504236 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504237 (x : real) (y : real) (z : real) : (term192 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem1504236) (@lem1504235 x y z)). Qed.
Lemma lem1504238 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504239 (x : real) (y : real) (z : real) : (term190 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1504237 x y z) (@lem1504238)). Qed.
Lemma lem1504240 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term62 x y z.
Proof. exact (EQ_MP (@lem1504239 x y z) (@lem1504234 x y z h1)). Qed.
Lemma lem1504241 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term76 x y z.
Proof. exact (conj (@lem1504240 x y z h1) (@lem1504219 x y z h1)). Qed.
Lemma lem1504243 (x : real) (y : real) : term193 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1504244 (x : real) (y : real) (z : real) : term194 x y z.
Proof. exact (@lem1504243 (term58 x y z) (term69 x y z)). Qed.
Lemma lem1504245 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term195 x y z.
Proof. exact (@lem1504244 x y z (@lem1504241 x y z h1)). Qed.
Lemma lem1504246 (x : real) (y : real) (z : real) : (term196 x y z) = (term197 x y z).
Proof. exact (@lem1483480 (term34 x) x (real_add y z) (term68 y z)). Qed.
Lemma lem1504247 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1483440 term41 x). Qed.
Lemma lem1504249 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504250 : term201 = term61.
Proof. exact (@lem1504249 term48). Qed.
Lemma lem1504251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504252 : term202 = term203.
Proof. exact (MK_COMB (@lem1504251) (@lem1504250)). Qed.
Lemma lem1504253 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504254 (x : real) : (term199 x) = (term204 x).
Proof. exact (MK_COMB (@lem1504252) (@lem1504253 x)). Qed.
Lemma lem1504255 (x : real) : (term198 x) = (term204 x).
Proof. exact (TRANS (@lem1504247 x) (@lem1504254 x)). Qed.
Lemma lem1504256 (x : real) : (term204 x) = term61.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1504257 (x : real) : (term198 x) = term61.
Proof. exact (TRANS (@lem1504255 x) (@lem1504256 x)). Qed.
Lemma lem1504258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504259 (x : real) : (term205 x) = term206.
Proof. exact (MK_COMB (@lem1504258) (@lem1504257 x)). Qed.
Lemma lem1504260 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483480 y (term34 y) z (term34 z)). Qed.
Lemma lem1504261 (y : real) : (term209 y) = (term199 y).
Proof. exact (@lem1483442 term41 y). Qed.
Lemma lem1504263 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504264 : term201 = term61.
Proof. exact (@lem1504263 term48). Qed.
Lemma lem1504265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504266 : term202 = term203.
Proof. exact (MK_COMB (@lem1504265) (@lem1504264)). Qed.
Lemma lem1504267 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504268 (y : real) : (term199 y) = (term204 y).
Proof. exact (MK_COMB (@lem1504266) (@lem1504267 y)). Qed.
Lemma lem1504269 (y : real) : (term209 y) = (term204 y).
Proof. exact (TRANS (@lem1504261 y) (@lem1504268 y)). Qed.
Lemma lem1504270 (y : real) : (term204 y) = term61.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1504271 (y : real) : (term209 y) = term61.
Proof. exact (TRANS (@lem1504269 y) (@lem1504270 y)). Qed.
Lemma lem1504272 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504273 (y : real) : (term210 y) = term206.
Proof. exact (MK_COMB (@lem1504272) (@lem1504271 y)). Qed.
Lemma lem1504274 (z : real) : (term209 z) = (term199 z).
Proof. exact (@lem1483442 term41 z). Qed.
Lemma lem1504276 (m : nat) : (term200 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504277 : term201 = term61.
Proof. exact (@lem1504276 term48). Qed.
Lemma lem1504278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504279 : term202 = term203.
Proof. exact (MK_COMB (@lem1504278) (@lem1504277)). Qed.
Lemma lem1504280 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1504281 (z : real) : (term199 z) = (term204 z).
Proof. exact (MK_COMB (@lem1504279) (@lem1504280 z)). Qed.
Lemma lem1504282 (z : real) : (term209 z) = (term204 z).
Proof. exact (TRANS (@lem1504274 z) (@lem1504281 z)). Qed.
Lemma lem1504283 (z : real) : (term204 z) = term61.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1504284 (z : real) : (term209 z) = term61.
Proof. exact (TRANS (@lem1504282 z) (@lem1504283 z)). Qed.
Lemma lem1504285 (y : real) (z : real) : (term208 y z) = term211.
Proof. exact (MK_COMB (@lem1504273 y) (@lem1504284 z)). Qed.
Lemma lem1504286 (y : real) (z : real) : (term207 y z) = term211.
Proof. exact (TRANS (@lem1504260 y z) (@lem1504285 y z)). Qed.
Lemma lem1504287 : term211 = term61.
Proof. exact (@lem1483448 term61). Qed.
Lemma lem1504288 (y : real) (z : real) : (term207 y z) = term61.
Proof. exact (TRANS (@lem1504286 y z) (@lem1504287)). Qed.
Lemma lem1504289 (x : real) (y : real) (z : real) : (term197 x y z) = term211.
Proof. exact (MK_COMB (@lem1504259 x) (@lem1504288 y z)). Qed.
Lemma lem1504290 (x : real) (y : real) (z : real) : (term196 x y z) = term211.
Proof. exact (TRANS (@lem1504246 x y z) (@lem1504289 x y z)). Qed.
Lemma lem1504291 : term211 = term61.
Proof. exact (@lem1483448 term61). Qed.
Lemma lem1504292 (x : real) (y : real) (z : real) : (term196 x y z) = term61.
Proof. exact (TRANS (@lem1504290 x y z) (@lem1504291)). Qed.
Lemma lem1504293 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504294 (x : real) (y : real) (z : real) : (term212 x y z) = term213.
Proof. exact (MK_COMB (@lem1504293) (@lem1504292 x y z)). Qed.
Lemma lem1504295 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1504296 (x : real) (y : real) (z : real) : (term195 x y z) = term214.
Proof. exact (MK_COMB (@lem1504294 x y z) (@lem1504295)). Qed.
Lemma lem1504297 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term214.
Proof. exact (EQ_MP (@lem1504296 x y z) (@lem1504245 x y z h1)). Qed.
Lemma lem1504299 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504300 : term214 = term215.
Proof. exact (@lem1504299 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1504301 : term215 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1504302 : term214 = False.
Proof. exact (TRANS (@lem1504300) (@lem1504301)). Qed.
Lemma lem1504303 (x : real) (y : real) (z : real) (h1 : term93 x y z) : False.
Proof. exact (EQ_MP (@lem1504302) (@lem1504297 x y z h1)). Qed.
Lemma lem1504304 (x : real) (y : real) (z : real) (h1 : term96 x y z) : False.
Proof. exact (or_elim (@lem1504087 x y z h1) (fun h0 : term76 x y z => @lem1504195 x y z h0) (fun h0 : term93 x y z => @lem1504303 x y z h0)). Qed.
Lemma lem1504306 (x : real) (y : real) (z : real) (h1 : term96 x y z) : term96 x y z.
Proof. exact (h1). Qed.
Lemma lem1504307 (x : real) (y : real) (z : real) (h1 : term96 x y z) : (term96 x y z) = False.
Proof. exact (prop_ext (fun h2 : term96 x y z => @lem1504304 x y z h1) (fun h2 : False => @lem1504306 x y z h1)). Qed.
Lemma lem1504308 (x : real) (y : real) (z : real) (h1 : term96 x y z) : False.
Proof. exact (EQ_MP (@lem1504307 x y z h1) (@lem1504306 x y z h1)). Qed.
Lemma lem1504309 (x : real) (y : real) (h1 : term98 x y) : term98 x y.
Proof. exact (h1). Qed.
Lemma lem1504310 (x : real) (y : real) (h1 : term98 x y) : False.
Proof. exact (ex_elim (@lem1504309 x y h1) (fun z : real => fun h0 : term97 x y z => @lem1504308 x y z h0)). Qed.
Lemma lem1504311 (x : real) (h1 : term100 x) : term100 x.
Proof. exact (h1). Qed.
Lemma lem1504312 (x : real) (h1 : term100 x) : False.
Proof. exact (ex_elim (@lem1504311 x h1) (fun y : real => fun h0 : term99 x y => @lem1504310 x y h0)). Qed.
Lemma lem1504313 (h1 : term102) : term102.
Proof. exact (h1). Qed.
Lemma lem1504314 (h1 : term102) : False.
Proof. exact (ex_elim (@lem1504313 h1) (fun x : real => fun h0 : term101 x => @lem1504312 x h0)). Qed.
Lemma lem1504315 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1504316 (h1 : term23) : term102.
Proof. exact (EQ_MP (@lem1504077) (@lem1504315 h1)). Qed.
Lemma lem1504317 (h1 : term23) : term102 = False.
Proof. exact (prop_ext (fun h2 : term102 => @lem1504314 h2) (fun h2 : False => @lem1504316 h1)). Qed.
Lemma lem1504318 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1504317 h1) (@lem1504316 h1)). Qed.
Lemma lem1504319 : term216.
Proof. exact (fun h0 : term23 => @lem1504318 h0). Qed.
Lemma lem1504320 : term217.
Proof. exact (@lem1386578 term218). Qed.
Lemma lem1504321 : term218.
Proof. exact (@lem1504320 (@lem1504319)). Qed.
