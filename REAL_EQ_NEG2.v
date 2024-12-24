Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_NEG2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1524327 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 ((real_neg x) = (real_neg y)) (x = y)). Qed.
Lemma lem1524328 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1524329 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1524328 (term6 x)). Qed.
Lemma lem1524330 (x : real) (y : real) : (term7 x y) = (((real_neg x) = (real_neg y)) = (x = y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1524331 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1524332 (x : real) (y : real) : (term8 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1524331) (@lem1524330 x y)). Qed.
Lemma lem1524333 (x : real) (y : real) : (term8 x y) = (term1 x y).
Proof. exact (TRANS (@lem1524332 x y) (@lem1524327 x y)). Qed.
Lemma lem1524334 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1524333 x y)). Qed.
Lemma lem1524335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524336 (x : real) : (term5 x) = (term11 x).
Proof. exact (MK_COMB (@lem1524335) (@lem1524334 x)). Qed.
Lemma lem1524337 (x : real) : (term4 x) = (term11 x).
Proof. exact (TRANS (@lem1524329 x) (@lem1524336 x)). Qed.
Lemma lem1524338 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1524339 : term12 = term13.
Proof. exact (@lem1524338 term14). Qed.
Lemma lem1524340 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1524341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1524342 (x : real) : (term17 x) = (term4 x).
Proof. exact (MK_COMB (@lem1524341) (@lem1524340 x)). Qed.
Lemma lem1524343 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1524342 x) (@lem1524337 x)). Qed.
Lemma lem1524344 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1524343 x)). Qed.
Lemma lem1524345 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524346 : term13 = term20.
Proof. exact (MK_COMB (@lem1524345) (@lem1524344)). Qed.
Lemma lem1524348 : term12 = term20.
Proof. exact (TRANS (@lem1524339) (@lem1524346)). Qed.
Lemma lem1524365 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1524366 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1524365 x y)). Qed.
Lemma lem1524367 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524368 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1524367) (@lem1524366 x)). Qed.
Lemma lem1524369 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1524368 x)). Qed.
Lemma lem1524370 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524371 : term20 = term20.
Proof. exact (MK_COMB (@lem1524370) (@lem1524369)). Qed.
Lemma lem1524372 : term12 = term20.
Proof. exact (TRANS (@lem1524348) (@lem1524371)). Qed.
Lemma lem1524373 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = ((term21 x y) = term22).
Proof. exact (@lem1483529 (real_neg x) (real_neg y)). Qed.
Lemma lem1524380 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1524387 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1524388 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1524389 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1524388) (@lem1524387 x)). Qed.
Lemma lem1524390 (x : real) (y : real) : (term21 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1524389 x) (@lem1524380 y)). Qed.
Lemma lem1524391 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (term23 x) (term23 y)). Qed.
Lemma lem1524392 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1524394 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1524395 : term33 = term34.
Proof. exact (@lem1524394 term35 term35). Qed.
Lemma lem1524396 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1524397 : term37 = term35.
Proof. exact (EQ_MP (@lem1524396) (@lem940073)). Qed.
Lemma lem1524398 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1524399 : term34 = term38.
Proof. exact (MK_COMB (@lem1524398) (@lem1524397)). Qed.
Lemma lem1524400 : term33 = term38.
Proof. exact (TRANS (@lem1524395) (@lem1524399)). Qed.
Lemma lem1524401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524402 : term39 = term40.
Proof. exact (MK_COMB (@lem1524401) (@lem1524400)). Qed.
Lemma lem1524403 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1524404 (y : real) : (term29 y) = (term41 y).
Proof. exact (MK_COMB (@lem1524402) (@lem1524403 y)). Qed.
Lemma lem1524405 (y : real) : (term28 y) = (term41 y).
Proof. exact (TRANS (@lem1524392 y) (@lem1524404 y)). Qed.
Lemma lem1524406 (y : real) : (term41 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1524407 (y : real) : (term28 y) = y.
Proof. exact (TRANS (@lem1524405 y) (@lem1524406 y)). Qed.
Lemma lem1524408 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1524411 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1524408 x) (@lem1524407 y)). Qed.
Lemma lem1524412 (x : real) (y : real) : (term26 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524391 x y) (@lem1524411 x y)). Qed.
Lemma lem1524413 (x : real) (y : real) : (term21 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524390 x y) (@lem1524412 x y)). Qed.
Lemma lem1524414 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1524415 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1524414) (@lem1524413 x y)). Qed.
Lemma lem1524416 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524417 (x : real) (y : real) : ((term21 x y) = term22) = ((term43 x y) = term22).
Proof. exact (MK_COMB (@lem1524415 x y) (@lem1524416)). Qed.
Lemma lem1524418 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = ((term43 x y) = term22).
Proof. exact (TRANS (@lem1524373 x y) (@lem1524417 x y)). Qed.
Lemma lem1524419 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem1483554 x y). Qed.
Lemma lem1524432 (x : real) (y : real) : (real_sub x y) = (term48 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1524433 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1524434 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1524433) (@lem1524432 x y)). Qed.
Lemma lem1524435 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (@lem1483512 (term48 x y)). Qed.
Lemma lem1524436 (x : real) (y : real) : (term51 x y) = (term27 x y).
Proof. exact (@lem1483508 x term30 (term23 y)). Qed.
Lemma lem1524437 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1524439 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1524440 : term33 = term34.
Proof. exact (@lem1524439 term35 term35). Qed.
Lemma lem1524441 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1524442 : term37 = term35.
Proof. exact (EQ_MP (@lem1524441) (@lem940073)). Qed.
Lemma lem1524443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1524444 : term34 = term38.
Proof. exact (MK_COMB (@lem1524443) (@lem1524442)). Qed.
Lemma lem1524445 : term33 = term38.
Proof. exact (TRANS (@lem1524440) (@lem1524444)). Qed.
Lemma lem1524446 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524447 : term39 = term40.
Proof. exact (MK_COMB (@lem1524446) (@lem1524445)). Qed.
Lemma lem1524448 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1524449 (y : real) : (term29 y) = (term41 y).
Proof. exact (MK_COMB (@lem1524447) (@lem1524448 y)). Qed.
Lemma lem1524450 (y : real) : (term28 y) = (term41 y).
Proof. exact (TRANS (@lem1524437 y) (@lem1524449 y)). Qed.
Lemma lem1524451 (y : real) : (term41 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1524452 (y : real) : (term28 y) = y.
Proof. exact (TRANS (@lem1524450 y) (@lem1524451 y)). Qed.
Lemma lem1524455 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1524456 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1524455 x) (@lem1524452 y)). Qed.
Lemma lem1524457 (x : real) (y : real) : (term51 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524436 x y) (@lem1524456 x y)). Qed.
Lemma lem1524458 (x : real) (y : real) : (term50 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524435 x y) (@lem1524457 x y)). Qed.
Lemma lem1524459 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1524460 (x : real) (y : real) : ((term49 x y) = (term50 x y)) = ((term49 x y) = (term43 x y)).
Proof. exact (MK_COMB (@lem1524459 x y) (@lem1524458 x y)). Qed.
Lemma lem1524461 (x : real) (y : real) : (term49 x y) = (term43 x y).
Proof. exact (EQ_MP (@lem1524460 x y) (@lem1524434 x y)). Qed.
Lemma lem1524462 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524463 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1524462) (@lem1524461 x y)). Qed.
Lemma lem1524464 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524465 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1524463 x y) (@lem1524464)). Qed.
Lemma lem1524466 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524467 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1524466) (@lem1524432 x y)). Qed.
Lemma lem1524468 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524469 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1524467 x y) (@lem1524468)). Qed.
Lemma lem1524470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524471 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1524470) (@lem1524469 x y)). Qed.
Lemma lem1524472 (x : real) (y : real) : (term47 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1524471 x y) (@lem1524465 x y)). Qed.
Lemma lem1524473 (x : real) (y : real) : (term46 x y) = (term63 x y).
Proof. exact (TRANS (@lem1524419 x y) (@lem1524472 x y)). Qed.
Lemma lem1524474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1524475 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1524474) (@lem1524418 x y)). Qed.
Lemma lem1524476 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1524475 x y) (@lem1524473 x y)). Qed.
Lemma lem1524477 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (@lem1483554 (real_neg x) (real_neg y)). Qed.
Lemma lem1524484 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1524491 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1524492 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1524493 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1524492) (@lem1524491 x)). Qed.
Lemma lem1524494 (x : real) (y : real) : (term21 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1524493 x) (@lem1524484 y)). Qed.
Lemma lem1524495 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (term23 x) (term23 y)). Qed.
Lemma lem1524496 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1524498 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1524499 : term33 = term34.
Proof. exact (@lem1524498 term35 term35). Qed.
Lemma lem1524500 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1524501 : term37 = term35.
Proof. exact (EQ_MP (@lem1524500) (@lem940073)). Qed.
Lemma lem1524502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1524503 : term34 = term38.
Proof. exact (MK_COMB (@lem1524502) (@lem1524501)). Qed.
Lemma lem1524504 : term33 = term38.
Proof. exact (TRANS (@lem1524499) (@lem1524503)). Qed.
Lemma lem1524505 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524506 : term39 = term40.
Proof. exact (MK_COMB (@lem1524505) (@lem1524504)). Qed.
Lemma lem1524507 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1524508 (y : real) : (term29 y) = (term41 y).
Proof. exact (MK_COMB (@lem1524506) (@lem1524507 y)). Qed.
Lemma lem1524509 (y : real) : (term28 y) = (term41 y).
Proof. exact (TRANS (@lem1524496 y) (@lem1524508 y)). Qed.
Lemma lem1524510 (y : real) : (term41 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1524511 (y : real) : (term28 y) = y.
Proof. exact (TRANS (@lem1524509 y) (@lem1524510 y)). Qed.
Lemma lem1524512 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1524515 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1524512 x) (@lem1524511 y)). Qed.
Lemma lem1524516 (x : real) (y : real) : (term26 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524495 x y) (@lem1524515 x y)). Qed.
Lemma lem1524517 (x : real) (y : real) : (term21 x y) = (term43 x y).
Proof. exact (TRANS (@lem1524494 x y) (@lem1524516 x y)). Qed.
Lemma lem1524518 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1524519 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1524518) (@lem1524517 x y)). Qed.
Lemma lem1524520 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (@lem1483512 (term43 x y)). Qed.
Lemma lem1524521 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483508 (term23 x) term30 y). Qed.
Lemma lem1524522 (y : real) : (term23 y) = (term23 y).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem1524523 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1524525 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1524526 : term33 = term34.
Proof. exact (@lem1524525 term35 term35). Qed.
Lemma lem1524527 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1524528 : term37 = term35.
Proof. exact (EQ_MP (@lem1524527) (@lem940073)). Qed.
Lemma lem1524529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1524530 : term34 = term38.
Proof. exact (MK_COMB (@lem1524529) (@lem1524528)). Qed.
Lemma lem1524531 : term33 = term38.
Proof. exact (TRANS (@lem1524526) (@lem1524530)). Qed.
Lemma lem1524532 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524533 : term39 = term40.
Proof. exact (MK_COMB (@lem1524532) (@lem1524531)). Qed.
Lemma lem1524534 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1524535 (x : real) : (term29 x) = (term41 x).
Proof. exact (MK_COMB (@lem1524533) (@lem1524534 x)). Qed.
Lemma lem1524536 (x : real) : (term28 x) = (term41 x).
Proof. exact (TRANS (@lem1524523 x) (@lem1524535 x)). Qed.
Lemma lem1524537 (x : real) : (term41 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1524538 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1524536 x) (@lem1524537 x)). Qed.
Lemma lem1524539 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524540 (x : real) : (term74 x) = (real_add x).
Proof. exact (MK_COMB (@lem1524539) (@lem1524538 x)). Qed.
Lemma lem1524541 (x : real) (y : real) : (term73 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1524540 x) (@lem1524522 y)). Qed.
Lemma lem1524542 (x : real) (y : real) : (term72 x y) = (term48 x y).
Proof. exact (TRANS (@lem1524521 x y) (@lem1524541 x y)). Qed.
Lemma lem1524543 (x : real) (y : real) : (term71 x y) = (term48 x y).
Proof. exact (TRANS (@lem1524520 x y) (@lem1524542 x y)). Qed.
Lemma lem1524544 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1524545 (x : real) (y : real) : ((term70 x y) = (term71 x y)) = ((term70 x y) = (term48 x y)).
Proof. exact (MK_COMB (@lem1524544 x y) (@lem1524543 x y)). Qed.
Lemma lem1524546 (x : real) (y : real) : (term70 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem1524545 x y) (@lem1524519 x y)). Qed.
Lemma lem1524547 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524548 (x : real) (y : real) : (term76 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1524547) (@lem1524546 x y)). Qed.
Lemma lem1524549 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524550 (x : real) (y : real) : (term77 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1524548 x y) (@lem1524549)). Qed.
Lemma lem1524551 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524552 (x : real) (y : real) : (term78 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1524551) (@lem1524517 x y)). Qed.
Lemma lem1524553 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524554 (x : real) (y : real) : (term79 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1524552 x y) (@lem1524553)). Qed.
Lemma lem1524555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524556 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1524555) (@lem1524554 x y)). Qed.
Lemma lem1524557 (x : real) (y : real) : (term69 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1524556 x y) (@lem1524550 x y)). Qed.
Lemma lem1524558 (x : real) (y : real) : (term68 x y) = (term82 x y).
Proof. exact (TRANS (@lem1524477 x y) (@lem1524557 x y)). Qed.
Lemma lem1524559 (x : real) (y : real) : (x = y) = ((real_sub x y) = term22).
Proof. exact (@lem1483529 x y). Qed.
Lemma lem1524572 (x : real) (y : real) : (real_sub x y) = (term48 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1524573 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1524574 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1524573) (@lem1524572 x y)). Qed.
Lemma lem1524575 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1524576 (x : real) (y : real) : ((real_sub x y) = term22) = ((term48 x y) = term22).
Proof. exact (MK_COMB (@lem1524574 x y) (@lem1524575)). Qed.
Lemma lem1524577 (x : real) (y : real) : (x = y) = ((term48 x y) = term22).
Proof. exact (TRANS (@lem1524559 x y) (@lem1524576 x y)). Qed.
Lemma lem1524578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1524579 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1524578) (@lem1524558 x y)). Qed.
Lemma lem1524580 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1524579 x y) (@lem1524577 x y)). Qed.
Lemma lem1524581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524582 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1524581) (@lem1524476 x y)). Qed.
Lemma lem1524583 (x : real) (y : real) : (term1 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1524582 x y) (@lem1524580 x y)). Qed.
Lemma lem1524584 (x : real) : (term10 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1524583 x y)). Qed.
Lemma lem1524585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524586 (x : real) : (term11 x) = (term93 x).
Proof. exact (MK_COMB (@lem1524585) (@lem1524584 x)). Qed.
Lemma lem1524587 : term19 = term94.
Proof. exact (fun_ext (fun x : real => @lem1524586 x)). Qed.
Lemma lem1524588 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524589 : term20 = term95.
Proof. exact (MK_COMB (@lem1524588) (@lem1524587)). Qed.
Lemma lem1524590 : term12 = term95.
Proof. exact (TRANS (@lem1524372) (@lem1524589)). Qed.
Lemma lem1524596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1524597 (P : real -> Prop) (Q : real -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem1524596 real P Q). Qed.
Lemma lem1524598 (x : real) : (term100 x) = (term101 x).
Proof. exact (@lem1524597 (term102 x) (term103 x)). Qed.
Lemma lem1524599 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1524600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524601 (x : real) (y : real) : (term105 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1524600) (@lem1524599 x y)). Qed.
Lemma lem1524602 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1524603 (x : real) (y : real) : (term107 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1524601 x y) (@lem1524602 x y)). Qed.
Lemma lem1524604 (x : real) : (term108 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1524603 x y)). Qed.
Lemma lem1524605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524606 (x : real) : (term100 x) = (term93 x).
Proof. exact (MK_COMB (@lem1524605) (@lem1524604 x)). Qed.
Lemma lem1524607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1524608 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1524607) (@lem1524606 x)). Qed.
Lemma lem1524609 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1524610 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1524609 x y)). Qed.
Lemma lem1524611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524612 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1524611) (@lem1524610 x)). Qed.
Lemma lem1524613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524614 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1524613) (@lem1524612 x)). Qed.
Lemma lem1524615 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1524616 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1524615 x y)). Qed.
Lemma lem1524617 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524618 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1524617) (@lem1524616 x)). Qed.
Lemma lem1524619 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1524614 x) (@lem1524618 x)). Qed.
Lemma lem1524620 (x : real) : ((term100 x) = (term101 x)) = ((term93 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1524608 x) (@lem1524619 x)). Qed.
Lemma lem1524621 (x : real) : (term93 x) = (term119 x).
Proof. exact (EQ_MP (@lem1524620 x) (@lem1524598 x)). Qed.
Lemma lem1524718 : term94 = term120.
Proof. exact (fun_ext (fun x : real => @lem1524621 x)). Qed.
Lemma lem1524719 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524720 : term95 = term121.
Proof. exact (MK_COMB (@lem1524719) (@lem1524718)). Qed.
Lemma lem1524722 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1524723 (P : real -> Prop) (Q : real -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem1524722 real P Q). Qed.
Lemma lem1524724 : term122 = term123.
Proof. exact (@lem1524723 term124 term125). Qed.
Lemma lem1524725 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1524726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524727 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1524726) (@lem1524725 x)). Qed.
Lemma lem1524728 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1524729 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1524727 x) (@lem1524728 x)). Qed.
Lemma lem1524730 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1524729 x)). Qed.
Lemma lem1524731 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524732 : term122 = term121.
Proof. exact (MK_COMB (@lem1524731) (@lem1524730)). Qed.
Lemma lem1524733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1524734 : term131 = term132.
Proof. exact (MK_COMB (@lem1524733) (@lem1524732)). Qed.
Lemma lem1524735 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1524736 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1524735 x)). Qed.
Lemma lem1524737 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524738 : term134 = term135.
Proof. exact (MK_COMB (@lem1524737) (@lem1524736)). Qed.
Lemma lem1524739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524740 : term136 = term137.
Proof. exact (MK_COMB (@lem1524739) (@lem1524738)). Qed.
Lemma lem1524741 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1524742 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1524741 x)). Qed.
Lemma lem1524743 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524744 : term139 = term140.
Proof. exact (MK_COMB (@lem1524743) (@lem1524742)). Qed.
Lemma lem1524745 : term123 = term141.
Proof. exact (MK_COMB (@lem1524740) (@lem1524744)). Qed.
Lemma lem1524746 : (term122 = term123) = (term121 = term141).
Proof. exact (MK_COMB (@lem1524734) (@lem1524745)). Qed.
Lemma lem1524747 : term121 = term141.
Proof. exact (EQ_MP (@lem1524746) (@lem1524724)). Qed.
Lemma lem1524852 : term95 = term141.
Proof. exact (TRANS (@lem1524720) (@lem1524747)). Qed.
Lemma lem1524854 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term96 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1524855 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term98 P Q).
Proof. exact (@lem1524854 real P Q). Qed.
Lemma lem1524856 : term123 = term122.
Proof. exact (@lem1524855 term124 term125). Qed.
Lemma lem1524857 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1524858 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1524857 x)). Qed.
Lemma lem1524859 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524860 : term134 = term135.
Proof. exact (MK_COMB (@lem1524859) (@lem1524858)). Qed.
Lemma lem1524861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524862 : term136 = term137.
Proof. exact (MK_COMB (@lem1524861) (@lem1524860)). Qed.
Lemma lem1524863 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1524864 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1524863 x)). Qed.
Lemma lem1524865 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524866 : term139 = term140.
Proof. exact (MK_COMB (@lem1524865) (@lem1524864)). Qed.
Lemma lem1524867 : term123 = term141.
Proof. exact (MK_COMB (@lem1524862) (@lem1524866)). Qed.
Lemma lem1524868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1524869 : term142 = term143.
Proof. exact (MK_COMB (@lem1524868) (@lem1524867)). Qed.
Lemma lem1524870 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1524871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524872 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1524871) (@lem1524870 x)). Qed.
Lemma lem1524873 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1524874 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1524872 x) (@lem1524873 x)). Qed.
Lemma lem1524875 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1524874 x)). Qed.
Lemma lem1524876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524877 : term122 = term121.
Proof. exact (MK_COMB (@lem1524876) (@lem1524875)). Qed.
Lemma lem1524878 : (term123 = term122) = (term141 = term121).
Proof. exact (MK_COMB (@lem1524869) (@lem1524877)). Qed.
Lemma lem1524879 : term141 = term121.
Proof. exact (EQ_MP (@lem1524878) (@lem1524856)). Qed.
Lemma lem1524881 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term96 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1524882 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term98 P Q).
Proof. exact (@lem1524881 real P Q). Qed.
Lemma lem1524883 (x : real) : (term101 x) = (term100 x).
Proof. exact (@lem1524882 (term102 x) (term103 x)). Qed.
Lemma lem1524884 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1524885 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1524884 x y)). Qed.
Lemma lem1524886 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524887 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1524886) (@lem1524885 x)). Qed.
Lemma lem1524888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524889 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1524888) (@lem1524887 x)). Qed.
Lemma lem1524890 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1524891 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1524890 x y)). Qed.
Lemma lem1524892 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524893 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1524892) (@lem1524891 x)). Qed.
Lemma lem1524894 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1524889 x) (@lem1524893 x)). Qed.
Lemma lem1524895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1524896 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1524895) (@lem1524894 x)). Qed.
Lemma lem1524897 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1524898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524899 (x : real) (y : real) : (term105 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1524898) (@lem1524897 x y)). Qed.
Lemma lem1524900 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1524901 (x : real) (y : real) : (term107 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1524899 x y) (@lem1524900 x y)). Qed.
Lemma lem1524902 (x : real) : (term108 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1524901 x y)). Qed.
Lemma lem1524903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524904 (x : real) : (term100 x) = (term93 x).
Proof. exact (MK_COMB (@lem1524903) (@lem1524902 x)). Qed.
Lemma lem1524905 (x : real) : ((term101 x) = (term100 x)) = ((term119 x) = (term93 x)).
Proof. exact (MK_COMB (@lem1524896 x) (@lem1524904 x)). Qed.
Lemma lem1524906 (x : real) : (term119 x) = (term93 x).
Proof. exact (EQ_MP (@lem1524905 x) (@lem1524883 x)). Qed.
Lemma lem1524907 : term120 = term94.
Proof. exact (fun_ext (fun x : real => @lem1524906 x)). Qed.
Lemma lem1524908 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524909 : term121 = term95.
Proof. exact (MK_COMB (@lem1524908) (@lem1524907)). Qed.
Lemma lem1524910 : term141 = term95.
Proof. exact (TRANS (@lem1524879) (@lem1524909)). Qed.
Lemma lem1524911 : term95 = term95.
Proof. exact (TRANS (@lem1524852) (@lem1524910)). Qed.
Lemma lem1524914 : term12 = term95.
Proof. exact (TRANS (@lem1524590) (@lem1524911)). Qed.
Lemma lem1524931 (x : real) (y : real) : (term88 x y) = (term146 x y).
Proof. exact (@lem19367 (term56 x y) (term60 x y) ((term48 x y) = term22)). Qed.
Lemma lem1524948 (x : real) (y : real) : (term67 x y) = (term147 x y).
Proof. exact (@lem19158 (term60 x y) ((term43 x y) = term22) (term56 x y)). Qed.
Lemma lem1524949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524950 (x : real) (y : real) : (term90 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1524949) (@lem1524948 x y)). Qed.
Lemma lem1524951 (x : real) (y : real) : (term91 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1524950 x y) (@lem1524931 x y)). Qed.
Lemma lem1524952 (x : real) : (term92 x) = (term150 x).
Proof. exact (fun_ext (fun y : real => @lem1524951 x y)). Qed.
Lemma lem1524953 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524954 (x : real) : (term93 x) = (term151 x).
Proof. exact (MK_COMB (@lem1524953) (@lem1524952 x)). Qed.
Lemma lem1524955 : term94 = term152.
Proof. exact (fun_ext (fun x : real => @lem1524954 x)). Qed.
Lemma lem1524956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524957 : term95 = term153.
Proof. exact (MK_COMB (@lem1524956) (@lem1524955)). Qed.
Lemma lem1524958 : term12 = term153.
Proof. exact (TRANS (@lem1524914) (@lem1524957)). Qed.
Lemma lem1524980 (x : real) (y : real) (h1 : term149 x y) : term149 x y.
Proof. exact (h1). Qed.
Lemma lem1524981 (x : real) (y : real) (h1 : term147 x y) : term147 x y.
Proof. exact (h1). Qed.
Lemma lem1524982 (x : real) (y : real) (h1 : term154 x y) : term154 x y.
Proof. exact (h1). Qed.
Lemma lem1524983 (x : real) (y : real) (h1 : term154 x y) : term60 x y.
Proof. exact (proj2 (@lem1524982 x y h1)). Qed.
Lemma lem1524984 (x : real) (y : real) (h1 : term154 x y) : (term43 x y) = term22.
Proof. exact (proj1 (@lem1524982 x y h1)). Qed.
Lemma lem1524986 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1524987 : term156 = term157.
Proof. exact (@lem1524986 (NUMERAL 0) term35). Qed.
Lemma lem1524988 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1524989 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1524990 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1524989 h1) (fun h1 : term157 = True => @lem1524988)). Qed.
Lemma lem1524991 : term157 = True.
Proof. exact (EQ_MP (@lem1524990) (@lem1524988)). Qed.
Lemma lem1524992 : term156 = True.
Proof. exact (TRANS (@lem1524987) (@lem1524991)). Qed.
Lemma lem1524993 : True = term156.
Proof. exact (SYM (@lem1524992)). Qed.
Lemma lem1524994 : term156.
Proof. exact (EQ_MP (@lem1524993) (@lem0)). Qed.
Lemma lem1524995 (x : real) (y : real) (h1 : term154 x y) : term159 x y.
Proof. exact (conj (@lem1524994) (@lem1524983 x y h1)). Qed.
Lemma lem1524997 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1524998 (x : real) (y : real) : term161 x y.
Proof. exact (@lem1524997 term38 (term48 x y)). Qed.
Lemma lem1524999 (x : real) (y : real) (h1 : term154 x y) : term162 x y.
Proof. exact (@lem1524998 x y (@lem1524995 x y h1)). Qed.
Lemma lem1525000 (x : real) (y : real) : (term163 x y) = (term48 x y).
Proof. exact (@lem1483460 (term48 x y)). Qed.
Lemma lem1525001 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525002 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1525001) (@lem1525000 x y)). Qed.
Lemma lem1525003 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525004 (x : real) (y : real) : (term162 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1525002 x y) (@lem1525003)). Qed.
Lemma lem1525005 (x : real) (y : real) (h1 : term154 x y) : term60 x y.
Proof. exact (EQ_MP (@lem1525004 x y) (@lem1524999 x y h1)). Qed.
Lemma lem1525007 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1525008 (x : real) (y : real) : term166 x y.
Proof. exact (@lem1525007 (term43 x y)). Qed.
Lemma lem1525009 (x : real) (y : real) (h1 : term154 x y) : term167 x y.
Proof. exact (@lem1525008 x y (@lem1524984 x y h1)). Qed.
Lemma lem1525010 (x : real) (y : real) (h1 : term154 x y) : term168 x y.
Proof. exact (@lem1525009 x y h1 term38). Qed.
Lemma lem1525011 (x : real) (y : real) : (term168 x y) = ((term169 x y) = term22).
Proof. exact (eq_refl (term168 x y)). Qed.
Lemma lem1525012 (x : real) (y : real) (h1 : term154 x y) : (term169 x y) = term22.
Proof. exact (EQ_MP (@lem1525011 x y) (@lem1525010 x y h1)). Qed.
Lemma lem1525013 (x : real) (y : real) : (term169 x y) = (term43 x y).
Proof. exact (@lem1483460 (term43 x y)). Qed.
Lemma lem1525014 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1525015 (x : real) (y : real) : (term170 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1525014) (@lem1525013 x y)). Qed.
Lemma lem1525016 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525017 (x : real) (y : real) : ((term169 x y) = term22) = ((term43 x y) = term22).
Proof. exact (MK_COMB (@lem1525015 x y) (@lem1525016)). Qed.
Lemma lem1525018 (x : real) (y : real) (h1 : term154 x y) : (term43 x y) = term22.
Proof. exact (EQ_MP (@lem1525017 x y) (@lem1525012 x y h1)). Qed.
Lemma lem1525019 (x : real) (y : real) (h1 : term154 x y) : term154 x y.
Proof. exact (conj (@lem1525018 x y h1) (@lem1525005 x y h1)). Qed.
Lemma lem1525021 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1525022 (x : real) (y : real) : term172 x y.
Proof. exact (@lem1525021 (term43 x y) (term48 x y)). Qed.
Lemma lem1525023 (x : real) (y : real) (h1 : term154 x y) : term173 x y.
Proof. exact (@lem1525022 x y (@lem1525019 x y h1)). Qed.
Lemma lem1525024 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483480 (term23 x) x y (term23 y)). Qed.
Lemma lem1525025 (x : real) : (term176 x) = (term177 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1525027 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525028 : term179 = term22.
Proof. exact (@lem1525027 term35). Qed.
Lemma lem1525029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525030 : term180 = term181.
Proof. exact (MK_COMB (@lem1525029) (@lem1525028)). Qed.
Lemma lem1525031 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525032 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1525030) (@lem1525031 x)). Qed.
Lemma lem1525033 (x : real) : (term176 x) = (term182 x).
Proof. exact (TRANS (@lem1525025 x) (@lem1525032 x)). Qed.
Lemma lem1525034 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1525035 (x : real) : (term176 x) = term22.
Proof. exact (TRANS (@lem1525033 x) (@lem1525034 x)). Qed.
Lemma lem1525036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1525037 (x : real) : (term183 x) = term184.
Proof. exact (MK_COMB (@lem1525036) (@lem1525035 x)). Qed.
Lemma lem1525038 (y : real) : (term185 y) = (term177 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1525040 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525041 : term179 = term22.
Proof. exact (@lem1525040 term35). Qed.
Lemma lem1525042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525043 : term180 = term181.
Proof. exact (MK_COMB (@lem1525042) (@lem1525041)). Qed.
Lemma lem1525044 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525045 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1525043) (@lem1525044 y)). Qed.
Lemma lem1525046 (y : real) : (term185 y) = (term182 y).
Proof. exact (TRANS (@lem1525038 y) (@lem1525045 y)). Qed.
Lemma lem1525047 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1525048 (y : real) : (term185 y) = term22.
Proof. exact (TRANS (@lem1525046 y) (@lem1525047 y)). Qed.
Lemma lem1525049 (x : real) (y : real) : (term175 x y) = term186.
Proof. exact (MK_COMB (@lem1525037 x) (@lem1525048 y)). Qed.
Lemma lem1525050 (x : real) (y : real) : (term174 x y) = term186.
Proof. exact (TRANS (@lem1525024 x y) (@lem1525049 x y)). Qed.
Lemma lem1525051 : term186 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1525052 (x : real) (y : real) : (term174 x y) = term22.
Proof. exact (TRANS (@lem1525050 x y) (@lem1525051)). Qed.
Lemma lem1525053 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525054 (x : real) (y : real) : (term187 x y) = term188.
Proof. exact (MK_COMB (@lem1525053) (@lem1525052 x y)). Qed.
Lemma lem1525055 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525056 (x : real) (y : real) : (term173 x y) = term189.
Proof. exact (MK_COMB (@lem1525054 x y) (@lem1525055)). Qed.
Lemma lem1525057 (x : real) (y : real) (h1 : term154 x y) : term189.
Proof. exact (EQ_MP (@lem1525056 x y) (@lem1525023 x y h1)). Qed.
Lemma lem1525059 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525060 : term189 = term190.
Proof. exact (@lem1525059 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1525061 : term190 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1525062 : term189 = False.
Proof. exact (TRANS (@lem1525060) (@lem1525061)). Qed.
Lemma lem1525063 (x : real) (y : real) (h1 : term154 x y) : False.
Proof. exact (EQ_MP (@lem1525062) (@lem1525057 x y h1)). Qed.
Lemma lem1525064 (x : real) (y : real) (h1 : term191 x y) : term191 x y.
Proof. exact (h1). Qed.
Lemma lem1525065 (x : real) (y : real) (h1 : term191 x y) : term56 x y.
Proof. exact (proj2 (@lem1525064 x y h1)). Qed.
Lemma lem1525066 (x : real) (y : real) (h1 : term191 x y) : (term43 x y) = term22.
Proof. exact (proj1 (@lem1525064 x y h1)). Qed.
Lemma lem1525068 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525069 : term156 = term157.
Proof. exact (@lem1525068 (NUMERAL 0) term35). Qed.
Lemma lem1525070 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1525071 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1525072 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1525071 h1) (fun h1 : term157 = True => @lem1525070)). Qed.
Lemma lem1525073 : term157 = True.
Proof. exact (EQ_MP (@lem1525072) (@lem1525070)). Qed.
Lemma lem1525074 : term156 = True.
Proof. exact (TRANS (@lem1525069) (@lem1525073)). Qed.
Lemma lem1525075 : True = term156.
Proof. exact (SYM (@lem1525074)). Qed.
Lemma lem1525076 : term156.
Proof. exact (EQ_MP (@lem1525075) (@lem0)). Qed.
Lemma lem1525077 (x : real) (y : real) (h1 : term191 x y) : term192 x y.
Proof. exact (conj (@lem1525076) (@lem1525065 x y h1)). Qed.
Lemma lem1525079 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1525080 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1525079 term38 (term43 x y)). Qed.
Lemma lem1525081 (x : real) (y : real) (h1 : term191 x y) : term194 x y.
Proof. exact (@lem1525080 x y (@lem1525077 x y h1)). Qed.
Lemma lem1525082 (x : real) (y : real) : (term169 x y) = (term43 x y).
Proof. exact (@lem1483460 (term43 x y)). Qed.
Lemma lem1525083 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525084 (x : real) (y : real) : (term195 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1525083) (@lem1525082 x y)). Qed.
Lemma lem1525085 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525086 (x : real) (y : real) : (term194 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1525084 x y) (@lem1525085)). Qed.
Lemma lem1525087 (x : real) (y : real) (h1 : term191 x y) : term56 x y.
Proof. exact (EQ_MP (@lem1525086 x y) (@lem1525081 x y h1)). Qed.
Lemma lem1525089 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1525090 (x : real) (y : real) : term166 x y.
Proof. exact (@lem1525089 (term43 x y)). Qed.
Lemma lem1525091 (x : real) (y : real) (h1 : term191 x y) : term167 x y.
Proof. exact (@lem1525090 x y (@lem1525066 x y h1)). Qed.
Lemma lem1525092 (x : real) (y : real) (h1 : term191 x y) : term196 x y.
Proof. exact (@lem1525091 x y h1 term30). Qed.
Lemma lem1525093 (x : real) (y : real) : (term196 x y) = ((term72 x y) = term22).
Proof. exact (eq_refl (term196 x y)). Qed.
Lemma lem1525094 (x : real) (y : real) (h1 : term191 x y) : (term72 x y) = term22.
Proof. exact (EQ_MP (@lem1525093 x y) (@lem1525092 x y h1)). Qed.
Lemma lem1525095 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483508 (term23 x) term30 y). Qed.
Lemma lem1525096 (y : real) : (term23 y) = (term23 y).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem1525097 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1525099 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1525100 : term33 = term34.
Proof. exact (@lem1525099 term35 term35). Qed.
Lemma lem1525101 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1525102 : term37 = term35.
Proof. exact (EQ_MP (@lem1525101) (@lem940073)). Qed.
Lemma lem1525103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1525104 : term34 = term38.
Proof. exact (MK_COMB (@lem1525103) (@lem1525102)). Qed.
Lemma lem1525105 : term33 = term38.
Proof. exact (TRANS (@lem1525100) (@lem1525104)). Qed.
Lemma lem1525106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525107 : term39 = term40.
Proof. exact (MK_COMB (@lem1525106) (@lem1525105)). Qed.
Lemma lem1525108 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525109 (x : real) : (term29 x) = (term41 x).
Proof. exact (MK_COMB (@lem1525107) (@lem1525108 x)). Qed.
Lemma lem1525110 (x : real) : (term28 x) = (term41 x).
Proof. exact (TRANS (@lem1525097 x) (@lem1525109 x)). Qed.
Lemma lem1525111 (x : real) : (term41 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1525112 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1525110 x) (@lem1525111 x)). Qed.
Lemma lem1525113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1525114 (x : real) : (term74 x) = (real_add x).
Proof. exact (MK_COMB (@lem1525113) (@lem1525112 x)). Qed.
Lemma lem1525115 (x : real) (y : real) : (term73 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1525114 x) (@lem1525096 y)). Qed.
Lemma lem1525116 (x : real) (y : real) : (term72 x y) = (term48 x y).
Proof. exact (TRANS (@lem1525095 x y) (@lem1525115 x y)). Qed.
Lemma lem1525117 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1525118 (x : real) (y : real) : (term197 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1525117) (@lem1525116 x y)). Qed.
Lemma lem1525119 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525120 (x : real) (y : real) : ((term72 x y) = term22) = ((term48 x y) = term22).
Proof. exact (MK_COMB (@lem1525118 x y) (@lem1525119)). Qed.
Lemma lem1525121 (x : real) (y : real) (h1 : term191 x y) : (term48 x y) = term22.
Proof. exact (EQ_MP (@lem1525120 x y) (@lem1525094 x y h1)). Qed.
Lemma lem1525122 (x : real) (y : real) (h1 : term191 x y) : term198 x y.
Proof. exact (conj (@lem1525121 x y h1) (@lem1525087 x y h1)). Qed.
Lemma lem1525124 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1525125 (x : real) (y : real) : term199 x y.
Proof. exact (@lem1525124 (term48 x y) (term43 x y)). Qed.
Lemma lem1525126 (x : real) (y : real) (h1 : term191 x y) : term200 x y.
Proof. exact (@lem1525125 x y (@lem1525122 x y h1)). Qed.
Lemma lem1525127 (x : real) (y : real) : (term201 x y) = (term202 x y).
Proof. exact (@lem1483480 x (term23 x) (term23 y) y). Qed.
Lemma lem1525128 (x : real) : (term185 x) = (term177 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1525130 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525131 : term179 = term22.
Proof. exact (@lem1525130 term35). Qed.
Lemma lem1525132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525133 : term180 = term181.
Proof. exact (MK_COMB (@lem1525132) (@lem1525131)). Qed.
Lemma lem1525134 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525135 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1525133) (@lem1525134 x)). Qed.
Lemma lem1525136 (x : real) : (term185 x) = (term182 x).
Proof. exact (TRANS (@lem1525128 x) (@lem1525135 x)). Qed.
Lemma lem1525137 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1525138 (x : real) : (term185 x) = term22.
Proof. exact (TRANS (@lem1525136 x) (@lem1525137 x)). Qed.
Lemma lem1525139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1525140 (x : real) : (term203 x) = term184.
Proof. exact (MK_COMB (@lem1525139) (@lem1525138 x)). Qed.
Lemma lem1525141 (y : real) : (term176 y) = (term177 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1525143 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525144 : term179 = term22.
Proof. exact (@lem1525143 term35). Qed.
Lemma lem1525145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525146 : term180 = term181.
Proof. exact (MK_COMB (@lem1525145) (@lem1525144)). Qed.
Lemma lem1525147 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525148 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1525146) (@lem1525147 y)). Qed.
Lemma lem1525149 (y : real) : (term176 y) = (term182 y).
Proof. exact (TRANS (@lem1525141 y) (@lem1525148 y)). Qed.
Lemma lem1525150 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1525151 (y : real) : (term176 y) = term22.
Proof. exact (TRANS (@lem1525149 y) (@lem1525150 y)). Qed.
Lemma lem1525152 (x : real) (y : real) : (term202 x y) = term186.
Proof. exact (MK_COMB (@lem1525140 x) (@lem1525151 y)). Qed.
Lemma lem1525153 (x : real) (y : real) : (term201 x y) = term186.
Proof. exact (TRANS (@lem1525127 x y) (@lem1525152 x y)). Qed.
Lemma lem1525154 : term186 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1525155 (x : real) (y : real) : (term201 x y) = term22.
Proof. exact (TRANS (@lem1525153 x y) (@lem1525154)). Qed.
Lemma lem1525156 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525157 (x : real) (y : real) : (term204 x y) = term188.
Proof. exact (MK_COMB (@lem1525156) (@lem1525155 x y)). Qed.
Lemma lem1525158 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525159 (x : real) (y : real) : (term200 x y) = term189.
Proof. exact (MK_COMB (@lem1525157 x y) (@lem1525158)). Qed.
Lemma lem1525160 (x : real) (y : real) (h1 : term191 x y) : term189.
Proof. exact (EQ_MP (@lem1525159 x y) (@lem1525126 x y h1)). Qed.
Lemma lem1525162 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525163 : term189 = term190.
Proof. exact (@lem1525162 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1525164 : term190 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1525165 : term189 = False.
Proof. exact (TRANS (@lem1525163) (@lem1525164)). Qed.
Lemma lem1525166 (x : real) (y : real) (h1 : term191 x y) : False.
Proof. exact (EQ_MP (@lem1525165) (@lem1525160 x y h1)). Qed.
Lemma lem1525167 (x : real) (y : real) (h1 : term147 x y) : False.
Proof. exact (or_elim (@lem1524981 x y h1) (fun h0 : term154 x y => @lem1525063 x y h0) (fun h0 : term191 x y => @lem1525166 x y h0)). Qed.
Lemma lem1525168 (x : real) (y : real) (h1 : term146 x y) : term146 x y.
Proof. exact (h1). Qed.
Lemma lem1525169 (x : real) (y : real) (h1 : term205 x y) : term205 x y.
Proof. exact (h1). Qed.
Lemma lem1525170 (x : real) (y : real) (h1 : term205 x y) : (term48 x y) = term22.
Proof. exact (proj2 (@lem1525169 x y h1)). Qed.
Lemma lem1525171 (x : real) (y : real) (h1 : term205 x y) : term56 x y.
Proof. exact (proj1 (@lem1525169 x y h1)). Qed.
Lemma lem1525173 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525174 : term156 = term157.
Proof. exact (@lem1525173 (NUMERAL 0) term35). Qed.
Lemma lem1525175 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1525176 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1525177 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1525176 h1) (fun h1 : term157 = True => @lem1525175)). Qed.
Lemma lem1525178 : term157 = True.
Proof. exact (EQ_MP (@lem1525177) (@lem1525175)). Qed.
Lemma lem1525179 : term156 = True.
Proof. exact (TRANS (@lem1525174) (@lem1525178)). Qed.
Lemma lem1525180 : True = term156.
Proof. exact (SYM (@lem1525179)). Qed.
Lemma lem1525181 : term156.
Proof. exact (EQ_MP (@lem1525180) (@lem0)). Qed.
Lemma lem1525182 (x : real) (y : real) (h1 : term205 x y) : term192 x y.
Proof. exact (conj (@lem1525181) (@lem1525171 x y h1)). Qed.
Lemma lem1525184 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1525185 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1525184 term38 (term43 x y)). Qed.
Lemma lem1525186 (x : real) (y : real) (h1 : term205 x y) : term194 x y.
Proof. exact (@lem1525185 x y (@lem1525182 x y h1)). Qed.
Lemma lem1525187 (x : real) (y : real) : (term169 x y) = (term43 x y).
Proof. exact (@lem1483460 (term43 x y)). Qed.
Lemma lem1525188 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525189 (x : real) (y : real) : (term195 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1525188) (@lem1525187 x y)). Qed.
Lemma lem1525190 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525191 (x : real) (y : real) : (term194 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1525189 x y) (@lem1525190)). Qed.
Lemma lem1525192 (x : real) (y : real) (h1 : term205 x y) : term56 x y.
Proof. exact (EQ_MP (@lem1525191 x y) (@lem1525186 x y h1)). Qed.
Lemma lem1525194 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1525195 (x : real) (y : real) : term206 x y.
Proof. exact (@lem1525194 (term48 x y)). Qed.
Lemma lem1525196 (x : real) (y : real) (h1 : term205 x y) : term207 x y.
Proof. exact (@lem1525195 x y (@lem1525170 x y h1)). Qed.
Lemma lem1525197 (x : real) (y : real) (h1 : term205 x y) : term208 x y.
Proof. exact (@lem1525196 x y h1 term38). Qed.
Lemma lem1525198 (x : real) (y : real) : (term208 x y) = ((term163 x y) = term22).
Proof. exact (eq_refl (term208 x y)). Qed.
Lemma lem1525199 (x : real) (y : real) (h1 : term205 x y) : (term163 x y) = term22.
Proof. exact (EQ_MP (@lem1525198 x y) (@lem1525197 x y h1)). Qed.
Lemma lem1525200 (x : real) (y : real) : (term163 x y) = (term48 x y).
Proof. exact (@lem1483460 (term48 x y)). Qed.
Lemma lem1525201 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1525202 (x : real) (y : real) : (term209 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1525201) (@lem1525200 x y)). Qed.
Lemma lem1525203 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525204 (x : real) (y : real) : ((term163 x y) = term22) = ((term48 x y) = term22).
Proof. exact (MK_COMB (@lem1525202 x y) (@lem1525203)). Qed.
Lemma lem1525205 (x : real) (y : real) (h1 : term205 x y) : (term48 x y) = term22.
Proof. exact (EQ_MP (@lem1525204 x y) (@lem1525199 x y h1)). Qed.
Lemma lem1525206 (x : real) (y : real) (h1 : term205 x y) : term198 x y.
Proof. exact (conj (@lem1525205 x y h1) (@lem1525192 x y h1)). Qed.
Lemma lem1525208 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1525209 (x : real) (y : real) : term199 x y.
Proof. exact (@lem1525208 (term48 x y) (term43 x y)). Qed.
Lemma lem1525210 (x : real) (y : real) (h1 : term205 x y) : term200 x y.
Proof. exact (@lem1525209 x y (@lem1525206 x y h1)). Qed.
Lemma lem1525211 (x : real) (y : real) : (term201 x y) = (term202 x y).
Proof. exact (@lem1483480 x (term23 x) (term23 y) y). Qed.
Lemma lem1525212 (x : real) : (term185 x) = (term177 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1525214 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525215 : term179 = term22.
Proof. exact (@lem1525214 term35). Qed.
Lemma lem1525216 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525217 : term180 = term181.
Proof. exact (MK_COMB (@lem1525216) (@lem1525215)). Qed.
Lemma lem1525218 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525219 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1525217) (@lem1525218 x)). Qed.
Lemma lem1525220 (x : real) : (term185 x) = (term182 x).
Proof. exact (TRANS (@lem1525212 x) (@lem1525219 x)). Qed.
Lemma lem1525221 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1525222 (x : real) : (term185 x) = term22.
Proof. exact (TRANS (@lem1525220 x) (@lem1525221 x)). Qed.
Lemma lem1525223 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1525224 (x : real) : (term203 x) = term184.
Proof. exact (MK_COMB (@lem1525223) (@lem1525222 x)). Qed.
Lemma lem1525225 (y : real) : (term176 y) = (term177 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1525227 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525228 : term179 = term22.
Proof. exact (@lem1525227 term35). Qed.
Lemma lem1525229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525230 : term180 = term181.
Proof. exact (MK_COMB (@lem1525229) (@lem1525228)). Qed.
Lemma lem1525231 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525232 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1525230) (@lem1525231 y)). Qed.
Lemma lem1525233 (y : real) : (term176 y) = (term182 y).
Proof. exact (TRANS (@lem1525225 y) (@lem1525232 y)). Qed.
Lemma lem1525234 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1525235 (y : real) : (term176 y) = term22.
Proof. exact (TRANS (@lem1525233 y) (@lem1525234 y)). Qed.
Lemma lem1525236 (x : real) (y : real) : (term202 x y) = term186.
Proof. exact (MK_COMB (@lem1525224 x) (@lem1525235 y)). Qed.
Lemma lem1525237 (x : real) (y : real) : (term201 x y) = term186.
Proof. exact (TRANS (@lem1525211 x y) (@lem1525236 x y)). Qed.
Lemma lem1525238 : term186 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1525239 (x : real) (y : real) : (term201 x y) = term22.
Proof. exact (TRANS (@lem1525237 x y) (@lem1525238)). Qed.
Lemma lem1525240 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525241 (x : real) (y : real) : (term204 x y) = term188.
Proof. exact (MK_COMB (@lem1525240) (@lem1525239 x y)). Qed.
Lemma lem1525242 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525243 (x : real) (y : real) : (term200 x y) = term189.
Proof. exact (MK_COMB (@lem1525241 x y) (@lem1525242)). Qed.
Lemma lem1525244 (x : real) (y : real) (h1 : term205 x y) : term189.
Proof. exact (EQ_MP (@lem1525243 x y) (@lem1525210 x y h1)). Qed.
Lemma lem1525246 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525247 : term189 = term190.
Proof. exact (@lem1525246 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1525248 : term190 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1525249 : term189 = False.
Proof. exact (TRANS (@lem1525247) (@lem1525248)). Qed.
Lemma lem1525250 (x : real) (y : real) (h1 : term205 x y) : False.
Proof. exact (EQ_MP (@lem1525249) (@lem1525244 x y h1)). Qed.
Lemma lem1525251 (x : real) (y : real) (h1 : term210 x y) : term210 x y.
Proof. exact (h1). Qed.
Lemma lem1525252 (x : real) (y : real) (h1 : term210 x y) : (term48 x y) = term22.
Proof. exact (proj2 (@lem1525251 x y h1)). Qed.
Lemma lem1525253 (x : real) (y : real) (h1 : term210 x y) : term60 x y.
Proof. exact (proj1 (@lem1525251 x y h1)). Qed.
Lemma lem1525255 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525256 : term156 = term157.
Proof. exact (@lem1525255 (NUMERAL 0) term35). Qed.
Lemma lem1525257 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1525258 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1525259 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1525258 h1) (fun h1 : term157 = True => @lem1525257)). Qed.
Lemma lem1525260 : term157 = True.
Proof. exact (EQ_MP (@lem1525259) (@lem1525257)). Qed.
Lemma lem1525261 : term156 = True.
Proof. exact (TRANS (@lem1525256) (@lem1525260)). Qed.
Lemma lem1525262 : True = term156.
Proof. exact (SYM (@lem1525261)). Qed.
Lemma lem1525263 : term156.
Proof. exact (EQ_MP (@lem1525262) (@lem0)). Qed.
Lemma lem1525264 (x : real) (y : real) (h1 : term210 x y) : term159 x y.
Proof. exact (conj (@lem1525263) (@lem1525253 x y h1)). Qed.
Lemma lem1525266 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1525267 (x : real) (y : real) : term161 x y.
Proof. exact (@lem1525266 term38 (term48 x y)). Qed.
Lemma lem1525268 (x : real) (y : real) (h1 : term210 x y) : term162 x y.
Proof. exact (@lem1525267 x y (@lem1525264 x y h1)). Qed.
Lemma lem1525269 (x : real) (y : real) : (term163 x y) = (term48 x y).
Proof. exact (@lem1483460 (term48 x y)). Qed.
Lemma lem1525270 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525271 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1525270) (@lem1525269 x y)). Qed.
Lemma lem1525272 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525273 (x : real) (y : real) : (term162 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1525271 x y) (@lem1525272)). Qed.
Lemma lem1525274 (x : real) (y : real) (h1 : term210 x y) : term60 x y.
Proof. exact (EQ_MP (@lem1525273 x y) (@lem1525268 x y h1)). Qed.
Lemma lem1525276 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1525277 (x : real) (y : real) : term206 x y.
Proof. exact (@lem1525276 (term48 x y)). Qed.
Lemma lem1525278 (x : real) (y : real) (h1 : term210 x y) : term207 x y.
Proof. exact (@lem1525277 x y (@lem1525252 x y h1)). Qed.
Lemma lem1525279 (x : real) (y : real) (h1 : term210 x y) : term211 x y.
Proof. exact (@lem1525278 x y h1 term30). Qed.
Lemma lem1525280 (x : real) (y : real) : (term211 x y) = ((term51 x y) = term22).
Proof. exact (eq_refl (term211 x y)). Qed.
Lemma lem1525281 (x : real) (y : real) (h1 : term210 x y) : (term51 x y) = term22.
Proof. exact (EQ_MP (@lem1525280 x y) (@lem1525279 x y h1)). Qed.
Lemma lem1525282 (x : real) (y : real) : (term51 x y) = (term27 x y).
Proof. exact (@lem1483508 x term30 (term23 y)). Qed.
Lemma lem1525283 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1525285 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1525286 : term33 = term34.
Proof. exact (@lem1525285 term35 term35). Qed.
Lemma lem1525287 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1525288 : term37 = term35.
Proof. exact (EQ_MP (@lem1525287) (@lem940073)). Qed.
Lemma lem1525289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1525290 : term34 = term38.
Proof. exact (MK_COMB (@lem1525289) (@lem1525288)). Qed.
Lemma lem1525291 : term33 = term38.
Proof. exact (TRANS (@lem1525286) (@lem1525290)). Qed.
Lemma lem1525292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525293 : term39 = term40.
Proof. exact (MK_COMB (@lem1525292) (@lem1525291)). Qed.
Lemma lem1525294 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525295 (y : real) : (term29 y) = (term41 y).
Proof. exact (MK_COMB (@lem1525293) (@lem1525294 y)). Qed.
Lemma lem1525296 (y : real) : (term28 y) = (term41 y).
Proof. exact (TRANS (@lem1525283 y) (@lem1525295 y)). Qed.
Lemma lem1525297 (y : real) : (term41 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1525298 (y : real) : (term28 y) = y.
Proof. exact (TRANS (@lem1525296 y) (@lem1525297 y)). Qed.
Lemma lem1525301 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1525302 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1525301 x) (@lem1525298 y)). Qed.
Lemma lem1525303 (x : real) (y : real) : (term51 x y) = (term43 x y).
Proof. exact (TRANS (@lem1525282 x y) (@lem1525302 x y)). Qed.
Lemma lem1525304 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1525305 (x : real) (y : real) : (term212 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1525304) (@lem1525303 x y)). Qed.
Lemma lem1525306 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525307 (x : real) (y : real) : ((term51 x y) = term22) = ((term43 x y) = term22).
Proof. exact (MK_COMB (@lem1525305 x y) (@lem1525306)). Qed.
Lemma lem1525308 (x : real) (y : real) (h1 : term210 x y) : (term43 x y) = term22.
Proof. exact (EQ_MP (@lem1525307 x y) (@lem1525281 x y h1)). Qed.
Lemma lem1525309 (x : real) (y : real) (h1 : term210 x y) : term154 x y.
Proof. exact (conj (@lem1525308 x y h1) (@lem1525274 x y h1)). Qed.
Lemma lem1525311 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1525312 (x : real) (y : real) : term172 x y.
Proof. exact (@lem1525311 (term43 x y) (term48 x y)). Qed.
Lemma lem1525313 (x : real) (y : real) (h1 : term210 x y) : term173 x y.
Proof. exact (@lem1525312 x y (@lem1525309 x y h1)). Qed.
Lemma lem1525314 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483480 (term23 x) x y (term23 y)). Qed.
Lemma lem1525315 (x : real) : (term176 x) = (term177 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1525317 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525318 : term179 = term22.
Proof. exact (@lem1525317 term35). Qed.
Lemma lem1525319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525320 : term180 = term181.
Proof. exact (MK_COMB (@lem1525319) (@lem1525318)). Qed.
Lemma lem1525321 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525322 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1525320) (@lem1525321 x)). Qed.
Lemma lem1525323 (x : real) : (term176 x) = (term182 x).
Proof. exact (TRANS (@lem1525315 x) (@lem1525322 x)). Qed.
Lemma lem1525324 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1525325 (x : real) : (term176 x) = term22.
Proof. exact (TRANS (@lem1525323 x) (@lem1525324 x)). Qed.
Lemma lem1525326 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1525327 (x : real) : (term183 x) = term184.
Proof. exact (MK_COMB (@lem1525326) (@lem1525325 x)). Qed.
Lemma lem1525328 (y : real) : (term185 y) = (term177 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1525330 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1525331 : term179 = term22.
Proof. exact (@lem1525330 term35). Qed.
Lemma lem1525332 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525333 : term180 = term181.
Proof. exact (MK_COMB (@lem1525332) (@lem1525331)). Qed.
Lemma lem1525334 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525335 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1525333) (@lem1525334 y)). Qed.
Lemma lem1525336 (y : real) : (term185 y) = (term182 y).
Proof. exact (TRANS (@lem1525328 y) (@lem1525335 y)). Qed.
Lemma lem1525337 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1525338 (y : real) : (term185 y) = term22.
Proof. exact (TRANS (@lem1525336 y) (@lem1525337 y)). Qed.
Lemma lem1525339 (x : real) (y : real) : (term175 x y) = term186.
Proof. exact (MK_COMB (@lem1525327 x) (@lem1525338 y)). Qed.
Lemma lem1525340 (x : real) (y : real) : (term174 x y) = term186.
Proof. exact (TRANS (@lem1525314 x y) (@lem1525339 x y)). Qed.
Lemma lem1525341 : term186 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1525342 (x : real) (y : real) : (term174 x y) = term22.
Proof. exact (TRANS (@lem1525340 x y) (@lem1525341)). Qed.
Lemma lem1525343 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525344 (x : real) (y : real) : (term187 x y) = term188.
Proof. exact (MK_COMB (@lem1525343) (@lem1525342 x y)). Qed.
Lemma lem1525345 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1525346 (x : real) (y : real) : (term173 x y) = term189.
Proof. exact (MK_COMB (@lem1525344 x y) (@lem1525345)). Qed.
Lemma lem1525347 (x : real) (y : real) (h1 : term210 x y) : term189.
Proof. exact (EQ_MP (@lem1525346 x y) (@lem1525313 x y h1)). Qed.
Lemma lem1525349 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525350 : term189 = term190.
Proof. exact (@lem1525349 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1525351 : term190 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1525352 : term189 = False.
Proof. exact (TRANS (@lem1525350) (@lem1525351)). Qed.
Lemma lem1525353 (x : real) (y : real) (h1 : term210 x y) : False.
Proof. exact (EQ_MP (@lem1525352) (@lem1525347 x y h1)). Qed.
Lemma lem1525354 (x : real) (y : real) (h1 : term146 x y) : False.
Proof. exact (or_elim (@lem1525168 x y h1) (fun h0 : term205 x y => @lem1525250 x y h0) (fun h0 : term210 x y => @lem1525353 x y h0)). Qed.
Lemma lem1525355 (x : real) (y : real) (h1 : term149 x y) : False.
Proof. exact (or_elim (@lem1524980 x y h1) (fun h0 : term147 x y => @lem1525167 x y h0) (fun h0 : term146 x y => @lem1525354 x y h0)). Qed.
Lemma lem1525357 (x : real) (y : real) (h1 : term149 x y) : term149 x y.
Proof. exact (h1). Qed.
Lemma lem1525358 (x : real) (y : real) (h1 : term149 x y) : (term149 x y) = False.
Proof. exact (prop_ext (fun h2 : term149 x y => @lem1525355 x y h1) (fun h2 : False => @lem1525357 x y h1)). Qed.
Lemma lem1525359 (x : real) (y : real) (h1 : term149 x y) : False.
Proof. exact (EQ_MP (@lem1525358 x y h1) (@lem1525357 x y h1)). Qed.
Lemma lem1525360 (x : real) (h1 : term151 x) : term151 x.
Proof. exact (h1). Qed.
Lemma lem1525361 (x : real) (h1 : term151 x) : False.
Proof. exact (ex_elim (@lem1525360 x h1) (fun y : real => fun h0 : term150 x y => @lem1525359 x y h0)). Qed.
Lemma lem1525362 (h1 : term153) : term153.
Proof. exact (h1). Qed.
Lemma lem1525363 (h1 : term153) : False.
Proof. exact (ex_elim (@lem1525362 h1) (fun x : real => fun h0 : term152 x => @lem1525361 x h0)). Qed.
Lemma lem1525364 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1525365 (h1 : term12) : term153.
Proof. exact (EQ_MP (@lem1524958) (@lem1525364 h1)). Qed.
Lemma lem1525366 (h1 : term12) : term153 = False.
Proof. exact (prop_ext (fun h2 : term153 => @lem1525363 h2) (fun h2 : False => @lem1525365 h1)). Qed.
Lemma lem1525367 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1525366 h1) (@lem1525365 h1)). Qed.
Lemma lem1525368 : term213.
Proof. exact (fun h0 : term12 => @lem1525367 h0). Qed.
Lemma lem1525369 : term214.
Proof. exact (@lem1386578 term215). Qed.
Lemma lem1525370 : term215.
Proof. exact (@lem1525369 (@lem1525368)). Qed.
