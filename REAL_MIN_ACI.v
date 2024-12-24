Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_ACI_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482698_spec.
Require Import thm1482715_spec.
Require Import thm1482716_spec.
Require Import thm1483429_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm17045_spec.
Require Import thm940073_spec.
Lemma lem1578343 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17045 ((real_min x x) = x) ((term2 x y) = (real_min x y))). Qed.
Lemma lem1578345 (y : real) (x : real) (z : real) : (term3 y x z) = (term3 y x z).
Proof. exact (eq_refl (term3 y x z)). Qed.
Lemma lem1578346 (z : real) (x : real) (y : real) : (term4 z x y) = (term5 z x y).
Proof. exact (MK_COMB (@lem1578345 y x z) (@lem1578343 x y)). Qed.
Lemma lem1578347 (z : real) (x : real) (y : real) : (term6 z x y) = (term4 z x y).
Proof. exact (@lem17045 ((term7 x y z) = (term7 y x z)) (term8 x y)). Qed.
Lemma lem1578348 (z : real) (x : real) (y : real) : (term6 z x y) = (term5 z x y).
Proof. exact (TRANS (@lem1578347 z x y) (@lem1578346 z x y)). Qed.
Lemma lem1578350 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1578351 (z : real) (x : real) (y : real) : (term10 z x y) = (term11 z x y).
Proof. exact (MK_COMB (@lem1578350 x y z) (@lem1578348 z x y)). Qed.
Lemma lem1578352 (z : real) (x : real) (y : real) : (term12 z x y) = (term10 z x y).
Proof. exact (@lem17045 ((term13 x y z) = (term7 x y z)) (term14 z x y)). Qed.
Lemma lem1578353 (z : real) (x : real) (y : real) : (term12 z x y) = (term11 z x y).
Proof. exact (TRANS (@lem1578352 z x y) (@lem1578351 z x y)). Qed.
Lemma lem1578355 (y : real) (x : real) : (term15 y x) = (term15 y x).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1578356 (z : real) (x : real) (y : real) : (term16 z x y) = (term17 z x y).
Proof. exact (MK_COMB (@lem1578355 y x) (@lem1578353 z x y)). Qed.
Lemma lem1578357 (z : real) (x : real) (y : real) : (term18 z x y) = (term16 z x y).
Proof. exact (@lem17045 ((real_min x y) = (real_min y x)) (term19 z x y)). Qed.
Lemma lem1578387 (z : real) (x : real) (y : real) : (term18 z x y) = (term17 z x y).
Proof. exact (TRANS (@lem1578357 z x y) (@lem1578356 z x y)). Qed.
Lemma lem1578388 (y : real) (x : real) : (term20 y x) = (term21 y x).
Proof. exact (@lem1483554 (real_min x y) (real_min y x)). Qed.
Lemma lem1578401 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1483519 (real_min x y) (real_min y x)). Qed.
Lemma lem1578402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1578403 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1578402) (@lem1578401 y x)). Qed.
Lemma lem1578404 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1483512 (term23 y x)). Qed.
Lemma lem1578405 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (@lem1483508 (real_min x y) term28 (term29 y x)). Qed.
Lemma lem1578406 (y : real) (x : real) : (term30 y x) = (term31 y x).
Proof. exact (@lem1483476 term28 term28 (real_min y x)). Qed.
Lemma lem1578408 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1578409 : term34 = term35.
Proof. exact (@lem1578408 term36 term36). Qed.
Lemma lem1578410 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1578411 : term38 = term36.
Proof. exact (EQ_MP (@lem1578410) (@lem940073)). Qed.
Lemma lem1578412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1578413 : term35 = term39.
Proof. exact (MK_COMB (@lem1578412) (@lem1578411)). Qed.
Lemma lem1578414 : term34 = term39.
Proof. exact (TRANS (@lem1578409) (@lem1578413)). Qed.
Lemma lem1578415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578416 : term40 = term41.
Proof. exact (MK_COMB (@lem1578415) (@lem1578414)). Qed.
Lemma lem1578417 (y : real) (x : real) : (real_min y x) = (real_min y x).
Proof. exact (eq_refl (real_min y x)). Qed.
Lemma lem1578418 (y : real) (x : real) : (term31 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1578416) (@lem1578417 y x)). Qed.
Lemma lem1578419 (y : real) (x : real) : (term30 y x) = (term42 y x).
Proof. exact (TRANS (@lem1578406 y x) (@lem1578418 y x)). Qed.
Lemma lem1578420 (y : real) (x : real) : (term42 y x) = (real_min y x).
Proof. exact (@lem1483436 (real_min y x)). Qed.
Lemma lem1578421 (y : real) (x : real) : (term30 y x) = (real_min y x).
Proof. exact (TRANS (@lem1578419 y x) (@lem1578420 y x)). Qed.
Lemma lem1578424 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1578425 (y : real) (x : real) : (term27 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1578424 x y) (@lem1578421 y x)). Qed.
Lemma lem1578426 (y : real) (x : real) : (term26 y x) = (term44 y x).
Proof. exact (TRANS (@lem1578405 y x) (@lem1578425 y x)). Qed.
Lemma lem1578427 (y : real) (x : real) : (term25 y x) = (term44 y x).
Proof. exact (TRANS (@lem1578404 y x) (@lem1578426 y x)). Qed.
Lemma lem1578428 (y : real) (x : real) : (term45 y x) = (term45 y x).
Proof. exact (eq_refl (term45 y x)). Qed.
Lemma lem1578429 (y : real) (x : real) : ((term24 y x) = (term25 y x)) = ((term24 y x) = (term44 y x)).
Proof. exact (MK_COMB (@lem1578428 y x) (@lem1578427 y x)). Qed.
Lemma lem1578430 (y : real) (x : real) : (term24 y x) = (term44 y x).
Proof. exact (EQ_MP (@lem1578429 y x) (@lem1578403 y x)). Qed.
Lemma lem1578431 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578432 (y : real) (x : real) : (term46 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1578431) (@lem1578430 y x)). Qed.
Lemma lem1578433 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578434 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1578432 y x) (@lem1578433)). Qed.
Lemma lem1578435 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578436 (y : real) (x : real) : (term51 y x) = (term52 y x).
Proof. exact (MK_COMB (@lem1578435) (@lem1578401 y x)). Qed.
Lemma lem1578437 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578438 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1578436 y x) (@lem1578437)). Qed.
Lemma lem1578439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578440 (y : real) (x : real) : (term55 y x) = (term56 y x).
Proof. exact (MK_COMB (@lem1578439) (@lem1578438 y x)). Qed.
Lemma lem1578441 (y : real) (x : real) : (term21 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1578440 y x) (@lem1578434 y x)). Qed.
Lemma lem1578442 (y : real) (x : real) : (term20 y x) = (term57 y x).
Proof. exact (TRANS (@lem1578388 y x) (@lem1578441 y x)). Qed.
Lemma lem1578443 (x : real) (y : real) (z : real) : (term58 x y z) = (term59 x y z).
Proof. exact (@lem1483554 (term13 x y z) (term7 x y z)). Qed.
Lemma lem1578449 (x : real) (y : real) (z : real) : (term60 x y z) = (term61 x y z).
Proof. exact (@lem1483519 (term13 x y z) (term7 x y z)). Qed.
Lemma lem1578454 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483488 (term63 x y z) (term13 x y z)). Qed.
Lemma lem1578456 (x : real) (y : real) (z : real) : (term60 x y z) = (term62 x y z).
Proof. exact (TRANS (@lem1578449 x y z) (@lem1578454 x y z)). Qed.
Lemma lem1578457 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1578458 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (MK_COMB (@lem1578457) (@lem1578456 x y z)). Qed.
Lemma lem1578459 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem1483512 (term62 x y z)). Qed.
Lemma lem1578460 (x : real) (y : real) (z : real) : (term66 x y z) = (term67 x y z).
Proof. exact (@lem1483508 (term63 x y z) term28 (term13 x y z)). Qed.
Lemma lem1578461 (x : real) (y : real) (z : real) : (term68 x y z) = (term68 x y z).
Proof. exact (eq_refl (term68 x y z)). Qed.
Lemma lem1578462 (x : real) (y : real) (z : real) : (term69 x y z) = (term70 x y z).
Proof. exact (@lem1483476 term28 term28 (term7 x y z)). Qed.
Lemma lem1578464 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1578465 : term34 = term35.
Proof. exact (@lem1578464 term36 term36). Qed.
Lemma lem1578466 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1578467 : term38 = term36.
Proof. exact (EQ_MP (@lem1578466) (@lem940073)). Qed.
Lemma lem1578468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1578469 : term35 = term39.
Proof. exact (MK_COMB (@lem1578468) (@lem1578467)). Qed.
Lemma lem1578470 : term34 = term39.
Proof. exact (TRANS (@lem1578465) (@lem1578469)). Qed.
Lemma lem1578471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578472 : term40 = term41.
Proof. exact (MK_COMB (@lem1578471) (@lem1578470)). Qed.
Lemma lem1578473 (x : real) (y : real) (z : real) : (term7 x y z) = (term7 x y z).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1578474 (x : real) (y : real) (z : real) : (term70 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1578472) (@lem1578473 x y z)). Qed.
Lemma lem1578475 (x : real) (y : real) (z : real) : (term69 x y z) = (term71 x y z).
Proof. exact (TRANS (@lem1578462 x y z) (@lem1578474 x y z)). Qed.
Lemma lem1578476 (x : real) (y : real) (z : real) : (term71 x y z) = (term7 x y z).
Proof. exact (@lem1483436 (term7 x y z)). Qed.
Lemma lem1578477 (x : real) (y : real) (z : real) : (term69 x y z) = (term7 x y z).
Proof. exact (TRANS (@lem1578475 x y z) (@lem1578476 x y z)). Qed.
Lemma lem1578478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1578479 (x : real) (y : real) (z : real) : (term72 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1578478) (@lem1578477 x y z)). Qed.
Lemma lem1578480 (x : real) (y : real) (z : real) : (term67 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1578479 x y z) (@lem1578461 x y z)). Qed.
Lemma lem1578481 (x : real) (y : real) (z : real) : (term66 x y z) = (term74 x y z).
Proof. exact (TRANS (@lem1578460 x y z) (@lem1578480 x y z)). Qed.
Lemma lem1578482 (x : real) (y : real) (z : real) : (term65 x y z) = (term74 x y z).
Proof. exact (TRANS (@lem1578459 x y z) (@lem1578481 x y z)). Qed.
Lemma lem1578483 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (eq_refl (term75 x y z)). Qed.
Lemma lem1578484 (x : real) (y : real) (z : real) : ((term64 x y z) = (term65 x y z)) = ((term64 x y z) = (term74 x y z)).
Proof. exact (MK_COMB (@lem1578483 x y z) (@lem1578482 x y z)). Qed.
Lemma lem1578485 (x : real) (y : real) (z : real) : (term64 x y z) = (term74 x y z).
Proof. exact (EQ_MP (@lem1578484 x y z) (@lem1578458 x y z)). Qed.
Lemma lem1578486 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578487 (x : real) (y : real) (z : real) : (term76 x y z) = (term77 x y z).
Proof. exact (MK_COMB (@lem1578486) (@lem1578485 x y z)). Qed.
Lemma lem1578488 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578489 (x : real) (y : real) (z : real) : (term78 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1578487 x y z) (@lem1578488)). Qed.
Lemma lem1578490 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578491 (x : real) (y : real) (z : real) : (term80 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1578490) (@lem1578456 x y z)). Qed.
Lemma lem1578492 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578493 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (MK_COMB (@lem1578491 x y z) (@lem1578492)). Qed.
Lemma lem1578494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578495 (x : real) (y : real) (z : real) : (term84 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem1578494) (@lem1578493 x y z)). Qed.
Lemma lem1578496 (x : real) (y : real) (z : real) : (term59 x y z) = (term86 x y z).
Proof. exact (MK_COMB (@lem1578495 x y z) (@lem1578489 x y z)). Qed.
Lemma lem1578497 (x : real) (y : real) (z : real) : (term58 x y z) = (term86 x y z).
Proof. exact (TRANS (@lem1578443 x y z) (@lem1578496 x y z)). Qed.
Lemma lem1578498 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1483554 (term7 x y z) (term7 y x z)). Qed.
Lemma lem1578511 (y : real) (x : real) (z : real) : (term89 y x z) = (term90 y x z).
Proof. exact (@lem1483519 (term7 x y z) (term7 y x z)). Qed.
Lemma lem1578512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1578513 (y : real) (x : real) (z : real) : (term91 y x z) = (term92 y x z).
Proof. exact (MK_COMB (@lem1578512) (@lem1578511 y x z)). Qed.
Lemma lem1578514 (y : real) (x : real) (z : real) : (term92 y x z) = (term93 y x z).
Proof. exact (@lem1483512 (term90 y x z)). Qed.
Lemma lem1578515 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1483508 (term7 x y z) term28 (term63 y x z)). Qed.
Lemma lem1578516 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (@lem1483476 term28 term28 (term7 y x z)). Qed.
Lemma lem1578518 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1578519 : term34 = term35.
Proof. exact (@lem1578518 term36 term36). Qed.
Lemma lem1578520 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1578521 : term38 = term36.
Proof. exact (EQ_MP (@lem1578520) (@lem940073)). Qed.
Lemma lem1578522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1578523 : term35 = term39.
Proof. exact (MK_COMB (@lem1578522) (@lem1578521)). Qed.
Lemma lem1578524 : term34 = term39.
Proof. exact (TRANS (@lem1578519) (@lem1578523)). Qed.
Lemma lem1578525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578526 : term40 = term41.
Proof. exact (MK_COMB (@lem1578525) (@lem1578524)). Qed.
Lemma lem1578527 (y : real) (x : real) (z : real) : (term7 y x z) = (term7 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem1578528 (y : real) (x : real) (z : real) : (term70 y x z) = (term71 y x z).
Proof. exact (MK_COMB (@lem1578526) (@lem1578527 y x z)). Qed.
Lemma lem1578529 (y : real) (x : real) (z : real) : (term69 y x z) = (term71 y x z).
Proof. exact (TRANS (@lem1578516 y x z) (@lem1578528 y x z)). Qed.
Lemma lem1578530 (y : real) (x : real) (z : real) : (term71 y x z) = (term7 y x z).
Proof. exact (@lem1483436 (term7 y x z)). Qed.
Lemma lem1578531 (y : real) (x : real) (z : real) : (term69 y x z) = (term7 y x z).
Proof. exact (TRANS (@lem1578529 y x z) (@lem1578530 y x z)). Qed.
Lemma lem1578534 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1578535 (y : real) (x : real) (z : real) : (term94 y x z) = (term96 y x z).
Proof. exact (MK_COMB (@lem1578534 x y z) (@lem1578531 y x z)). Qed.
Lemma lem1578536 (y : real) (x : real) (z : real) : (term93 y x z) = (term96 y x z).
Proof. exact (TRANS (@lem1578515 y x z) (@lem1578535 y x z)). Qed.
Lemma lem1578537 (y : real) (x : real) (z : real) : (term92 y x z) = (term96 y x z).
Proof. exact (TRANS (@lem1578514 y x z) (@lem1578536 y x z)). Qed.
Lemma lem1578538 (y : real) (x : real) (z : real) : (term97 y x z) = (term97 y x z).
Proof. exact (eq_refl (term97 y x z)). Qed.
Lemma lem1578539 (y : real) (x : real) (z : real) : ((term91 y x z) = (term92 y x z)) = ((term91 y x z) = (term96 y x z)).
Proof. exact (MK_COMB (@lem1578538 y x z) (@lem1578537 y x z)). Qed.
Lemma lem1578540 (y : real) (x : real) (z : real) : (term91 y x z) = (term96 y x z).
Proof. exact (EQ_MP (@lem1578539 y x z) (@lem1578513 y x z)). Qed.
Lemma lem1578541 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578542 (y : real) (x : real) (z : real) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1578541) (@lem1578540 y x z)). Qed.
Lemma lem1578543 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578544 (y : real) (x : real) (z : real) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1578542 y x z) (@lem1578543)). Qed.
Lemma lem1578545 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578546 (y : real) (x : real) (z : real) : (term102 y x z) = (term103 y x z).
Proof. exact (MK_COMB (@lem1578545) (@lem1578511 y x z)). Qed.
Lemma lem1578547 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578548 (y : real) (x : real) (z : real) : (term104 y x z) = (term105 y x z).
Proof. exact (MK_COMB (@lem1578546 y x z) (@lem1578547)). Qed.
Lemma lem1578549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578550 (y : real) (x : real) (z : real) : (term106 y x z) = (term107 y x z).
Proof. exact (MK_COMB (@lem1578549) (@lem1578548 y x z)). Qed.
Lemma lem1578551 (y : real) (x : real) (z : real) : (term88 y x z) = (term108 y x z).
Proof. exact (MK_COMB (@lem1578550 y x z) (@lem1578544 y x z)). Qed.
Lemma lem1578552 (y : real) (x : real) (z : real) : (term87 y x z) = (term108 y x z).
Proof. exact (TRANS (@lem1578498 y x z) (@lem1578551 y x z)). Qed.
Lemma lem1578553 (x : real) : (term109 x) = (term110 x).
Proof. exact (@lem1483554 (real_min x x) x). Qed.
Lemma lem1578559 (x : real) : (term111 x) = (term112 x).
Proof. exact (@lem1483519 (real_min x x) x). Qed.
Lemma lem1578564 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem1483488 (term114 x) (real_min x x)). Qed.
Lemma lem1578566 (x : real) : (term111 x) = (term113 x).
Proof. exact (TRANS (@lem1578559 x) (@lem1578564 x)). Qed.
Lemma lem1578567 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1578568 (x : real) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem1578567) (@lem1578566 x)). Qed.
Lemma lem1578569 (x : real) : (term116 x) = (term117 x).
Proof. exact (@lem1483512 (term113 x)). Qed.
Lemma lem1578570 (x : real) : (term117 x) = (term118 x).
Proof. exact (@lem1483508 (term114 x) term28 (real_min x x)). Qed.
Lemma lem1578571 (x : real) : (term119 x) = (term119 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1578572 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1578574 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1578575 : term34 = term35.
Proof. exact (@lem1578574 term36 term36). Qed.
Lemma lem1578576 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1578577 : term38 = term36.
Proof. exact (EQ_MP (@lem1578576) (@lem940073)). Qed.
Lemma lem1578578 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1578579 : term35 = term39.
Proof. exact (MK_COMB (@lem1578578) (@lem1578577)). Qed.
Lemma lem1578580 : term34 = term39.
Proof. exact (TRANS (@lem1578575) (@lem1578579)). Qed.
Lemma lem1578581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578582 : term40 = term41.
Proof. exact (MK_COMB (@lem1578581) (@lem1578580)). Qed.
Lemma lem1578583 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1578584 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1578582) (@lem1578583 x)). Qed.
Lemma lem1578585 (x : real) : (term120 x) = (term122 x).
Proof. exact (TRANS (@lem1578572 x) (@lem1578584 x)). Qed.
Lemma lem1578586 (x : real) : (term122 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1578587 (x : real) : (term120 x) = x.
Proof. exact (TRANS (@lem1578585 x) (@lem1578586 x)). Qed.
Lemma lem1578588 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1578589 (x : real) : (term123 x) = (real_add x).
Proof. exact (MK_COMB (@lem1578588) (@lem1578587 x)). Qed.
Lemma lem1578590 (x : real) : (term118 x) = (term124 x).
Proof. exact (MK_COMB (@lem1578589 x) (@lem1578571 x)). Qed.
Lemma lem1578591 (x : real) : (term117 x) = (term124 x).
Proof. exact (TRANS (@lem1578570 x) (@lem1578590 x)). Qed.
Lemma lem1578592 (x : real) : (term116 x) = (term124 x).
Proof. exact (TRANS (@lem1578569 x) (@lem1578591 x)). Qed.
Lemma lem1578593 (x : real) : (term125 x) = (term125 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1578594 (x : real) : ((term115 x) = (term116 x)) = ((term115 x) = (term124 x)).
Proof. exact (MK_COMB (@lem1578593 x) (@lem1578592 x)). Qed.
Lemma lem1578595 (x : real) : (term115 x) = (term124 x).
Proof. exact (EQ_MP (@lem1578594 x) (@lem1578568 x)). Qed.
Lemma lem1578596 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578597 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1578596) (@lem1578595 x)). Qed.
Lemma lem1578598 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578599 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1578597 x) (@lem1578598)). Qed.
Lemma lem1578600 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578601 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1578600) (@lem1578566 x)). Qed.
Lemma lem1578602 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578603 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1578601 x) (@lem1578602)). Qed.
Lemma lem1578604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578605 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1578604) (@lem1578603 x)). Qed.
Lemma lem1578606 (x : real) : (term110 x) = (term136 x).
Proof. exact (MK_COMB (@lem1578605 x) (@lem1578599 x)). Qed.
Lemma lem1578607 (x : real) : (term109 x) = (term136 x).
Proof. exact (TRANS (@lem1578553 x) (@lem1578606 x)). Qed.
Lemma lem1578608 (x : real) (y : real) : (term137 x y) = (term138 x y).
Proof. exact (@lem1483554 (term2 x y) (real_min x y)). Qed.
Lemma lem1578614 (x : real) (y : real) : (term139 x y) = (term140 x y).
Proof. exact (@lem1483519 (term2 x y) (real_min x y)). Qed.
Lemma lem1578619 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (@lem1483488 (term29 x y) (term2 x y)). Qed.
Lemma lem1578621 (x : real) (y : real) : (term139 x y) = (term141 x y).
Proof. exact (TRANS (@lem1578614 x y) (@lem1578619 x y)). Qed.
Lemma lem1578622 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1578623 (x : real) (y : real) : (term142 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1578622) (@lem1578621 x y)). Qed.
Lemma lem1578624 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (@lem1483512 (term141 x y)). Qed.
Lemma lem1578625 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1483508 (term29 x y) term28 (term2 x y)). Qed.
Lemma lem1578626 (x : real) (y : real) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem1578627 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483476 term28 term28 (real_min x y)). Qed.
Lemma lem1578629 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1578630 : term34 = term35.
Proof. exact (@lem1578629 term36 term36). Qed.
Lemma lem1578631 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1578632 : term38 = term36.
Proof. exact (EQ_MP (@lem1578631) (@lem940073)). Qed.
Lemma lem1578633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1578634 : term35 = term39.
Proof. exact (MK_COMB (@lem1578633) (@lem1578632)). Qed.
Lemma lem1578635 : term34 = term39.
Proof. exact (TRANS (@lem1578630) (@lem1578634)). Qed.
Lemma lem1578636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578637 : term40 = term41.
Proof. exact (MK_COMB (@lem1578636) (@lem1578635)). Qed.
Lemma lem1578638 (x : real) (y : real) : (real_min x y) = (real_min x y).
Proof. exact (eq_refl (real_min x y)). Qed.
Lemma lem1578639 (x : real) (y : real) : (term31 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1578637) (@lem1578638 x y)). Qed.
Lemma lem1578640 (x : real) (y : real) : (term30 x y) = (term42 x y).
Proof. exact (TRANS (@lem1578627 x y) (@lem1578639 x y)). Qed.
Lemma lem1578641 (x : real) (y : real) : (term42 x y) = (real_min x y).
Proof. exact (@lem1483436 (real_min x y)). Qed.
Lemma lem1578642 (x : real) (y : real) : (term30 x y) = (real_min x y).
Proof. exact (TRANS (@lem1578640 x y) (@lem1578641 x y)). Qed.
Lemma lem1578643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1578644 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1578643) (@lem1578642 x y)). Qed.
Lemma lem1578645 (x : real) (y : real) : (term145 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1578644 x y) (@lem1578626 x y)). Qed.
Lemma lem1578646 (x : real) (y : real) : (term144 x y) = (term149 x y).
Proof. exact (TRANS (@lem1578625 x y) (@lem1578645 x y)). Qed.
Lemma lem1578647 (x : real) (y : real) : (term143 x y) = (term149 x y).
Proof. exact (TRANS (@lem1578624 x y) (@lem1578646 x y)). Qed.
Lemma lem1578648 (x : real) (y : real) : (term150 x y) = (term150 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1578649 (x : real) (y : real) : ((term142 x y) = (term143 x y)) = ((term142 x y) = (term149 x y)).
Proof. exact (MK_COMB (@lem1578648 x y) (@lem1578647 x y)). Qed.
Lemma lem1578650 (x : real) (y : real) : (term142 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem1578649 x y) (@lem1578623 x y)). Qed.
Lemma lem1578651 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578652 (x : real) (y : real) : (term151 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem1578651) (@lem1578650 x y)). Qed.
Lemma lem1578653 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578654 (x : real) (y : real) : (term153 x y) = (term154 x y).
Proof. exact (MK_COMB (@lem1578652 x y) (@lem1578653)). Qed.
Lemma lem1578655 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578656 (x : real) (y : real) : (term155 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem1578655) (@lem1578621 x y)). Qed.
Lemma lem1578657 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578658 (x : real) (y : real) : (term157 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1578656 x y) (@lem1578657)). Qed.
Lemma lem1578659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578660 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1578659) (@lem1578658 x y)). Qed.
Lemma lem1578661 (x : real) (y : real) : (term138 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1578660 x y) (@lem1578654 x y)). Qed.
Lemma lem1578662 (x : real) (y : real) : (term137 x y) = (term161 x y).
Proof. exact (TRANS (@lem1578608 x y) (@lem1578661 x y)). Qed.
Lemma lem1578663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578664 (x : real) : (term162 x) = (term163 x).
Proof. exact (MK_COMB (@lem1578663) (@lem1578607 x)). Qed.
Lemma lem1578665 (x : real) (y : real) : (term1 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1578664 x) (@lem1578662 x y)). Qed.
Lemma lem1578666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578667 (y : real) (x : real) (z : real) : (term3 y x z) = (term165 y x z).
Proof. exact (MK_COMB (@lem1578666) (@lem1578552 y x z)). Qed.
Lemma lem1578668 (z : real) (x : real) (y : real) : (term5 z x y) = (term166 z x y).
Proof. exact (MK_COMB (@lem1578667 y x z) (@lem1578665 x y)). Qed.
Lemma lem1578669 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578670 (x : real) (y : real) (z : real) : (term9 x y z) = (term167 x y z).
Proof. exact (MK_COMB (@lem1578669) (@lem1578497 x y z)). Qed.
Lemma lem1578671 (z : real) (x : real) (y : real) : (term11 z x y) = (term168 z x y).
Proof. exact (MK_COMB (@lem1578670 x y z) (@lem1578668 z x y)). Qed.
Lemma lem1578672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578673 (y : real) (x : real) : (term15 y x) = (term169 y x).
Proof. exact (MK_COMB (@lem1578672) (@lem1578442 y x)). Qed.
Lemma lem1578674 (z : real) (x : real) (y : real) : (term17 z x y) = (term170 z x y).
Proof. exact (MK_COMB (@lem1578673 y x) (@lem1578671 z x y)). Qed.
Lemma lem1578719 (z : real) (x : real) (y : real) : (term18 z x y) = (term170 z x y).
Proof. exact (TRANS (@lem1578387 z x y) (@lem1578674 z x y)). Qed.
Lemma lem1578721 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1578722 (x : real) (y : real) : (term54 y x) = (term173 x y).
Proof. exact (@lem1578721 x (term29 y x) y term48). Qed.
Lemma lem1578735 (y : real) (x : real) : (term174 x y) = (term175 y x).
Proof. exact (@lem1483488 y (term29 y x)). Qed.
Lemma lem1578736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578737 (y : real) (x : real) : (term176 x y) = (term177 y x).
Proof. exact (MK_COMB (@lem1578736) (@lem1578735 y x)). Qed.
Lemma lem1578738 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578739 (y : real) (x : real) : (term178 x y) = (term179 y x).
Proof. exact (MK_COMB (@lem1578737 y x) (@lem1578738)). Qed.
Lemma lem1578752 (y : real) (x : real) : (term180 y x) = (term181 y x).
Proof. exact (@lem1483488 x (term29 y x)). Qed.
Lemma lem1578753 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578754 (y : real) (x : real) : (term182 y x) = (term183 y x).
Proof. exact (MK_COMB (@lem1578753) (@lem1578752 y x)). Qed.
Lemma lem1578755 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578756 (y : real) (x : real) : (term184 y x) = (term185 y x).
Proof. exact (MK_COMB (@lem1578754 y x) (@lem1578755)). Qed.
Lemma lem1578757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1578758 (y : real) (x : real) : (term186 y x) = (term187 y x).
Proof. exact (MK_COMB (@lem1578757) (@lem1578756 y x)). Qed.
Lemma lem1578759 (y : real) (x : real) : (term173 x y) = (term188 y x).
Proof. exact (MK_COMB (@lem1578758 y x) (@lem1578739 y x)). Qed.
Lemma lem1578760 (y : real) (x : real) : (term54 y x) = (term188 y x).
Proof. exact (TRANS (@lem1578722 x y) (@lem1578759 y x)). Qed.
Lemma lem1578761 (y : real) (x : real) : (term189 y x) = (term188 y x).
Proof. exact (eq_refl (term189 y x)). Qed.
Lemma lem1578762 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (SYM (@lem1578761 y x)). Qed.
Lemma lem1578763 (y : real) (x : real) : (term189 y x) = (term190 y x).
Proof. exact (@lem1483429 y (term191 x y) x). Qed.
Lemma lem1578764 (y : real) (x : real) : (term188 y x) = (term190 y x).
Proof. exact (TRANS (@lem1578762 y x) (@lem1578763 y x)). Qed.
Lemma lem1578765 (y : real) (x : real) : (term192 y x) = (term193 y x).
Proof. exact (eq_refl (term192 y x)). Qed.
Lemma lem1578766 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1578767 (y : real) (x : real) : (term195 y x) = (term196 y x).
Proof. exact (MK_COMB (@lem1578766 y x) (@lem1578765 y x)). Qed.
Lemma lem1578768 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (eq_refl (term197 x y)). Qed.
Lemma lem1578769 (x : real) (y : real) : (term199 x y) = (term199 x y).
Proof. exact (eq_refl (term199 x y)). Qed.
Lemma lem1578770 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1578769 x y) (@lem1578768 x y)). Qed.
Lemma lem1578771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578772 (x : real) (y : real) : (term202 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1578771) (@lem1578770 x y)). Qed.
Lemma lem1578773 (y : real) (x : real) : (term190 y x) = (term204 y x).
Proof. exact (MK_COMB (@lem1578772 x y) (@lem1578767 y x)). Qed.
Lemma lem1578774 (y : real) (x : real) : (term205 y x) = (term205 y x).
Proof. exact (eq_refl (term205 y x)). Qed.
Lemma lem1578775 (y : real) (x : real) : ((term188 y x) = (term190 y x)) = ((term188 y x) = (term204 y x)).
Proof. exact (MK_COMB (@lem1578774 y x) (@lem1578773 y x)). Qed.
Lemma lem1578776 (y : real) (x : real) : (term188 y x) = (term204 y x).
Proof. exact (EQ_MP (@lem1578775 y x) (@lem1578764 y x)). Qed.
Lemma lem1578777 (x : real) (y : real) : (real_ge x y) = (term206 x y).
Proof. exact (@lem1483527 x y). Qed.
Lemma lem1578790 (x : real) (y : real) : (real_sub x y) = (term207 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1578791 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1578792 (x : real) (y : real) : (term208 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1578791) (@lem1578790 x y)). Qed.
Lemma lem1578793 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578794 (x : real) (y : real) : (term206 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1578792 x y) (@lem1578793)). Qed.
Lemma lem1578795 (x : real) (y : real) : (real_ge x y) = (term210 x y).
Proof. exact (TRANS (@lem1578777 x y) (@lem1578794 x y)). Qed.
Lemma lem1578796 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1483525 (term207 x y) term48). Qed.
Lemma lem1578814 (x : real) (y : real) : (term213 x y) = (term214 x y).
Proof. exact (@lem1483519 (term207 x y) term48). Qed.
Lemma lem1578816 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1578817 : term216 = term48.
Proof. exact (@lem1578816 term36). Qed.
Lemma lem1578818 (x : real) (y : real) : (term217 x y) = (term217 x y).
Proof. exact (eq_refl (term217 x y)). Qed.
Lemma lem1578819 (x : real) (y : real) : (term214 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1578818 x y) (@lem1578817)). Qed.
Lemma lem1578820 (x : real) (y : real) : (term218 x y) = (term207 x y).
Proof. exact (@lem1483450 (term207 x y)). Qed.
Lemma lem1578821 (x : real) (y : real) : (term214 x y) = (term207 x y).
Proof. exact (TRANS (@lem1578819 x y) (@lem1578820 x y)). Qed.
Lemma lem1578823 (x : real) (y : real) : (term213 x y) = (term207 x y).
Proof. exact (TRANS (@lem1578814 x y) (@lem1578821 x y)). Qed.
Lemma lem1578824 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578825 (x : real) (y : real) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1578824) (@lem1578823 x y)). Qed.
Lemma lem1578826 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578827 (x : real) (y : real) : (term212 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1578825 x y) (@lem1578826)). Qed.
Lemma lem1578828 (x : real) (y : real) : (term211 x y) = (term211 x y).
Proof. exact (TRANS (@lem1578796 x y) (@lem1578827 x y)). Qed.
Lemma lem1578829 (y : real) : (term221 y) = (term222 y).
Proof. exact (@lem1483525 (term223 y) term48). Qed.
Lemma lem1578830 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578842 (y : real) : (term223 y) = (term224 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1578844 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1578845 : term226 = term48.
Proof. exact (@lem1578844 term36). Qed.
Lemma lem1578846 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578847 : term227 = term228.
Proof. exact (MK_COMB (@lem1578846) (@lem1578845)). Qed.
Lemma lem1578848 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1578849 (y : real) : (term224 y) = (term229 y).
Proof. exact (MK_COMB (@lem1578847) (@lem1578848 y)). Qed.
Lemma lem1578850 (y : real) : (term223 y) = (term229 y).
Proof. exact (TRANS (@lem1578842 y) (@lem1578849 y)). Qed.
Lemma lem1578851 (y : real) : (term229 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1578853 (y : real) : (term223 y) = term48.
Proof. exact (TRANS (@lem1578850 y) (@lem1578851 y)). Qed.
Lemma lem1578854 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1578855 (y : real) : (term230 y) = term231.
Proof. exact (MK_COMB (@lem1578854) (@lem1578853 y)). Qed.
Lemma lem1578856 (y : real) : (term232 y) = term233.
Proof. exact (MK_COMB (@lem1578855 y) (@lem1578830)). Qed.
Lemma lem1578857 : term233 = term234.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1578859 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1578860 : term216 = term48.
Proof. exact (@lem1578859 term36). Qed.
Lemma lem1578861 : term235 = term235.
Proof. exact (eq_refl term235). Qed.
Lemma lem1578862 : term234 = term236.
Proof. exact (MK_COMB (@lem1578861) (@lem1578860)). Qed.
Lemma lem1578863 : term236 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1578864 : term234 = term48.
Proof. exact (TRANS (@lem1578862) (@lem1578863)). Qed.
Lemma lem1578865 : term233 = term48.
Proof. exact (TRANS (@lem1578857) (@lem1578864)). Qed.
Lemma lem1578866 (y : real) : (term232 y) = term48.
Proof. exact (TRANS (@lem1578856 y) (@lem1578865)). Qed.
Lemma lem1578867 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578868 (y : real) : (term237 y) = term238.
Proof. exact (MK_COMB (@lem1578867) (@lem1578866 y)). Qed.
Lemma lem1578869 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578870 (y : real) : (term222 y) = term239.
Proof. exact (MK_COMB (@lem1578868 y) (@lem1578869)). Qed.
Lemma lem1578871 (y : real) : (term221 y) = term239.
Proof. exact (TRANS (@lem1578829 y) (@lem1578870 y)). Qed.
Lemma lem1578872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1578873 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1578872) (@lem1578828 x y)). Qed.
Lemma lem1578874 (x : real) (y : real) : (term198 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1578873 x y) (@lem1578871 y)). Qed.
Lemma lem1578875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1578876 (x : real) (y : real) : (term199 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1578875) (@lem1578795 x y)). Qed.
Lemma lem1578877 (x : real) (y : real) : (term201 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1578876 x y) (@lem1578874 x y)). Qed.
Lemma lem1578878 (y : real) (x : real) : (real_gt y x) = (term244 y x).
Proof. exact (@lem1483525 y x). Qed.
Lemma lem1578884 (y : real) (x : real) : (real_sub y x) = (term207 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1578889 (x : real) (y : real) : (term207 y x) = (term245 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1578891 (x : real) (y : real) : (real_sub y x) = (term245 x y).
Proof. exact (TRANS (@lem1578884 y x) (@lem1578889 x y)). Qed.
Lemma lem1578892 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578893 (x : real) (y : real) : (term246 y x) = (term247 x y).
Proof. exact (MK_COMB (@lem1578892) (@lem1578891 x y)). Qed.
Lemma lem1578894 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578895 (x : real) (y : real) : (term244 y x) = (term248 x y).
Proof. exact (MK_COMB (@lem1578893 x y) (@lem1578894)). Qed.
Lemma lem1578896 (x : real) (y : real) : (real_gt y x) = (term248 x y).
Proof. exact (TRANS (@lem1578878 y x) (@lem1578895 x y)). Qed.
Lemma lem1578897 (x : real) : (term221 x) = (term222 x).
Proof. exact (@lem1483525 (term223 x) term48). Qed.
Lemma lem1578898 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578910 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1578912 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1578913 : term226 = term48.
Proof. exact (@lem1578912 term36). Qed.
Lemma lem1578914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1578915 : term227 = term228.
Proof. exact (MK_COMB (@lem1578914) (@lem1578913)). Qed.
Lemma lem1578916 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1578917 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1578915) (@lem1578916 x)). Qed.
Lemma lem1578918 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1578910 x) (@lem1578917 x)). Qed.
Lemma lem1578919 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1578921 (x : real) : (term223 x) = term48.
Proof. exact (TRANS (@lem1578918 x) (@lem1578919 x)). Qed.
Lemma lem1578922 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1578923 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1578922) (@lem1578921 x)). Qed.
Lemma lem1578924 (x : real) : (term232 x) = term233.
Proof. exact (MK_COMB (@lem1578923 x) (@lem1578898)). Qed.
Lemma lem1578925 : term233 = term234.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1578927 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1578928 : term216 = term48.
Proof. exact (@lem1578927 term36). Qed.
Lemma lem1578929 : term235 = term235.
Proof. exact (eq_refl term235). Qed.
Lemma lem1578930 : term234 = term236.
Proof. exact (MK_COMB (@lem1578929) (@lem1578928)). Qed.
Lemma lem1578931 : term236 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1578932 : term234 = term48.
Proof. exact (TRANS (@lem1578930) (@lem1578931)). Qed.
Lemma lem1578933 : term233 = term48.
Proof. exact (TRANS (@lem1578925) (@lem1578932)). Qed.
Lemma lem1578934 (x : real) : (term232 x) = term48.
Proof. exact (TRANS (@lem1578924 x) (@lem1578933)). Qed.
Lemma lem1578935 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578936 (x : real) : (term237 x) = term238.
Proof. exact (MK_COMB (@lem1578935) (@lem1578934 x)). Qed.
Lemma lem1578937 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578938 (x : real) : (term222 x) = term239.
Proof. exact (MK_COMB (@lem1578936 x) (@lem1578937)). Qed.
Lemma lem1578939 (x : real) : (term221 x) = term239.
Proof. exact (TRANS (@lem1578897 x) (@lem1578938 x)). Qed.
Lemma lem1578940 (y : real) (x : real) : (term211 y x) = (term212 y x).
Proof. exact (@lem1483525 (term207 y x) term48). Qed.
Lemma lem1578941 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578954 (x : real) (y : real) : (term207 y x) = (term245 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1578955 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1578956 (x : real) (y : real) : (term249 y x) = (term250 x y).
Proof. exact (MK_COMB (@lem1578955) (@lem1578954 x y)). Qed.
Lemma lem1578957 (x : real) (y : real) : (term213 y x) = (term251 x y).
Proof. exact (MK_COMB (@lem1578956 x y) (@lem1578941)). Qed.
Lemma lem1578958 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (@lem1483519 (term245 x y) term48). Qed.
Lemma lem1578960 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1578961 : term216 = term48.
Proof. exact (@lem1578960 term36). Qed.
Lemma lem1578962 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem1578963 (x : real) (y : real) : (term252 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1578962 x y) (@lem1578961)). Qed.
Lemma lem1578964 (x : real) (y : real) : (term254 x y) = (term245 x y).
Proof. exact (@lem1483450 (term245 x y)). Qed.
Lemma lem1578965 (x : real) (y : real) : (term252 x y) = (term245 x y).
Proof. exact (TRANS (@lem1578963 x y) (@lem1578964 x y)). Qed.
Lemma lem1578966 (x : real) (y : real) : (term251 x y) = (term245 x y).
Proof. exact (TRANS (@lem1578958 x y) (@lem1578965 x y)). Qed.
Lemma lem1578967 (x : real) (y : real) : (term213 y x) = (term245 x y).
Proof. exact (TRANS (@lem1578957 x y) (@lem1578966 x y)). Qed.
Lemma lem1578968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1578969 (x : real) (y : real) : (term219 y x) = (term247 x y).
Proof. exact (MK_COMB (@lem1578968) (@lem1578967 x y)). Qed.
Lemma lem1578970 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1578971 (x : real) (y : real) : (term212 y x) = (term248 x y).
Proof. exact (MK_COMB (@lem1578969 x y) (@lem1578970)). Qed.
Lemma lem1578972 (x : real) (y : real) : (term211 y x) = (term248 x y).
Proof. exact (TRANS (@lem1578940 y x) (@lem1578971 x y)). Qed.
Lemma lem1578973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1578974 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1578973) (@lem1578939 x)). Qed.
Lemma lem1578975 (x : real) (y : real) : (term193 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1578974 x) (@lem1578972 x y)). Qed.
Lemma lem1578976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1578977 (x : real) (y : real) : (term194 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1578976) (@lem1578896 x y)). Qed.
Lemma lem1578978 (x : real) (y : real) : (term196 y x) = (term259 x y).
Proof. exact (MK_COMB (@lem1578977 x y) (@lem1578975 x y)). Qed.
Lemma lem1578979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1578980 (x : real) (y : real) : (term203 x y) = (term260 x y).
Proof. exact (MK_COMB (@lem1578979) (@lem1578877 x y)). Qed.
Lemma lem1578981 (x : real) (y : real) : (term204 y x) = (term261 x y).
Proof. exact (MK_COMB (@lem1578980 x y) (@lem1578978 x y)). Qed.
Lemma lem1578992 (x : real) (y : real) : (term188 y x) = (term261 x y).
Proof. exact (TRANS (@lem1578776 y x) (@lem1578981 x y)). Qed.
Lemma lem1578993 (x : real) (y : real) : (term54 y x) = (term261 x y).
Proof. exact (TRANS (@lem1578760 y x) (@lem1578992 x y)). Qed.
Lemma lem1578995 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1578996 (y : real) (x : real) : (term50 y x) = (term173 y x).
Proof. exact (@lem1578995 y (term29 x y) x term48). Qed.
Lemma lem1579009 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 x (term29 x y)). Qed.
Lemma lem1579010 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579011 (x : real) (y : real) : (term176 y x) = (term177 x y).
Proof. exact (MK_COMB (@lem1579010) (@lem1579009 x y)). Qed.
Lemma lem1579012 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579013 (x : real) (y : real) : (term178 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1579011 x y) (@lem1579012)). Qed.
Lemma lem1579026 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (@lem1483488 y (term29 x y)). Qed.
Lemma lem1579027 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579028 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1579027) (@lem1579026 x y)). Qed.
Lemma lem1579029 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579030 (x : real) (y : real) : (term184 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1579028 x y) (@lem1579029)). Qed.
Lemma lem1579031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579032 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1579031) (@lem1579030 x y)). Qed.
Lemma lem1579033 (x : real) (y : real) : (term173 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1579032 x y) (@lem1579013 x y)). Qed.
Lemma lem1579034 (x : real) (y : real) : (term50 y x) = (term188 x y).
Proof. exact (TRANS (@lem1578996 y x) (@lem1579033 x y)). Qed.
Lemma lem1579035 (x : real) (y : real) : (term189 x y) = (term188 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1579036 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (SYM (@lem1579035 x y)). Qed.
Lemma lem1579037 (x : real) (y : real) : (term189 x y) = (term190 x y).
Proof. exact (@lem1483429 x (term191 y x) y). Qed.
Lemma lem1579038 (x : real) (y : real) : (term188 x y) = (term190 x y).
Proof. exact (TRANS (@lem1579036 x y) (@lem1579037 x y)). Qed.
Lemma lem1579039 (x : real) (y : real) : (term192 x y) = (term193 x y).
Proof. exact (eq_refl (term192 x y)). Qed.
Lemma lem1579040 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1579041 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1579040 x y) (@lem1579039 x y)). Qed.
Lemma lem1579042 (y : real) (x : real) : (term197 y x) = (term198 y x).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1579043 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1579044 (y : real) (x : real) : (term200 y x) = (term201 y x).
Proof. exact (MK_COMB (@lem1579043 y x) (@lem1579042 y x)). Qed.
Lemma lem1579045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579046 (y : real) (x : real) : (term202 y x) = (term203 y x).
Proof. exact (MK_COMB (@lem1579045) (@lem1579044 y x)). Qed.
Lemma lem1579047 (x : real) (y : real) : (term190 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1579046 y x) (@lem1579041 x y)). Qed.
Lemma lem1579048 (x : real) (y : real) : (term205 x y) = (term205 x y).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem1579049 (x : real) (y : real) : ((term188 x y) = (term190 x y)) = ((term188 x y) = (term204 x y)).
Proof. exact (MK_COMB (@lem1579048 x y) (@lem1579047 x y)). Qed.
Lemma lem1579050 (x : real) (y : real) : (term188 x y) = (term204 x y).
Proof. exact (EQ_MP (@lem1579049 x y) (@lem1579038 x y)). Qed.
Lemma lem1579051 (y : real) (x : real) : (real_ge y x) = (term206 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1579057 (y : real) (x : real) : (real_sub y x) = (term207 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1579062 (x : real) (y : real) : (term207 y x) = (term245 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1579064 (x : real) (y : real) : (real_sub y x) = (term245 x y).
Proof. exact (TRANS (@lem1579057 y x) (@lem1579062 x y)). Qed.
Lemma lem1579065 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1579066 (x : real) (y : real) : (term208 y x) = (term263 x y).
Proof. exact (MK_COMB (@lem1579065) (@lem1579064 x y)). Qed.
Lemma lem1579067 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579068 (x : real) (y : real) : (term206 y x) = (term264 x y).
Proof. exact (MK_COMB (@lem1579066 x y) (@lem1579067)). Qed.
Lemma lem1579069 (x : real) (y : real) : (real_ge y x) = (term264 x y).
Proof. exact (TRANS (@lem1579051 y x) (@lem1579068 x y)). Qed.
Lemma lem1579070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579071 (x : real) (y : real) : (term240 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1579070) (@lem1578972 x y)). Qed.
Lemma lem1579072 (x : real) (y : real) : (term198 y x) = (term265 x y).
Proof. exact (MK_COMB (@lem1579071 x y) (@lem1578939 x)). Qed.
Lemma lem1579073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579074 (x : real) (y : real) : (term199 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem1579073) (@lem1579069 x y)). Qed.
Lemma lem1579075 (x : real) (y : real) : (term201 y x) = (term267 x y).
Proof. exact (MK_COMB (@lem1579074 x y) (@lem1579072 x y)). Qed.
Lemma lem1579076 (x : real) (y : real) : (real_gt x y) = (term244 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1579089 (x : real) (y : real) : (real_sub x y) = (term207 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1579090 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579091 (x : real) (y : real) : (term246 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1579090) (@lem1579089 x y)). Qed.
Lemma lem1579092 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579093 (x : real) (y : real) : (term244 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1579091 x y) (@lem1579092)). Qed.
Lemma lem1579094 (x : real) (y : real) : (real_gt x y) = (term211 x y).
Proof. exact (TRANS (@lem1579076 x y) (@lem1579093 x y)). Qed.
Lemma lem1579095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579096 (y : real) : (term255 y) = term256.
Proof. exact (MK_COMB (@lem1579095) (@lem1578871 y)). Qed.
Lemma lem1579097 (x : real) (y : real) : (term193 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1579096 y) (@lem1578828 x y)). Qed.
Lemma lem1579098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579099 (x : real) (y : real) : (term194 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1579098) (@lem1579094 x y)). Qed.
Lemma lem1579100 (x : real) (y : real) : (term196 x y) = (term269 x y).
Proof. exact (MK_COMB (@lem1579099 x y) (@lem1579097 x y)). Qed.
Lemma lem1579101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579102 (x : real) (y : real) : (term203 y x) = (term270 x y).
Proof. exact (MK_COMB (@lem1579101) (@lem1579075 x y)). Qed.
Lemma lem1579103 (x : real) (y : real) : (term204 x y) = (term271 x y).
Proof. exact (MK_COMB (@lem1579102 x y) (@lem1579100 x y)). Qed.
Lemma lem1579114 (x : real) (y : real) : (term188 x y) = (term271 x y).
Proof. exact (TRANS (@lem1579050 x y) (@lem1579103 x y)). Qed.
Lemma lem1579115 (x : real) (y : real) : (term50 y x) = (term271 x y).
Proof. exact (TRANS (@lem1579034 x y) (@lem1579114 x y)). Qed.
Lemma lem1579116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579117 (x : real) (y : real) : (term56 y x) = (term272 x y).
Proof. exact (MK_COMB (@lem1579116) (@lem1578993 x y)). Qed.
Lemma lem1579118 (x : real) (y : real) : (term57 y x) = (term273 x y).
Proof. exact (MK_COMB (@lem1579117 x y) (@lem1579115 x y)). Qed.
Lemma lem1579120 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579121 (x : real) (y : real) (z : real) : (term83 x y z) = (term274 x y z).
Proof. exact (@lem1579120 (real_min x y) (term63 x y z) z term48). Qed.
Lemma lem1579134 (x : real) (y : real) (z : real) : (term275 x y z) = (term276 x y z).
Proof. exact (@lem1483488 z (term63 x y z)). Qed.
Lemma lem1579135 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579136 (x : real) (y : real) (z : real) : (term277 x y z) = (term278 x y z).
Proof. exact (MK_COMB (@lem1579135) (@lem1579134 x y z)). Qed.
Lemma lem1579137 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579138 (x : real) (y : real) (z : real) : (term279 x y z) = (term280 x y z).
Proof. exact (MK_COMB (@lem1579136 x y z) (@lem1579137)). Qed.
Lemma lem1579151 (x : real) (y : real) (z : real) : (term281 z x y) = (term282 x y z).
Proof. exact (@lem1483488 (real_min x y) (term63 x y z)). Qed.
Lemma lem1579152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579153 (x : real) (y : real) (z : real) : (term283 z x y) = (term284 x y z).
Proof. exact (MK_COMB (@lem1579152) (@lem1579151 x y z)). Qed.
Lemma lem1579154 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579155 (x : real) (y : real) (z : real) : (term285 z x y) = (term286 x y z).
Proof. exact (MK_COMB (@lem1579153 x y z) (@lem1579154)). Qed.
Lemma lem1579156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579157 (x : real) (y : real) (z : real) : (term287 z x y) = (term288 x y z).
Proof. exact (MK_COMB (@lem1579156) (@lem1579155 x y z)). Qed.
Lemma lem1579158 (x : real) (y : real) (z : real) : (term274 x y z) = (term289 x y z).
Proof. exact (MK_COMB (@lem1579157 x y z) (@lem1579138 x y z)). Qed.
Lemma lem1579159 (x : real) (y : real) (z : real) : (term83 x y z) = (term289 x y z).
Proof. exact (TRANS (@lem1579121 x y z) (@lem1579158 x y z)). Qed.
Lemma lem1579161 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579162 (x : real) (z : real) (y : real) : (term286 x y z) = (term290 x z y).
Proof. exact (@lem1579161 x (term63 x y z) y term48). Qed.
Lemma lem1579175 (x : real) (y : real) (z : real) : (term291 x z y) = (term292 x y z).
Proof. exact (@lem1483488 y (term63 x y z)). Qed.
Lemma lem1579176 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579177 (x : real) (y : real) (z : real) : (term293 x z y) = (term294 x y z).
Proof. exact (MK_COMB (@lem1579176) (@lem1579175 x y z)). Qed.
Lemma lem1579178 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579179 (x : real) (y : real) (z : real) : (term295 x z y) = (term296 x y z).
Proof. exact (MK_COMB (@lem1579177 x y z) (@lem1579178)). Qed.
Lemma lem1579192 (x : real) (y : real) (z : real) : (term297 y z x) = (term298 x y z).
Proof. exact (@lem1483488 x (term63 x y z)). Qed.
Lemma lem1579193 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579194 (x : real) (y : real) (z : real) : (term299 y z x) = (term300 x y z).
Proof. exact (MK_COMB (@lem1579193) (@lem1579192 x y z)). Qed.
Lemma lem1579195 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579196 (x : real) (y : real) (z : real) : (term301 y z x) = (term302 x y z).
Proof. exact (MK_COMB (@lem1579194 x y z) (@lem1579195)). Qed.
Lemma lem1579197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579198 (x : real) (y : real) (z : real) : (term303 y z x) = (term304 x y z).
Proof. exact (MK_COMB (@lem1579197) (@lem1579196 x y z)). Qed.
Lemma lem1579199 (x : real) (y : real) (z : real) : (term290 x z y) = (term305 x y z).
Proof. exact (MK_COMB (@lem1579198 x y z) (@lem1579179 x y z)). Qed.
Lemma lem1579200 (x : real) (y : real) (z : real) : (term286 x y z) = (term305 x y z).
Proof. exact (TRANS (@lem1579162 x z y) (@lem1579199 x y z)). Qed.
Lemma lem1579201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579202 (x : real) (y : real) (z : real) : (term288 x y z) = (term306 x y z).
Proof. exact (MK_COMB (@lem1579201) (@lem1579200 x y z)). Qed.
Lemma lem1579203 (x : real) (y : real) (z : real) : (term280 x y z) = (term280 x y z).
Proof. exact (eq_refl (term280 x y z)). Qed.
Lemma lem1579204 (x : real) (y : real) (z : real) : (term289 x y z) = (term307 x y z).
Proof. exact (MK_COMB (@lem1579202 x y z) (@lem1579203 x y z)). Qed.
Lemma lem1579205 (x : real) (y : real) (z : real) : (term83 x y z) = (term307 x y z).
Proof. exact (TRANS (@lem1579159 x y z) (@lem1579204 x y z)). Qed.
Lemma lem1579206 (x : real) (y : real) (z : real) : (term308 x y z) = (term307 x y z).
Proof. exact (eq_refl (term308 x y z)). Qed.
Lemma lem1579207 (x : real) (y : real) (z : real) : (term307 x y z) = (term308 x y z).
Proof. exact (SYM (@lem1579206 x y z)). Qed.
Lemma lem1579208 (x : real) (y : real) (z : real) : (term308 x y z) = (term309 x y z).
Proof. exact (@lem1483429 x (term310 x y z) (real_min y z)). Qed.
Lemma lem1579209 (x : real) (y : real) (z : real) : (term307 x y z) = (term309 x y z).
Proof. exact (TRANS (@lem1579207 x y z) (@lem1579208 x y z)). Qed.
Lemma lem1579210 (x : real) (y : real) (z : real) : (term311 x y z) = (term312 x y z).
Proof. exact (eq_refl (term311 x y z)). Qed.
Lemma lem1579211 (x : real) (y : real) (z : real) : (term313 x y z) = (term313 x y z).
Proof. exact (eq_refl (term313 x y z)). Qed.
Lemma lem1579212 (x : real) (y : real) (z : real) : (term314 x y z) = (term315 x y z).
Proof. exact (MK_COMB (@lem1579211 x y z) (@lem1579210 x y z)). Qed.
Lemma lem1579213 (y : real) (z : real) (x : real) : (term316 y z x) = (term317 y z x).
Proof. exact (eq_refl (term316 y z x)). Qed.
Lemma lem1579214 (y : real) (z : real) (x : real) : (term318 y z x) = (term318 y z x).
Proof. exact (eq_refl (term318 y z x)). Qed.
Lemma lem1579215 (y : real) (z : real) (x : real) : (term319 y z x) = (term320 y z x).
Proof. exact (MK_COMB (@lem1579214 y z x) (@lem1579213 y z x)). Qed.
Lemma lem1579216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579217 (y : real) (z : real) (x : real) : (term321 y z x) = (term322 y z x).
Proof. exact (MK_COMB (@lem1579216) (@lem1579215 y z x)). Qed.
Lemma lem1579218 (x : real) (y : real) (z : real) : (term309 x y z) = (term323 x y z).
Proof. exact (MK_COMB (@lem1579217 y z x) (@lem1579212 x y z)). Qed.
Lemma lem1579219 (x : real) (y : real) (z : real) : (term324 x y z) = (term324 x y z).
Proof. exact (eq_refl (term324 x y z)). Qed.
Lemma lem1579220 (x : real) (y : real) (z : real) : ((term307 x y z) = (term309 x y z)) = ((term307 x y z) = (term323 x y z)).
Proof. exact (MK_COMB (@lem1579219 x y z) (@lem1579218 x y z)). Qed.
Lemma lem1579221 (x : real) (y : real) (z : real) : (term307 x y z) = (term323 x y z).
Proof. exact (EQ_MP (@lem1579220 x y z) (@lem1579209 x y z)). Qed.
Lemma lem1579222 (y : real) (z : real) (x : real) : (term325 y z x) = (term326 y z x).
Proof. exact (@lem1483527 (real_min y z) x). Qed.
Lemma lem1579228 (y : real) (z : real) (x : real) : (term327 y z x) = (term328 y z x).
Proof. exact (@lem1483519 (real_min y z) x). Qed.
Lemma lem1579233 (x : real) (y : real) (z : real) : (term328 y z x) = (term329 x y z).
Proof. exact (@lem1483488 (term114 x) (real_min y z)). Qed.
Lemma lem1579235 (x : real) (y : real) (z : real) : (term327 y z x) = (term329 x y z).
Proof. exact (TRANS (@lem1579228 y z x) (@lem1579233 x y z)). Qed.
Lemma lem1579236 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1579237 (x : real) (y : real) (z : real) : (term330 y z x) = (term331 x y z).
Proof. exact (MK_COMB (@lem1579236) (@lem1579235 x y z)). Qed.
Lemma lem1579238 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579239 (x : real) (y : real) (z : real) : (term326 y z x) = (term332 x y z).
Proof. exact (MK_COMB (@lem1579237 x y z) (@lem1579238)). Qed.
Lemma lem1579240 (x : real) (y : real) (z : real) : (term325 y z x) = (term332 x y z).
Proof. exact (TRANS (@lem1579222 y z x) (@lem1579239 x y z)). Qed.
Lemma lem1579241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579242 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1579241) (@lem1578939 x)). Qed.
Lemma lem1579243 (x : real) (y : real) : (term193 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1579242 x) (@lem1578972 x y)). Qed.
Lemma lem1579244 (z : real) (x : real) : (term211 z x) = (term212 z x).
Proof. exact (@lem1483525 (term207 z x) term48). Qed.
Lemma lem1579245 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579258 (x : real) (z : real) : (term207 z x) = (term245 x z).
Proof. exact (@lem1483488 (term114 x) z). Qed.
Lemma lem1579259 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1579260 (x : real) (z : real) : (term249 z x) = (term250 x z).
Proof. exact (MK_COMB (@lem1579259) (@lem1579258 x z)). Qed.
Lemma lem1579261 (x : real) (z : real) : (term213 z x) = (term251 x z).
Proof. exact (MK_COMB (@lem1579260 x z) (@lem1579245)). Qed.
Lemma lem1579262 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483519 (term245 x z) term48). Qed.
Lemma lem1579264 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579265 : term216 = term48.
Proof. exact (@lem1579264 term36). Qed.
Lemma lem1579266 (x : real) (z : real) : (term253 x z) = (term253 x z).
Proof. exact (eq_refl (term253 x z)). Qed.
Lemma lem1579267 (x : real) (z : real) : (term252 x z) = (term254 x z).
Proof. exact (MK_COMB (@lem1579266 x z) (@lem1579265)). Qed.
Lemma lem1579268 (x : real) (z : real) : (term254 x z) = (term245 x z).
Proof. exact (@lem1483450 (term245 x z)). Qed.
Lemma lem1579269 (x : real) (z : real) : (term252 x z) = (term245 x z).
Proof. exact (TRANS (@lem1579267 x z) (@lem1579268 x z)). Qed.
Lemma lem1579270 (x : real) (z : real) : (term251 x z) = (term245 x z).
Proof. exact (TRANS (@lem1579262 x z) (@lem1579269 x z)). Qed.
Lemma lem1579271 (x : real) (z : real) : (term213 z x) = (term245 x z).
Proof. exact (TRANS (@lem1579261 x z) (@lem1579270 x z)). Qed.
Lemma lem1579272 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579273 (x : real) (z : real) : (term219 z x) = (term247 x z).
Proof. exact (MK_COMB (@lem1579272) (@lem1579271 x z)). Qed.
Lemma lem1579274 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579275 (x : real) (z : real) : (term212 z x) = (term248 x z).
Proof. exact (MK_COMB (@lem1579273 x z) (@lem1579274)). Qed.
Lemma lem1579276 (x : real) (z : real) : (term211 z x) = (term248 x z).
Proof. exact (TRANS (@lem1579244 z x) (@lem1579275 x z)). Qed.
Lemma lem1579277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579278 (x : real) (y : real) : (term333 y x) = (term334 x y).
Proof. exact (MK_COMB (@lem1579277) (@lem1579243 x y)). Qed.
Lemma lem1579279 (y : real) (x : real) (z : real) : (term317 y z x) = (term335 y x z).
Proof. exact (MK_COMB (@lem1579278 x y) (@lem1579276 x z)). Qed.
Lemma lem1579280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579281 (x : real) (y : real) (z : real) : (term318 y z x) = (term336 x y z).
Proof. exact (MK_COMB (@lem1579280) (@lem1579240 x y z)). Qed.
Lemma lem1579282 (y : real) (x : real) (z : real) : (term320 y z x) = (term337 y x z).
Proof. exact (MK_COMB (@lem1579281 x y z) (@lem1579279 y x z)). Qed.
Lemma lem1579283 (x : real) (y : real) (z : real) : (term338 x y z) = (term339 x y z).
Proof. exact (@lem1483525 x (real_min y z)). Qed.
Lemma lem1579296 (x : real) (y : real) (z : real) : (term340 x y z) = (term341 x y z).
Proof. exact (@lem1483519 x (real_min y z)). Qed.
Lemma lem1579297 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579298 (x : real) (y : real) (z : real) : (term342 x y z) = (term343 x y z).
Proof. exact (MK_COMB (@lem1579297) (@lem1579296 x y z)). Qed.
Lemma lem1579299 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579300 (x : real) (y : real) (z : real) : (term339 x y z) = (term344 x y z).
Proof. exact (MK_COMB (@lem1579298 x y z) (@lem1579299)). Qed.
Lemma lem1579301 (x : real) (y : real) (z : real) : (term338 x y z) = (term344 x y z).
Proof. exact (TRANS (@lem1579283 x y z) (@lem1579300 x y z)). Qed.
Lemma lem1579302 (x : real) (y : real) (z : real) : (term344 x y z) = (term345 x y z).
Proof. exact (@lem1483525 (term341 x y z) term48). Qed.
Lemma lem1579320 (x : real) (y : real) (z : real) : (term346 x y z) = (term347 x y z).
Proof. exact (@lem1483519 (term341 x y z) term48). Qed.
Lemma lem1579322 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579323 : term216 = term48.
Proof. exact (@lem1579322 term36). Qed.
Lemma lem1579324 (x : real) (y : real) (z : real) : (term348 x y z) = (term348 x y z).
Proof. exact (eq_refl (term348 x y z)). Qed.
Lemma lem1579325 (x : real) (y : real) (z : real) : (term347 x y z) = (term349 x y z).
Proof. exact (MK_COMB (@lem1579324 x y z) (@lem1579323)). Qed.
Lemma lem1579326 (x : real) (y : real) (z : real) : (term349 x y z) = (term341 x y z).
Proof. exact (@lem1483450 (term341 x y z)). Qed.
Lemma lem1579327 (x : real) (y : real) (z : real) : (term347 x y z) = (term341 x y z).
Proof. exact (TRANS (@lem1579325 x y z) (@lem1579326 x y z)). Qed.
Lemma lem1579329 (x : real) (y : real) (z : real) : (term346 x y z) = (term341 x y z).
Proof. exact (TRANS (@lem1579320 x y z) (@lem1579327 x y z)). Qed.
Lemma lem1579330 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579331 (x : real) (y : real) (z : real) : (term350 x y z) = (term343 x y z).
Proof. exact (MK_COMB (@lem1579330) (@lem1579329 x y z)). Qed.
Lemma lem1579332 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579333 (x : real) (y : real) (z : real) : (term345 x y z) = (term344 x y z).
Proof. exact (MK_COMB (@lem1579331 x y z) (@lem1579332)). Qed.
Lemma lem1579334 (x : real) (y : real) (z : real) : (term344 x y z) = (term344 x y z).
Proof. exact (TRANS (@lem1579302 x y z) (@lem1579333 x y z)). Qed.
Lemma lem1579335 (y : real) (z : real) : (term179 y z) = (term351 y z).
Proof. exact (@lem1483525 (term175 y z) term48). Qed.
Lemma lem1579353 (y : real) (z : real) : (term352 y z) = (term353 y z).
Proof. exact (@lem1483519 (term175 y z) term48). Qed.
Lemma lem1579355 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579356 : term216 = term48.
Proof. exact (@lem1579355 term36). Qed.
Lemma lem1579357 (y : real) (z : real) : (term354 y z) = (term354 y z).
Proof. exact (eq_refl (term354 y z)). Qed.
Lemma lem1579358 (y : real) (z : real) : (term353 y z) = (term355 y z).
Proof. exact (MK_COMB (@lem1579357 y z) (@lem1579356)). Qed.
Lemma lem1579359 (y : real) (z : real) : (term355 y z) = (term175 y z).
Proof. exact (@lem1483450 (term175 y z)). Qed.
Lemma lem1579360 (y : real) (z : real) : (term353 y z) = (term175 y z).
Proof. exact (TRANS (@lem1579358 y z) (@lem1579359 y z)). Qed.
Lemma lem1579362 (y : real) (z : real) : (term352 y z) = (term175 y z).
Proof. exact (TRANS (@lem1579353 y z) (@lem1579360 y z)). Qed.
Lemma lem1579363 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579364 (y : real) (z : real) : (term356 y z) = (term177 y z).
Proof. exact (MK_COMB (@lem1579363) (@lem1579362 y z)). Qed.
Lemma lem1579365 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579366 (y : real) (z : real) : (term351 y z) = (term179 y z).
Proof. exact (MK_COMB (@lem1579364 y z) (@lem1579365)). Qed.
Lemma lem1579367 (y : real) (z : real) : (term179 y z) = (term179 y z).
Proof. exact (TRANS (@lem1579335 y z) (@lem1579366 y z)). Qed.
Lemma lem1579368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579369 (x : real) (y : real) (z : real) : (term357 x y z) = (term357 x y z).
Proof. exact (MK_COMB (@lem1579368) (@lem1579334 x y z)). Qed.
Lemma lem1579370 (x : real) (y : real) (z : real) : (term358 x y z) = (term358 x y z).
Proof. exact (MK_COMB (@lem1579369 x y z) (@lem1579367 y z)). Qed.
Lemma lem1579371 (y : real) (z : real) : (term185 y z) = (term359 y z).
Proof. exact (@lem1483525 (term181 y z) term48). Qed.
Lemma lem1579389 (y : real) (z : real) : (term360 y z) = (term361 y z).
Proof. exact (@lem1483519 (term181 y z) term48). Qed.
Lemma lem1579391 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579392 : term216 = term48.
Proof. exact (@lem1579391 term36). Qed.
Lemma lem1579393 (y : real) (z : real) : (term362 y z) = (term362 y z).
Proof. exact (eq_refl (term362 y z)). Qed.
Lemma lem1579394 (y : real) (z : real) : (term361 y z) = (term363 y z).
Proof. exact (MK_COMB (@lem1579393 y z) (@lem1579392)). Qed.
Lemma lem1579395 (y : real) (z : real) : (term363 y z) = (term181 y z).
Proof. exact (@lem1483450 (term181 y z)). Qed.
Lemma lem1579396 (y : real) (z : real) : (term361 y z) = (term181 y z).
Proof. exact (TRANS (@lem1579394 y z) (@lem1579395 y z)). Qed.
Lemma lem1579398 (y : real) (z : real) : (term360 y z) = (term181 y z).
Proof. exact (TRANS (@lem1579389 y z) (@lem1579396 y z)). Qed.
Lemma lem1579399 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579400 (y : real) (z : real) : (term364 y z) = (term183 y z).
Proof. exact (MK_COMB (@lem1579399) (@lem1579398 y z)). Qed.
Lemma lem1579401 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579402 (y : real) (z : real) : (term359 y z) = (term185 y z).
Proof. exact (MK_COMB (@lem1579400 y z) (@lem1579401)). Qed.
Lemma lem1579403 (y : real) (z : real) : (term185 y z) = (term185 y z).
Proof. exact (TRANS (@lem1579371 y z) (@lem1579402 y z)). Qed.
Lemma lem1579404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579405 (x : real) (y : real) (z : real) : (term365 x y z) = (term365 x y z).
Proof. exact (MK_COMB (@lem1579404) (@lem1579370 x y z)). Qed.
Lemma lem1579406 (x : real) (y : real) (z : real) : (term312 x y z) = (term312 x y z).
Proof. exact (MK_COMB (@lem1579405 x y z) (@lem1579403 y z)). Qed.
Lemma lem1579407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579408 (x : real) (y : real) (z : real) : (term313 x y z) = (term357 x y z).
Proof. exact (MK_COMB (@lem1579407) (@lem1579301 x y z)). Qed.
Lemma lem1579409 (x : real) (y : real) (z : real) : (term315 x y z) = (term366 x y z).
Proof. exact (MK_COMB (@lem1579408 x y z) (@lem1579406 x y z)). Qed.
Lemma lem1579410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579411 (y : real) (x : real) (z : real) : (term322 y z x) = (term367 y x z).
Proof. exact (MK_COMB (@lem1579410) (@lem1579282 y x z)). Qed.
Lemma lem1579412 (x : real) (y : real) (z : real) : (term323 x y z) = (term368 x y z).
Proof. exact (MK_COMB (@lem1579411 y x z) (@lem1579409 x y z)). Qed.
Lemma lem1579413 (x : real) (y : real) (z : real) : (term307 x y z) = (term368 x y z).
Proof. exact (TRANS (@lem1579221 x y z) (@lem1579412 x y z)). Qed.
Lemma lem1579415 (x : real) (y : real) (z : real) : (term369 x y z) = (term366 x y z).
Proof. exact (eq_refl (term369 x y z)). Qed.
Lemma lem1579416 (x : real) (y : real) (z : real) : (term366 x y z) = (term369 x y z).
Proof. exact (SYM (@lem1579415 x y z)). Qed.
Lemma lem1579417 (x : real) (y : real) (z : real) : (term369 x y z) = (term370 x y z).
Proof. exact (@lem1483429 y (term371 x y z) z). Qed.
Lemma lem1579418 (x : real) (y : real) (z : real) : (term366 x y z) = (term370 x y z).
Proof. exact (TRANS (@lem1579416 x y z) (@lem1579417 x y z)). Qed.
Lemma lem1579419 (x : real) (y : real) (z : real) : (term372 x y z) = (term373 x y z).
Proof. exact (eq_refl (term372 x y z)). Qed.
Lemma lem1579420 (y : real) (z : real) : (term194 y z) = (term194 y z).
Proof. exact (eq_refl (term194 y z)). Qed.
Lemma lem1579421 (x : real) (y : real) (z : real) : (term374 x y z) = (term375 x y z).
Proof. exact (MK_COMB (@lem1579420 y z) (@lem1579419 x y z)). Qed.
Lemma lem1579422 (x : real) (z : real) (y : real) : (term376 x z y) = (term377 x z y).
Proof. exact (eq_refl (term376 x z y)). Qed.
Lemma lem1579423 (z : real) (y : real) : (term199 z y) = (term199 z y).
Proof. exact (eq_refl (term199 z y)). Qed.
Lemma lem1579424 (x : real) (z : real) (y : real) : (term378 x z y) = (term379 x z y).
Proof. exact (MK_COMB (@lem1579423 z y) (@lem1579422 x z y)). Qed.
Lemma lem1579425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579426 (x : real) (z : real) (y : real) : (term380 x z y) = (term381 x z y).
Proof. exact (MK_COMB (@lem1579425) (@lem1579424 x z y)). Qed.
Lemma lem1579427 (x : real) (y : real) (z : real) : (term370 x y z) = (term382 x y z).
Proof. exact (MK_COMB (@lem1579426 x z y) (@lem1579421 x y z)). Qed.
Lemma lem1579428 (x : real) (y : real) (z : real) : (term383 x y z) = (term383 x y z).
Proof. exact (eq_refl (term383 x y z)). Qed.
Lemma lem1579429 (x : real) (y : real) (z : real) : ((term366 x y z) = (term370 x y z)) = ((term366 x y z) = (term382 x y z)).
Proof. exact (MK_COMB (@lem1579428 x y z) (@lem1579427 x y z)). Qed.
Lemma lem1579430 (x : real) (y : real) (z : real) : (term366 x y z) = (term382 x y z).
Proof. exact (EQ_MP (@lem1579429 x y z) (@lem1579418 x y z)). Qed.
Lemma lem1579431 (z : real) (y : real) : (real_ge z y) = (term206 z y).
Proof. exact (@lem1483527 z y). Qed.
Lemma lem1579437 (z : real) (y : real) : (real_sub z y) = (term207 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1579442 (y : real) (z : real) : (term207 z y) = (term245 y z).
Proof. exact (@lem1483488 (term114 y) z). Qed.
Lemma lem1579444 (y : real) (z : real) : (real_sub z y) = (term245 y z).
Proof. exact (TRANS (@lem1579437 z y) (@lem1579442 y z)). Qed.
Lemma lem1579445 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1579446 (y : real) (z : real) : (term208 z y) = (term263 y z).
Proof. exact (MK_COMB (@lem1579445) (@lem1579444 y z)). Qed.
Lemma lem1579447 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579448 (y : real) (z : real) : (term206 z y) = (term264 y z).
Proof. exact (MK_COMB (@lem1579446 y z) (@lem1579447)). Qed.
Lemma lem1579449 (y : real) (z : real) : (real_ge z y) = (term264 y z).
Proof. exact (TRANS (@lem1579431 z y) (@lem1579448 y z)). Qed.
Lemma lem1579450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579451 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1579450) (@lem1578828 x y)). Qed.
Lemma lem1579452 (x : real) (y : real) : (term198 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1579451 x y) (@lem1578871 y)). Qed.
Lemma lem1579453 (z : real) (y : real) : (term211 z y) = (term212 z y).
Proof. exact (@lem1483525 (term207 z y) term48). Qed.
Lemma lem1579454 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579467 (y : real) (z : real) : (term207 z y) = (term245 y z).
Proof. exact (@lem1483488 (term114 y) z). Qed.
Lemma lem1579468 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1579469 (y : real) (z : real) : (term249 z y) = (term250 y z).
Proof. exact (MK_COMB (@lem1579468) (@lem1579467 y z)). Qed.
Lemma lem1579470 (y : real) (z : real) : (term213 z y) = (term251 y z).
Proof. exact (MK_COMB (@lem1579469 y z) (@lem1579454)). Qed.
Lemma lem1579471 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483519 (term245 y z) term48). Qed.
Lemma lem1579473 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579474 : term216 = term48.
Proof. exact (@lem1579473 term36). Qed.
Lemma lem1579475 (y : real) (z : real) : (term253 y z) = (term253 y z).
Proof. exact (eq_refl (term253 y z)). Qed.
Lemma lem1579476 (y : real) (z : real) : (term252 y z) = (term254 y z).
Proof. exact (MK_COMB (@lem1579475 y z) (@lem1579474)). Qed.
Lemma lem1579477 (y : real) (z : real) : (term254 y z) = (term245 y z).
Proof. exact (@lem1483450 (term245 y z)). Qed.
Lemma lem1579478 (y : real) (z : real) : (term252 y z) = (term245 y z).
Proof. exact (TRANS (@lem1579476 y z) (@lem1579477 y z)). Qed.
Lemma lem1579479 (y : real) (z : real) : (term251 y z) = (term245 y z).
Proof. exact (TRANS (@lem1579471 y z) (@lem1579478 y z)). Qed.
Lemma lem1579480 (y : real) (z : real) : (term213 z y) = (term245 y z).
Proof. exact (TRANS (@lem1579470 y z) (@lem1579479 y z)). Qed.
Lemma lem1579481 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579482 (y : real) (z : real) : (term219 z y) = (term247 y z).
Proof. exact (MK_COMB (@lem1579481) (@lem1579480 y z)). Qed.
Lemma lem1579483 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579484 (y : real) (z : real) : (term212 z y) = (term248 y z).
Proof. exact (MK_COMB (@lem1579482 y z) (@lem1579483)). Qed.
Lemma lem1579485 (y : real) (z : real) : (term211 z y) = (term248 y z).
Proof. exact (TRANS (@lem1579453 z y) (@lem1579484 y z)). Qed.
Lemma lem1579486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579487 (x : real) (y : real) : (term384 x y) = (term385 x y).
Proof. exact (MK_COMB (@lem1579486) (@lem1579452 x y)). Qed.
Lemma lem1579488 (x : real) (y : real) (z : real) : (term386 x z y) = (term387 x y z).
Proof. exact (MK_COMB (@lem1579487 x y) (@lem1579485 y z)). Qed.
Lemma lem1579489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579490 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1579489) (@lem1578828 x y)). Qed.
Lemma lem1579491 (x : real) (y : real) (z : real) : (term377 x z y) = (term388 x y z).
Proof. exact (MK_COMB (@lem1579490 x y) (@lem1579488 x y z)). Qed.
Lemma lem1579492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579493 (y : real) (z : real) : (term199 z y) = (term266 y z).
Proof. exact (MK_COMB (@lem1579492) (@lem1579449 y z)). Qed.
Lemma lem1579494 (x : real) (y : real) (z : real) : (term379 x z y) = (term389 x y z).
Proof. exact (MK_COMB (@lem1579493 y z) (@lem1579491 x y z)). Qed.
Lemma lem1579495 (y : real) (z : real) : (real_gt y z) = (term244 y z).
Proof. exact (@lem1483525 y z). Qed.
Lemma lem1579508 (y : real) (z : real) : (real_sub y z) = (term207 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1579509 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579510 (y : real) (z : real) : (term246 y z) = (term220 y z).
Proof. exact (MK_COMB (@lem1579509) (@lem1579508 y z)). Qed.
Lemma lem1579511 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579512 (y : real) (z : real) : (term244 y z) = (term211 y z).
Proof. exact (MK_COMB (@lem1579510 y z) (@lem1579511)). Qed.
Lemma lem1579513 (y : real) (z : real) : (real_gt y z) = (term211 y z).
Proof. exact (TRANS (@lem1579495 y z) (@lem1579512 y z)). Qed.
Lemma lem1579514 (x : real) (z : real) : (term211 x z) = (term212 x z).
Proof. exact (@lem1483525 (term207 x z) term48). Qed.
Lemma lem1579532 (x : real) (z : real) : (term213 x z) = (term214 x z).
Proof. exact (@lem1483519 (term207 x z) term48). Qed.
Lemma lem1579534 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579535 : term216 = term48.
Proof. exact (@lem1579534 term36). Qed.
Lemma lem1579536 (x : real) (z : real) : (term217 x z) = (term217 x z).
Proof. exact (eq_refl (term217 x z)). Qed.
Lemma lem1579537 (x : real) (z : real) : (term214 x z) = (term218 x z).
Proof. exact (MK_COMB (@lem1579536 x z) (@lem1579535)). Qed.
Lemma lem1579538 (x : real) (z : real) : (term218 x z) = (term207 x z).
Proof. exact (@lem1483450 (term207 x z)). Qed.
Lemma lem1579539 (x : real) (z : real) : (term214 x z) = (term207 x z).
Proof. exact (TRANS (@lem1579537 x z) (@lem1579538 x z)). Qed.
Lemma lem1579541 (x : real) (z : real) : (term213 x z) = (term207 x z).
Proof. exact (TRANS (@lem1579532 x z) (@lem1579539 x z)). Qed.
Lemma lem1579542 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579543 (x : real) (z : real) : (term219 x z) = (term220 x z).
Proof. exact (MK_COMB (@lem1579542) (@lem1579541 x z)). Qed.
Lemma lem1579544 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579545 (x : real) (z : real) : (term212 x z) = (term211 x z).
Proof. exact (MK_COMB (@lem1579543 x z) (@lem1579544)). Qed.
Lemma lem1579546 (x : real) (z : real) : (term211 x z) = (term211 x z).
Proof. exact (TRANS (@lem1579514 x z) (@lem1579545 x z)). Qed.
Lemma lem1579547 (y : real) (z : real) : (term211 y z) = (term212 y z).
Proof. exact (@lem1483525 (term207 y z) term48). Qed.
Lemma lem1579565 (y : real) (z : real) : (term213 y z) = (term214 y z).
Proof. exact (@lem1483519 (term207 y z) term48). Qed.
Lemma lem1579567 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579568 : term216 = term48.
Proof. exact (@lem1579567 term36). Qed.
Lemma lem1579569 (y : real) (z : real) : (term217 y z) = (term217 y z).
Proof. exact (eq_refl (term217 y z)). Qed.
Lemma lem1579570 (y : real) (z : real) : (term214 y z) = (term218 y z).
Proof. exact (MK_COMB (@lem1579569 y z) (@lem1579568)). Qed.
Lemma lem1579571 (y : real) (z : real) : (term218 y z) = (term207 y z).
Proof. exact (@lem1483450 (term207 y z)). Qed.
Lemma lem1579572 (y : real) (z : real) : (term214 y z) = (term207 y z).
Proof. exact (TRANS (@lem1579570 y z) (@lem1579571 y z)). Qed.
Lemma lem1579574 (y : real) (z : real) : (term213 y z) = (term207 y z).
Proof. exact (TRANS (@lem1579565 y z) (@lem1579572 y z)). Qed.
Lemma lem1579575 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579576 (y : real) (z : real) : (term219 y z) = (term220 y z).
Proof. exact (MK_COMB (@lem1579575) (@lem1579574 y z)). Qed.
Lemma lem1579577 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579578 (y : real) (z : real) : (term212 y z) = (term211 y z).
Proof. exact (MK_COMB (@lem1579576 y z) (@lem1579577)). Qed.
Lemma lem1579579 (y : real) (z : real) : (term211 y z) = (term211 y z).
Proof. exact (TRANS (@lem1579547 y z) (@lem1579578 y z)). Qed.
Lemma lem1579580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579581 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1579580) (@lem1579546 x z)). Qed.
Lemma lem1579582 (x : real) (y : real) (z : real) : (term390 x y z) = (term390 x y z).
Proof. exact (MK_COMB (@lem1579581 x z) (@lem1579579 y z)). Qed.
Lemma lem1579583 (z : real) : (term221 z) = (term222 z).
Proof. exact (@lem1483525 (term223 z) term48). Qed.
Lemma lem1579584 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579596 (z : real) : (term223 z) = (term224 z).
Proof. exact (@lem1483442 term28 z). Qed.
Lemma lem1579598 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1579599 : term226 = term48.
Proof. exact (@lem1579598 term36). Qed.
Lemma lem1579600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1579601 : term227 = term228.
Proof. exact (MK_COMB (@lem1579600) (@lem1579599)). Qed.
Lemma lem1579602 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1579603 (z : real) : (term224 z) = (term229 z).
Proof. exact (MK_COMB (@lem1579601) (@lem1579602 z)). Qed.
Lemma lem1579604 (z : real) : (term223 z) = (term229 z).
Proof. exact (TRANS (@lem1579596 z) (@lem1579603 z)). Qed.
Lemma lem1579605 (z : real) : (term229 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1579607 (z : real) : (term223 z) = term48.
Proof. exact (TRANS (@lem1579604 z) (@lem1579605 z)). Qed.
Lemma lem1579608 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1579609 (z : real) : (term230 z) = term231.
Proof. exact (MK_COMB (@lem1579608) (@lem1579607 z)). Qed.
Lemma lem1579610 (z : real) : (term232 z) = term233.
Proof. exact (MK_COMB (@lem1579609 z) (@lem1579584)). Qed.
Lemma lem1579611 : term233 = term234.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1579613 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579614 : term216 = term48.
Proof. exact (@lem1579613 term36). Qed.
Lemma lem1579615 : term235 = term235.
Proof. exact (eq_refl term235). Qed.
Lemma lem1579616 : term234 = term236.
Proof. exact (MK_COMB (@lem1579615) (@lem1579614)). Qed.
Lemma lem1579617 : term236 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1579618 : term234 = term48.
Proof. exact (TRANS (@lem1579616) (@lem1579617)). Qed.
Lemma lem1579619 : term233 = term48.
Proof. exact (TRANS (@lem1579611) (@lem1579618)). Qed.
Lemma lem1579620 (z : real) : (term232 z) = term48.
Proof. exact (TRANS (@lem1579610 z) (@lem1579619)). Qed.
Lemma lem1579621 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579622 (z : real) : (term237 z) = term238.
Proof. exact (MK_COMB (@lem1579621) (@lem1579620 z)). Qed.
Lemma lem1579623 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579624 (z : real) : (term222 z) = term239.
Proof. exact (MK_COMB (@lem1579622 z) (@lem1579623)). Qed.
Lemma lem1579625 (z : real) : (term221 z) = term239.
Proof. exact (TRANS (@lem1579583 z) (@lem1579624 z)). Qed.
Lemma lem1579626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579627 (x : real) (y : real) (z : real) : (term391 x y z) = (term391 x y z).
Proof. exact (MK_COMB (@lem1579626) (@lem1579582 x y z)). Qed.
Lemma lem1579628 (x : real) (y : real) (z : real) : (term392 x y z) = (term393 x y z).
Proof. exact (MK_COMB (@lem1579627 x y z) (@lem1579625 z)). Qed.
Lemma lem1579629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579630 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1579629) (@lem1579546 x z)). Qed.
Lemma lem1579631 (x : real) (y : real) (z : real) : (term373 x y z) = (term394 x y z).
Proof. exact (MK_COMB (@lem1579630 x z) (@lem1579628 x y z)). Qed.
Lemma lem1579632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579633 (y : real) (z : real) : (term194 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1579632) (@lem1579513 y z)). Qed.
Lemma lem1579634 (x : real) (y : real) (z : real) : (term375 x y z) = (term395 x y z).
Proof. exact (MK_COMB (@lem1579633 y z) (@lem1579631 x y z)). Qed.
Lemma lem1579635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579636 (x : real) (y : real) (z : real) : (term381 x z y) = (term396 x y z).
Proof. exact (MK_COMB (@lem1579635) (@lem1579494 x y z)). Qed.
Lemma lem1579637 (x : real) (y : real) (z : real) : (term382 x y z) = (term397 x y z).
Proof. exact (MK_COMB (@lem1579636 x y z) (@lem1579634 x y z)). Qed.
Lemma lem1579649 (x : real) (y : real) (z : real) : (term366 x y z) = (term397 x y z).
Proof. exact (TRANS (@lem1579430 x y z) (@lem1579637 x y z)). Qed.
Lemma lem1579651 (x : real) (a : real) (y : real) (r : real) : (term398 a x y r) = (term399 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579690 (y : real) (x : real) (z : real) : (term332 x y z) = (term400 y x z).
Proof. exact (@lem1579651 y (term114 x) z term48). Qed.
Lemma lem1579691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579692 (y : real) (x : real) (z : real) : (term336 x y z) = (term401 y x z).
Proof. exact (MK_COMB (@lem1579691) (@lem1579690 y x z)). Qed.
Lemma lem1579693 (y : real) (x : real) (z : real) : (term335 y x z) = (term335 y x z).
Proof. exact (eq_refl (term335 y x z)). Qed.
Lemma lem1579696 (y : real) (x : real) (z : real) : (term337 y x z) = (term402 y x z).
Proof. exact (MK_COMB (@lem1579692 y x z) (@lem1579693 y x z)). Qed.
Lemma lem1579697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579698 (y : real) (x : real) (z : real) : (term367 y x z) = (term403 y x z).
Proof. exact (MK_COMB (@lem1579697) (@lem1579696 y x z)). Qed.
Lemma lem1579699 (x : real) (y : real) (z : real) : (term368 x y z) = (term404 x y z).
Proof. exact (MK_COMB (@lem1579698 y x z) (@lem1579649 x y z)). Qed.
Lemma lem1579700 (x : real) (y : real) (z : real) : (term307 x y z) = (term404 x y z).
Proof. exact (TRANS (@lem1579413 x y z) (@lem1579699 x y z)). Qed.
Lemma lem1579701 (x : real) (y : real) (z : real) : (term83 x y z) = (term404 x y z).
Proof. exact (TRANS (@lem1579205 x y z) (@lem1579700 x y z)). Qed.
Lemma lem1579703 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579704 (x : real) (y : real) (z : real) : (term79 x y z) = (term405 x y z).
Proof. exact (@lem1579703 x (term68 x y z) (real_min y z) term48). Qed.
Lemma lem1579717 (x : real) (y : real) (z : real) : (term406 x y z) = (term407 x y z).
Proof. exact (@lem1483488 (real_min y z) (term68 x y z)). Qed.
Lemma lem1579718 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579719 (x : real) (y : real) (z : real) : (term408 x y z) = (term409 x y z).
Proof. exact (MK_COMB (@lem1579718) (@lem1579717 x y z)). Qed.
Lemma lem1579720 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579721 (x : real) (y : real) (z : real) : (term410 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem1579719 x y z) (@lem1579720)). Qed.
Lemma lem1579734 (x : real) (y : real) (z : real) : (term412 y z x) = (term413 x y z).
Proof. exact (@lem1483488 x (term68 x y z)). Qed.
Lemma lem1579735 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579736 (x : real) (y : real) (z : real) : (term414 y z x) = (term415 x y z).
Proof. exact (MK_COMB (@lem1579735) (@lem1579734 x y z)). Qed.
Lemma lem1579737 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579738 (x : real) (y : real) (z : real) : (term416 y z x) = (term417 x y z).
Proof. exact (MK_COMB (@lem1579736 x y z) (@lem1579737)). Qed.
Lemma lem1579739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579740 (x : real) (y : real) (z : real) : (term418 y z x) = (term419 x y z).
Proof. exact (MK_COMB (@lem1579739) (@lem1579738 x y z)). Qed.
Lemma lem1579741 (x : real) (y : real) (z : real) : (term405 x y z) = (term420 x y z).
Proof. exact (MK_COMB (@lem1579740 x y z) (@lem1579721 x y z)). Qed.
Lemma lem1579742 (x : real) (y : real) (z : real) : (term79 x y z) = (term420 x y z).
Proof. exact (TRANS (@lem1579704 x y z) (@lem1579741 x y z)). Qed.
Lemma lem1579744 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579745 (x : real) (y : real) (z : real) : (term411 x y z) = (term421 x y z).
Proof. exact (@lem1579744 y (term68 x y z) z term48). Qed.
Lemma lem1579758 (x : real) (y : real) (z : real) : (term422 x y z) = (term423 x y z).
Proof. exact (@lem1483488 z (term68 x y z)). Qed.
Lemma lem1579759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579760 (x : real) (y : real) (z : real) : (term424 x y z) = (term425 x y z).
Proof. exact (MK_COMB (@lem1579759) (@lem1579758 x y z)). Qed.
Lemma lem1579761 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579762 (x : real) (y : real) (z : real) : (term426 x y z) = (term427 x y z).
Proof. exact (MK_COMB (@lem1579760 x y z) (@lem1579761)). Qed.
Lemma lem1579775 (x : real) (y : real) (z : real) : (term428 x z y) = (term429 x y z).
Proof. exact (@lem1483488 y (term68 x y z)). Qed.
Lemma lem1579776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579777 (x : real) (y : real) (z : real) : (term430 x z y) = (term431 x y z).
Proof. exact (MK_COMB (@lem1579776) (@lem1579775 x y z)). Qed.
Lemma lem1579778 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579779 (x : real) (y : real) (z : real) : (term432 x z y) = (term433 x y z).
Proof. exact (MK_COMB (@lem1579777 x y z) (@lem1579778)). Qed.
Lemma lem1579780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579781 (x : real) (y : real) (z : real) : (term434 x z y) = (term435 x y z).
Proof. exact (MK_COMB (@lem1579780) (@lem1579779 x y z)). Qed.
Lemma lem1579782 (x : real) (y : real) (z : real) : (term421 x y z) = (term436 x y z).
Proof. exact (MK_COMB (@lem1579781 x y z) (@lem1579762 x y z)). Qed.
Lemma lem1579783 (x : real) (y : real) (z : real) : (term411 x y z) = (term436 x y z).
Proof. exact (TRANS (@lem1579745 x y z) (@lem1579782 x y z)). Qed.
Lemma lem1579784 (x : real) (y : real) (z : real) : (term419 x y z) = (term419 x y z).
Proof. exact (eq_refl (term419 x y z)). Qed.
Lemma lem1579785 (x : real) (y : real) (z : real) : (term420 x y z) = (term437 x y z).
Proof. exact (MK_COMB (@lem1579784 x y z) (@lem1579783 x y z)). Qed.
Lemma lem1579786 (x : real) (y : real) (z : real) : (term79 x y z) = (term437 x y z).
Proof. exact (TRANS (@lem1579742 x y z) (@lem1579785 x y z)). Qed.
Lemma lem1579787 (x : real) (y : real) (z : real) : (term438 x y z) = (term437 x y z).
Proof. exact (eq_refl (term438 x y z)). Qed.
Lemma lem1579788 (x : real) (y : real) (z : real) : (term437 x y z) = (term438 x y z).
Proof. exact (SYM (@lem1579787 x y z)). Qed.
Lemma lem1579789 (x : real) (y : real) (z : real) : (term438 x y z) = (term439 x y z).
Proof. exact (@lem1483429 (real_min x y) (term440 x y z) z). Qed.
Lemma lem1579790 (x : real) (y : real) (z : real) : (term437 x y z) = (term439 x y z).
Proof. exact (TRANS (@lem1579788 x y z) (@lem1579789 x y z)). Qed.
Lemma lem1579791 (x : real) (y : real) (z : real) : (term441 x y z) = (term442 x y z).
Proof. exact (eq_refl (term441 x y z)). Qed.
Lemma lem1579792 (x : real) (y : real) (z : real) : (term443 x y z) = (term443 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1579793 (x : real) (y : real) (z : real) : (term444 x y z) = (term445 x y z).
Proof. exact (MK_COMB (@lem1579792 x y z) (@lem1579791 x y z)). Qed.
Lemma lem1579794 (z : real) (x : real) (y : real) : (term446 z x y) = (term447 z x y).
Proof. exact (eq_refl (term446 z x y)). Qed.
Lemma lem1579795 (z : real) (x : real) (y : real) : (term448 z x y) = (term448 z x y).
Proof. exact (eq_refl (term448 z x y)). Qed.
Lemma lem1579796 (z : real) (x : real) (y : real) : (term449 z x y) = (term450 z x y).
Proof. exact (MK_COMB (@lem1579795 z x y) (@lem1579794 z x y)). Qed.
Lemma lem1579797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579798 (z : real) (x : real) (y : real) : (term451 z x y) = (term452 z x y).
Proof. exact (MK_COMB (@lem1579797) (@lem1579796 z x y)). Qed.
Lemma lem1579799 (x : real) (y : real) (z : real) : (term439 x y z) = (term453 x y z).
Proof. exact (MK_COMB (@lem1579798 z x y) (@lem1579793 x y z)). Qed.
Lemma lem1579800 (x : real) (y : real) (z : real) : (term454 x y z) = (term454 x y z).
Proof. exact (eq_refl (term454 x y z)). Qed.
Lemma lem1579801 (x : real) (y : real) (z : real) : ((term437 x y z) = (term439 x y z)) = ((term437 x y z) = (term453 x y z)).
Proof. exact (MK_COMB (@lem1579800 x y z) (@lem1579799 x y z)). Qed.
Lemma lem1579802 (x : real) (y : real) (z : real) : (term437 x y z) = (term453 x y z).
Proof. exact (EQ_MP (@lem1579801 x y z) (@lem1579790 x y z)). Qed.
Lemma lem1579803 (z : real) (x : real) (y : real) : (term455 z x y) = (term456 z x y).
Proof. exact (@lem1483527 z (real_min x y)). Qed.
Lemma lem1579816 (z : real) (x : real) (y : real) : (term340 z x y) = (term341 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1579817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1579818 (z : real) (x : real) (y : real) : (term457 z x y) = (term458 z x y).
Proof. exact (MK_COMB (@lem1579817) (@lem1579816 z x y)). Qed.
Lemma lem1579819 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579820 (z : real) (x : real) (y : real) : (term456 z x y) = (term459 z x y).
Proof. exact (MK_COMB (@lem1579818 z x y) (@lem1579819)). Qed.
Lemma lem1579821 (z : real) (x : real) (y : real) : (term455 z x y) = (term459 z x y).
Proof. exact (TRANS (@lem1579803 z x y) (@lem1579820 z x y)). Qed.
Lemma lem1579822 (x : real) (y : real) : (term179 x y) = (term351 x y).
Proof. exact (@lem1483525 (term175 x y) term48). Qed.
Lemma lem1579840 (x : real) (y : real) : (term352 x y) = (term353 x y).
Proof. exact (@lem1483519 (term175 x y) term48). Qed.
Lemma lem1579842 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579843 : term216 = term48.
Proof. exact (@lem1579842 term36). Qed.
Lemma lem1579844 (x : real) (y : real) : (term354 x y) = (term354 x y).
Proof. exact (eq_refl (term354 x y)). Qed.
Lemma lem1579845 (x : real) (y : real) : (term353 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1579844 x y) (@lem1579843)). Qed.
Lemma lem1579846 (x : real) (y : real) : (term355 x y) = (term175 x y).
Proof. exact (@lem1483450 (term175 x y)). Qed.
Lemma lem1579847 (x : real) (y : real) : (term353 x y) = (term175 x y).
Proof. exact (TRANS (@lem1579845 x y) (@lem1579846 x y)). Qed.
Lemma lem1579849 (x : real) (y : real) : (term352 x y) = (term175 x y).
Proof. exact (TRANS (@lem1579840 x y) (@lem1579847 x y)). Qed.
Lemma lem1579850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579851 (x : real) (y : real) : (term356 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem1579850) (@lem1579849 x y)). Qed.
Lemma lem1579852 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579853 (x : real) (y : real) : (term351 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1579851 x y) (@lem1579852)). Qed.
Lemma lem1579854 (x : real) (y : real) : (term179 x y) = (term179 x y).
Proof. exact (TRANS (@lem1579822 x y) (@lem1579853 x y)). Qed.
Lemma lem1579855 (x : real) (y : real) : (term185 x y) = (term359 x y).
Proof. exact (@lem1483525 (term181 x y) term48). Qed.
Lemma lem1579873 (x : real) (y : real) : (term360 x y) = (term361 x y).
Proof. exact (@lem1483519 (term181 x y) term48). Qed.
Lemma lem1579875 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579876 : term216 = term48.
Proof. exact (@lem1579875 term36). Qed.
Lemma lem1579877 (x : real) (y : real) : (term362 x y) = (term362 x y).
Proof. exact (eq_refl (term362 x y)). Qed.
Lemma lem1579878 (x : real) (y : real) : (term361 x y) = (term363 x y).
Proof. exact (MK_COMB (@lem1579877 x y) (@lem1579876)). Qed.
Lemma lem1579879 (x : real) (y : real) : (term363 x y) = (term181 x y).
Proof. exact (@lem1483450 (term181 x y)). Qed.
Lemma lem1579880 (x : real) (y : real) : (term361 x y) = (term181 x y).
Proof. exact (TRANS (@lem1579878 x y) (@lem1579879 x y)). Qed.
Lemma lem1579882 (x : real) (y : real) : (term360 x y) = (term181 x y).
Proof. exact (TRANS (@lem1579873 x y) (@lem1579880 x y)). Qed.
Lemma lem1579883 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579884 (x : real) (y : real) : (term364 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1579883) (@lem1579882 x y)). Qed.
Lemma lem1579885 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579886 (x : real) (y : real) : (term359 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1579884 x y) (@lem1579885)). Qed.
Lemma lem1579887 (x : real) (y : real) : (term185 x y) = (term185 x y).
Proof. exact (TRANS (@lem1579855 x y) (@lem1579886 x y)). Qed.
Lemma lem1579888 (z : real) (x : real) (y : real) : (term344 z x y) = (term345 z x y).
Proof. exact (@lem1483525 (term341 z x y) term48). Qed.
Lemma lem1579906 (z : real) (x : real) (y : real) : (term346 z x y) = (term347 z x y).
Proof. exact (@lem1483519 (term341 z x y) term48). Qed.
Lemma lem1579908 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1579909 : term216 = term48.
Proof. exact (@lem1579908 term36). Qed.
Lemma lem1579910 (z : real) (x : real) (y : real) : (term348 z x y) = (term348 z x y).
Proof. exact (eq_refl (term348 z x y)). Qed.
Lemma lem1579911 (z : real) (x : real) (y : real) : (term347 z x y) = (term349 z x y).
Proof. exact (MK_COMB (@lem1579910 z x y) (@lem1579909)). Qed.
Lemma lem1579912 (z : real) (x : real) (y : real) : (term349 z x y) = (term341 z x y).
Proof. exact (@lem1483450 (term341 z x y)). Qed.
Lemma lem1579913 (z : real) (x : real) (y : real) : (term347 z x y) = (term341 z x y).
Proof. exact (TRANS (@lem1579911 z x y) (@lem1579912 z x y)). Qed.
Lemma lem1579915 (z : real) (x : real) (y : real) : (term346 z x y) = (term341 z x y).
Proof. exact (TRANS (@lem1579906 z x y) (@lem1579913 z x y)). Qed.
Lemma lem1579916 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579917 (z : real) (x : real) (y : real) : (term350 z x y) = (term343 z x y).
Proof. exact (MK_COMB (@lem1579916) (@lem1579915 z x y)). Qed.
Lemma lem1579918 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579919 (z : real) (x : real) (y : real) : (term345 z x y) = (term344 z x y).
Proof. exact (MK_COMB (@lem1579917 z x y) (@lem1579918)). Qed.
Lemma lem1579920 (z : real) (x : real) (y : real) : (term344 z x y) = (term344 z x y).
Proof. exact (TRANS (@lem1579888 z x y) (@lem1579919 z x y)). Qed.
Lemma lem1579921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579922 (x : real) (y : real) : (term187 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1579921) (@lem1579887 x y)). Qed.
Lemma lem1579923 (z : real) (x : real) (y : real) : (term460 z x y) = (term460 z x y).
Proof. exact (MK_COMB (@lem1579922 x y) (@lem1579920 z x y)). Qed.
Lemma lem1579924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579925 (x : real) (y : real) : (term461 x y) = (term461 x y).
Proof. exact (MK_COMB (@lem1579924) (@lem1579854 x y)). Qed.
Lemma lem1579926 (z : real) (x : real) (y : real) : (term447 z x y) = (term447 z x y).
Proof. exact (MK_COMB (@lem1579925 x y) (@lem1579923 z x y)). Qed.
Lemma lem1579927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579928 (z : real) (x : real) (y : real) : (term448 z x y) = (term462 z x y).
Proof. exact (MK_COMB (@lem1579927) (@lem1579821 z x y)). Qed.
Lemma lem1579929 (z : real) (x : real) (y : real) : (term450 z x y) = (term463 z x y).
Proof. exact (MK_COMB (@lem1579928 z x y) (@lem1579926 z x y)). Qed.
Lemma lem1579930 (x : real) (y : real) (z : real) : (term464 x y z) = (term465 x y z).
Proof. exact (@lem1483525 (real_min x y) z). Qed.
Lemma lem1579936 (x : real) (y : real) (z : real) : (term327 x y z) = (term328 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1579941 (z : real) (x : real) (y : real) : (term328 x y z) = (term329 z x y).
Proof. exact (@lem1483488 (term114 z) (real_min x y)). Qed.
Lemma lem1579943 (z : real) (x : real) (y : real) : (term327 x y z) = (term329 z x y).
Proof. exact (TRANS (@lem1579936 x y z) (@lem1579941 z x y)). Qed.
Lemma lem1579944 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579945 (z : real) (x : real) (y : real) : (term466 x y z) = (term467 z x y).
Proof. exact (MK_COMB (@lem1579944) (@lem1579943 z x y)). Qed.
Lemma lem1579946 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579947 (z : real) (x : real) (y : real) : (term465 x y z) = (term468 z x y).
Proof. exact (MK_COMB (@lem1579945 z x y) (@lem1579946)). Qed.
Lemma lem1579948 (z : real) (x : real) (y : real) : (term464 x y z) = (term468 z x y).
Proof. exact (TRANS (@lem1579930 x y z) (@lem1579947 z x y)). Qed.
Lemma lem1579949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579950 (y : real) (z : real) : (term240 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1579949) (@lem1579579 y z)). Qed.
Lemma lem1579951 (y : real) (z : real) : (term198 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1579950 y z) (@lem1579625 z)). Qed.
Lemma lem1579952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579953 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1579952) (@lem1579546 x z)). Qed.
Lemma lem1579954 (x : real) (y : real) (z : real) : (term442 x y z) = (term469 x y z).
Proof. exact (MK_COMB (@lem1579953 x z) (@lem1579951 y z)). Qed.
Lemma lem1579955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1579956 (z : real) (x : real) (y : real) : (term443 x y z) = (term470 z x y).
Proof. exact (MK_COMB (@lem1579955) (@lem1579948 z x y)). Qed.
Lemma lem1579957 (x : real) (y : real) (z : real) : (term445 x y z) = (term471 x y z).
Proof. exact (MK_COMB (@lem1579956 z x y) (@lem1579954 x y z)). Qed.
Lemma lem1579958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1579959 (z : real) (x : real) (y : real) : (term452 z x y) = (term472 z x y).
Proof. exact (MK_COMB (@lem1579958) (@lem1579929 z x y)). Qed.
Lemma lem1579960 (x : real) (y : real) (z : real) : (term453 x y z) = (term473 x y z).
Proof. exact (MK_COMB (@lem1579959 z x y) (@lem1579957 x y z)). Qed.
Lemma lem1579961 (x : real) (y : real) (z : real) : (term437 x y z) = (term473 x y z).
Proof. exact (TRANS (@lem1579802 x y z) (@lem1579960 x y z)). Qed.
Lemma lem1579963 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1579964 (x : real) (z : real) (y : real) : (term468 z x y) = (term474 x z y).
Proof. exact (@lem1579963 x (term114 z) y term48). Qed.
Lemma lem1579977 (y : real) (z : real) : (term245 z y) = (term207 y z).
Proof. exact (@lem1483488 y (term114 z)). Qed.
Lemma lem1579978 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579979 (y : real) (z : real) : (term247 z y) = (term220 y z).
Proof. exact (MK_COMB (@lem1579978) (@lem1579977 y z)). Qed.
Lemma lem1579980 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579981 (y : real) (z : real) : (term248 z y) = (term211 y z).
Proof. exact (MK_COMB (@lem1579979 y z) (@lem1579980)). Qed.
Lemma lem1579994 (x : real) (z : real) : (term245 z x) = (term207 x z).
Proof. exact (@lem1483488 x (term114 z)). Qed.
Lemma lem1579995 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1579996 (x : real) (z : real) : (term247 z x) = (term220 x z).
Proof. exact (MK_COMB (@lem1579995) (@lem1579994 x z)). Qed.
Lemma lem1579997 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1579998 (x : real) (z : real) : (term248 z x) = (term211 x z).
Proof. exact (MK_COMB (@lem1579996 x z) (@lem1579997)). Qed.
Lemma lem1579999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580000 (x : real) (z : real) : (term258 z x) = (term240 x z).
Proof. exact (MK_COMB (@lem1579999) (@lem1579998 x z)). Qed.
Lemma lem1580001 (x : real) (y : real) (z : real) : (term474 x z y) = (term390 x y z).
Proof. exact (MK_COMB (@lem1580000 x z) (@lem1579981 y z)). Qed.
Lemma lem1580002 (x : real) (y : real) (z : real) : (term468 z x y) = (term390 x y z).
Proof. exact (TRANS (@lem1579964 x z y) (@lem1580001 x y z)). Qed.
Lemma lem1580003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580004 (x : real) (y : real) (z : real) : (term470 z x y) = (term391 x y z).
Proof. exact (MK_COMB (@lem1580003) (@lem1580002 x y z)). Qed.
Lemma lem1580005 (x : real) (y : real) (z : real) : (term469 x y z) = (term469 x y z).
Proof. exact (eq_refl (term469 x y z)). Qed.
Lemma lem1580008 (x : real) (y : real) (z : real) : (term471 x y z) = (term475 x y z).
Proof. exact (MK_COMB (@lem1580004 x y z) (@lem1580005 x y z)). Qed.
Lemma lem1580010 (z : real) (x : real) (y : real) : (term476 z x y) = (term463 z x y).
Proof. exact (eq_refl (term476 z x y)). Qed.
Lemma lem1580011 (z : real) (x : real) (y : real) : (term463 z x y) = (term476 z x y).
Proof. exact (SYM (@lem1580010 z x y)). Qed.
Lemma lem1580012 (x : real) (z : real) (y : real) : (term476 z x y) = (term477 x z y).
Proof. exact (@lem1483429 x (term478 x y z) y). Qed.
Lemma lem1580013 (x : real) (z : real) (y : real) : (term463 z x y) = (term477 x z y).
Proof. exact (TRANS (@lem1580011 z x y) (@lem1580012 x z y)). Qed.
Lemma lem1580014 (x : real) (z : real) (y : real) : (term479 x z y) = (term480 x z y).
Proof. exact (eq_refl (term479 x z y)). Qed.
Lemma lem1580015 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1580016 (x : real) (z : real) (y : real) : (term481 x z y) = (term482 x z y).
Proof. exact (MK_COMB (@lem1580015 x y) (@lem1580014 x z y)). Qed.
Lemma lem1580017 (y : real) (z : real) (x : real) : (term483 y z x) = (term484 y z x).
Proof. exact (eq_refl (term483 y z x)). Qed.
Lemma lem1580018 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1580019 (y : real) (z : real) (x : real) : (term485 y z x) = (term486 y z x).
Proof. exact (MK_COMB (@lem1580018 y x) (@lem1580017 y z x)). Qed.
Lemma lem1580020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580021 (y : real) (z : real) (x : real) : (term487 y z x) = (term488 y z x).
Proof. exact (MK_COMB (@lem1580020) (@lem1580019 y z x)). Qed.
Lemma lem1580022 (x : real) (z : real) (y : real) : (term477 x z y) = (term489 x z y).
Proof. exact (MK_COMB (@lem1580021 y z x) (@lem1580016 x z y)). Qed.
Lemma lem1580023 (z : real) (x : real) (y : real) : (term490 z x y) = (term490 z x y).
Proof. exact (eq_refl (term490 z x y)). Qed.
Lemma lem1580024 (x : real) (z : real) (y : real) : ((term463 z x y) = (term477 x z y)) = ((term463 z x y) = (term489 x z y)).
Proof. exact (MK_COMB (@lem1580023 z x y) (@lem1580022 x z y)). Qed.
Lemma lem1580025 (x : real) (z : real) (y : real) : (term463 z x y) = (term489 x z y).
Proof. exact (EQ_MP (@lem1580024 x z y) (@lem1580013 x z y)). Qed.
Lemma lem1580026 (z : real) (x : real) : (term210 z x) = (term491 z x).
Proof. exact (@lem1483527 (term207 z x) term48). Qed.
Lemma lem1580027 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580040 (x : real) (z : real) : (term207 z x) = (term245 x z).
Proof. exact (@lem1483488 (term114 x) z). Qed.
Lemma lem1580041 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1580042 (x : real) (z : real) : (term249 z x) = (term250 x z).
Proof. exact (MK_COMB (@lem1580041) (@lem1580040 x z)). Qed.
Lemma lem1580043 (x : real) (z : real) : (term213 z x) = (term251 x z).
Proof. exact (MK_COMB (@lem1580042 x z) (@lem1580027)). Qed.
Lemma lem1580044 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483519 (term245 x z) term48). Qed.
Lemma lem1580046 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1580047 : term216 = term48.
Proof. exact (@lem1580046 term36). Qed.
Lemma lem1580048 (x : real) (z : real) : (term253 x z) = (term253 x z).
Proof. exact (eq_refl (term253 x z)). Qed.
Lemma lem1580049 (x : real) (z : real) : (term252 x z) = (term254 x z).
Proof. exact (MK_COMB (@lem1580048 x z) (@lem1580047)). Qed.
Lemma lem1580050 (x : real) (z : real) : (term254 x z) = (term245 x z).
Proof. exact (@lem1483450 (term245 x z)). Qed.
Lemma lem1580051 (x : real) (z : real) : (term252 x z) = (term245 x z).
Proof. exact (TRANS (@lem1580049 x z) (@lem1580050 x z)). Qed.
Lemma lem1580052 (x : real) (z : real) : (term251 x z) = (term245 x z).
Proof. exact (TRANS (@lem1580044 x z) (@lem1580051 x z)). Qed.
Lemma lem1580053 (x : real) (z : real) : (term213 z x) = (term245 x z).
Proof. exact (TRANS (@lem1580043 x z) (@lem1580052 x z)). Qed.
Lemma lem1580054 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580055 (x : real) (z : real) : (term492 z x) = (term263 x z).
Proof. exact (MK_COMB (@lem1580054) (@lem1580053 x z)). Qed.
Lemma lem1580056 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580057 (x : real) (z : real) : (term491 z x) = (term264 x z).
Proof. exact (MK_COMB (@lem1580055 x z) (@lem1580056)). Qed.
Lemma lem1580058 (x : real) (z : real) : (term210 z x) = (term264 x z).
Proof. exact (TRANS (@lem1580026 z x) (@lem1580057 x z)). Qed.
Lemma lem1580059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580060 (x : real) (y : real) : (term240 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1580059) (@lem1578972 x y)). Qed.
Lemma lem1580061 (y : real) (x : real) (z : real) : (term390 y z x) = (term474 y x z).
Proof. exact (MK_COMB (@lem1580060 x y) (@lem1579276 x z)). Qed.
Lemma lem1580062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580063 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1580062) (@lem1578939 x)). Qed.
Lemma lem1580064 (y : real) (x : real) (z : real) : (term493 y z x) = (term494 y x z).
Proof. exact (MK_COMB (@lem1580063 x) (@lem1580061 y x z)). Qed.
Lemma lem1580065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580066 (x : real) (z : real) : (term242 z x) = (term266 x z).
Proof. exact (MK_COMB (@lem1580065) (@lem1580058 x z)). Qed.
Lemma lem1580067 (y : real) (x : real) (z : real) : (term484 y z x) = (term495 y x z).
Proof. exact (MK_COMB (@lem1580066 x z) (@lem1580064 y x z)). Qed.
Lemma lem1580068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580069 (x : real) (y : real) : (term199 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem1580068) (@lem1579069 x y)). Qed.
Lemma lem1580070 (y : real) (x : real) (z : real) : (term486 y z x) = (term496 y x z).
Proof. exact (MK_COMB (@lem1580069 x y) (@lem1580067 y x z)). Qed.
Lemma lem1580071 (z : real) (y : real) : (term210 z y) = (term491 z y).
Proof. exact (@lem1483527 (term207 z y) term48). Qed.
Lemma lem1580072 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580085 (y : real) (z : real) : (term207 z y) = (term245 y z).
Proof. exact (@lem1483488 (term114 y) z). Qed.
Lemma lem1580086 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1580087 (y : real) (z : real) : (term249 z y) = (term250 y z).
Proof. exact (MK_COMB (@lem1580086) (@lem1580085 y z)). Qed.
Lemma lem1580088 (y : real) (z : real) : (term213 z y) = (term251 y z).
Proof. exact (MK_COMB (@lem1580087 y z) (@lem1580072)). Qed.
Lemma lem1580089 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483519 (term245 y z) term48). Qed.
Lemma lem1580091 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1580092 : term216 = term48.
Proof. exact (@lem1580091 term36). Qed.
Lemma lem1580093 (y : real) (z : real) : (term253 y z) = (term253 y z).
Proof. exact (eq_refl (term253 y z)). Qed.
Lemma lem1580094 (y : real) (z : real) : (term252 y z) = (term254 y z).
Proof. exact (MK_COMB (@lem1580093 y z) (@lem1580092)). Qed.
Lemma lem1580095 (y : real) (z : real) : (term254 y z) = (term245 y z).
Proof. exact (@lem1483450 (term245 y z)). Qed.
Lemma lem1580096 (y : real) (z : real) : (term252 y z) = (term245 y z).
Proof. exact (TRANS (@lem1580094 y z) (@lem1580095 y z)). Qed.
Lemma lem1580097 (y : real) (z : real) : (term251 y z) = (term245 y z).
Proof. exact (TRANS (@lem1580089 y z) (@lem1580096 y z)). Qed.
Lemma lem1580098 (y : real) (z : real) : (term213 z y) = (term245 y z).
Proof. exact (TRANS (@lem1580088 y z) (@lem1580097 y z)). Qed.
Lemma lem1580099 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580100 (y : real) (z : real) : (term492 z y) = (term263 y z).
Proof. exact (MK_COMB (@lem1580099) (@lem1580098 y z)). Qed.
Lemma lem1580101 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580102 (y : real) (z : real) : (term491 z y) = (term264 y z).
Proof. exact (MK_COMB (@lem1580100 y z) (@lem1580101)). Qed.
Lemma lem1580103 (y : real) (z : real) : (term210 z y) = (term264 y z).
Proof. exact (TRANS (@lem1580071 z y) (@lem1580102 y z)). Qed.
Lemma lem1580104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580105 (y : real) : (term255 y) = term256.
Proof. exact (MK_COMB (@lem1580104) (@lem1578871 y)). Qed.
Lemma lem1580106 (y : real) (z : real) : (term193 z y) = (term257 y z).
Proof. exact (MK_COMB (@lem1580105 y) (@lem1579485 y z)). Qed.
Lemma lem1580107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580108 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1580107) (@lem1578828 x y)). Qed.
Lemma lem1580109 (x : real) (y : real) (z : real) : (term497 x z y) = (term498 x y z).
Proof. exact (MK_COMB (@lem1580108 x y) (@lem1580106 y z)). Qed.
Lemma lem1580110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580111 (y : real) (z : real) : (term242 z y) = (term266 y z).
Proof. exact (MK_COMB (@lem1580110) (@lem1580103 y z)). Qed.
Lemma lem1580112 (x : real) (y : real) (z : real) : (term480 x z y) = (term499 x y z).
Proof. exact (MK_COMB (@lem1580111 y z) (@lem1580109 x y z)). Qed.
Lemma lem1580113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580114 (x : real) (y : real) : (term194 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1580113) (@lem1579094 x y)). Qed.
Lemma lem1580115 (x : real) (y : real) (z : real) : (term482 x z y) = (term500 x y z).
Proof. exact (MK_COMB (@lem1580114 x y) (@lem1580112 x y z)). Qed.
Lemma lem1580116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580117 (y : real) (x : real) (z : real) : (term488 y z x) = (term501 y x z).
Proof. exact (MK_COMB (@lem1580116) (@lem1580070 y x z)). Qed.
Lemma lem1580118 (x : real) (y : real) (z : real) : (term489 x z y) = (term502 x y z).
Proof. exact (MK_COMB (@lem1580117 y x z) (@lem1580115 x y z)). Qed.
Lemma lem1580130 (x : real) (y : real) (z : real) : (term463 z x y) = (term502 x y z).
Proof. exact (TRANS (@lem1580025 x z y) (@lem1580118 x y z)). Qed.
Lemma lem1580131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580132 (x : real) (y : real) (z : real) : (term472 z x y) = (term503 x y z).
Proof. exact (MK_COMB (@lem1580131) (@lem1580130 x y z)). Qed.
Lemma lem1580133 (x : real) (y : real) (z : real) : (term473 x y z) = (term504 x y z).
Proof. exact (MK_COMB (@lem1580132 x y z) (@lem1580008 x y z)). Qed.
Lemma lem1580134 (x : real) (y : real) (z : real) : (term437 x y z) = (term504 x y z).
Proof. exact (TRANS (@lem1579961 x y z) (@lem1580133 x y z)). Qed.
Lemma lem1580135 (x : real) (y : real) (z : real) : (term79 x y z) = (term504 x y z).
Proof. exact (TRANS (@lem1579786 x y z) (@lem1580134 x y z)). Qed.
Lemma lem1580136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580137 (x : real) (y : real) (z : real) : (term85 x y z) = (term505 x y z).
Proof. exact (MK_COMB (@lem1580136) (@lem1579701 x y z)). Qed.
Lemma lem1580138 (x : real) (y : real) (z : real) : (term86 x y z) = (term506 x y z).
Proof. exact (MK_COMB (@lem1580137 x y z) (@lem1580135 x y z)). Qed.
Lemma lem1580140 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580141 (x : real) (y : real) (z : real) : (term105 y x z) = (term507 x y z).
Proof. exact (@lem1580140 x (term63 y x z) (real_min y z) term48). Qed.
Lemma lem1580154 (y : real) (x : real) (z : real) : (term508 x y z) = (term509 y x z).
Proof. exact (@lem1483488 (real_min y z) (term63 y x z)). Qed.
Lemma lem1580155 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580156 (y : real) (x : real) (z : real) : (term510 x y z) = (term511 y x z).
Proof. exact (MK_COMB (@lem1580155) (@lem1580154 y x z)). Qed.
Lemma lem1580157 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580158 (y : real) (x : real) (z : real) : (term512 x y z) = (term513 y x z).
Proof. exact (MK_COMB (@lem1580156 y x z) (@lem1580157)). Qed.
Lemma lem1580171 (y : real) (x : real) (z : real) : (term291 y z x) = (term292 y x z).
Proof. exact (@lem1483488 x (term63 y x z)). Qed.
Lemma lem1580172 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580173 (y : real) (x : real) (z : real) : (term293 y z x) = (term294 y x z).
Proof. exact (MK_COMB (@lem1580172) (@lem1580171 y x z)). Qed.
Lemma lem1580174 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580175 (y : real) (x : real) (z : real) : (term295 y z x) = (term296 y x z).
Proof. exact (MK_COMB (@lem1580173 y x z) (@lem1580174)). Qed.
Lemma lem1580176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580177 (y : real) (x : real) (z : real) : (term514 y z x) = (term515 y x z).
Proof. exact (MK_COMB (@lem1580176) (@lem1580175 y x z)). Qed.
Lemma lem1580178 (y : real) (x : real) (z : real) : (term507 x y z) = (term516 y x z).
Proof. exact (MK_COMB (@lem1580177 y x z) (@lem1580158 y x z)). Qed.
Lemma lem1580179 (y : real) (x : real) (z : real) : (term105 y x z) = (term516 y x z).
Proof. exact (TRANS (@lem1580141 x y z) (@lem1580178 y x z)). Qed.
Lemma lem1580181 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580182 (y : real) (x : real) (z : real) : (term513 y x z) = (term517 y x z).
Proof. exact (@lem1580181 y (term63 y x z) z term48). Qed.
Lemma lem1580195 (y : real) (x : real) (z : real) : (term275 y x z) = (term276 y x z).
Proof. exact (@lem1483488 z (term63 y x z)). Qed.
Lemma lem1580196 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580197 (y : real) (x : real) (z : real) : (term277 y x z) = (term278 y x z).
Proof. exact (MK_COMB (@lem1580196) (@lem1580195 y x z)). Qed.
Lemma lem1580198 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580199 (y : real) (x : real) (z : real) : (term279 y x z) = (term280 y x z).
Proof. exact (MK_COMB (@lem1580197 y x z) (@lem1580198)). Qed.
Lemma lem1580212 (y : real) (x : real) (z : real) : (term297 x z y) = (term298 y x z).
Proof. exact (@lem1483488 y (term63 y x z)). Qed.
Lemma lem1580213 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580214 (y : real) (x : real) (z : real) : (term299 x z y) = (term300 y x z).
Proof. exact (MK_COMB (@lem1580213) (@lem1580212 y x z)). Qed.
Lemma lem1580215 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580216 (y : real) (x : real) (z : real) : (term301 x z y) = (term302 y x z).
Proof. exact (MK_COMB (@lem1580214 y x z) (@lem1580215)). Qed.
Lemma lem1580217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580218 (y : real) (x : real) (z : real) : (term303 x z y) = (term304 y x z).
Proof. exact (MK_COMB (@lem1580217) (@lem1580216 y x z)). Qed.
Lemma lem1580219 (y : real) (x : real) (z : real) : (term517 y x z) = (term518 y x z).
Proof. exact (MK_COMB (@lem1580218 y x z) (@lem1580199 y x z)). Qed.
Lemma lem1580220 (y : real) (x : real) (z : real) : (term513 y x z) = (term518 y x z).
Proof. exact (TRANS (@lem1580182 y x z) (@lem1580219 y x z)). Qed.
Lemma lem1580221 (y : real) (x : real) (z : real) : (term515 y x z) = (term515 y x z).
Proof. exact (eq_refl (term515 y x z)). Qed.
Lemma lem1580222 (y : real) (x : real) (z : real) : (term516 y x z) = (term519 y x z).
Proof. exact (MK_COMB (@lem1580221 y x z) (@lem1580220 y x z)). Qed.
Lemma lem1580223 (y : real) (x : real) (z : real) : (term105 y x z) = (term519 y x z).
Proof. exact (TRANS (@lem1580179 y x z) (@lem1580222 y x z)). Qed.
Lemma lem1580224 (y : real) (x : real) (z : real) : (term520 y x z) = (term519 y x z).
Proof. exact (eq_refl (term520 y x z)). Qed.
Lemma lem1580225 (y : real) (x : real) (z : real) : (term519 y x z) = (term520 y x z).
Proof. exact (SYM (@lem1580224 y x z)). Qed.
Lemma lem1580226 (y : real) (x : real) (z : real) : (term520 y x z) = (term521 y x z).
Proof. exact (@lem1483429 y (term440 x y z) (real_min x z)). Qed.
Lemma lem1580227 (y : real) (x : real) (z : real) : (term519 y x z) = (term521 y x z).
Proof. exact (TRANS (@lem1580225 y x z) (@lem1580226 y x z)). Qed.
Lemma lem1580228 (y : real) (x : real) (z : real) : (term522 y x z) = (term523 y x z).
Proof. exact (eq_refl (term522 y x z)). Qed.
Lemma lem1580229 (y : real) (x : real) (z : real) : (term313 y x z) = (term313 y x z).
Proof. exact (eq_refl (term313 y x z)). Qed.
Lemma lem1580230 (y : real) (x : real) (z : real) : (term524 y x z) = (term525 y x z).
Proof. exact (MK_COMB (@lem1580229 y x z) (@lem1580228 y x z)). Qed.
Lemma lem1580231 (x : real) (z : real) (y : real) : (term526 x z y) = (term497 x z y).
Proof. exact (eq_refl (term526 x z y)). Qed.
Lemma lem1580232 (x : real) (z : real) (y : real) : (term318 x z y) = (term318 x z y).
Proof. exact (eq_refl (term318 x z y)). Qed.
Lemma lem1580233 (x : real) (z : real) (y : real) : (term527 x z y) = (term528 x z y).
Proof. exact (MK_COMB (@lem1580232 x z y) (@lem1580231 x z y)). Qed.
Lemma lem1580234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580235 (x : real) (z : real) (y : real) : (term529 x z y) = (term530 x z y).
Proof. exact (MK_COMB (@lem1580234) (@lem1580233 x z y)). Qed.
Lemma lem1580236 (y : real) (x : real) (z : real) : (term521 y x z) = (term531 y x z).
Proof. exact (MK_COMB (@lem1580235 x z y) (@lem1580230 y x z)). Qed.
Lemma lem1580237 (y : real) (x : real) (z : real) : (term532 y x z) = (term532 y x z).
Proof. exact (eq_refl (term532 y x z)). Qed.
Lemma lem1580238 (y : real) (x : real) (z : real) : ((term519 y x z) = (term521 y x z)) = ((term519 y x z) = (term531 y x z)).
Proof. exact (MK_COMB (@lem1580237 y x z) (@lem1580236 y x z)). Qed.
Lemma lem1580239 (y : real) (x : real) (z : real) : (term519 y x z) = (term531 y x z).
Proof. exact (EQ_MP (@lem1580238 y x z) (@lem1580227 y x z)). Qed.
Lemma lem1580240 (x : real) (z : real) (y : real) : (term325 x z y) = (term326 x z y).
Proof. exact (@lem1483527 (real_min x z) y). Qed.
Lemma lem1580246 (x : real) (z : real) (y : real) : (term327 x z y) = (term328 x z y).
Proof. exact (@lem1483519 (real_min x z) y). Qed.
Lemma lem1580251 (y : real) (x : real) (z : real) : (term328 x z y) = (term329 y x z).
Proof. exact (@lem1483488 (term114 y) (real_min x z)). Qed.
Lemma lem1580253 (y : real) (x : real) (z : real) : (term327 x z y) = (term329 y x z).
Proof. exact (TRANS (@lem1580246 x z y) (@lem1580251 y x z)). Qed.
Lemma lem1580254 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580255 (y : real) (x : real) (z : real) : (term330 x z y) = (term331 y x z).
Proof. exact (MK_COMB (@lem1580254) (@lem1580253 y x z)). Qed.
Lemma lem1580256 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580257 (y : real) (x : real) (z : real) : (term326 x z y) = (term332 y x z).
Proof. exact (MK_COMB (@lem1580255 y x z) (@lem1580256)). Qed.
Lemma lem1580258 (y : real) (x : real) (z : real) : (term325 x z y) = (term332 y x z).
Proof. exact (TRANS (@lem1580240 x z y) (@lem1580257 y x z)). Qed.
Lemma lem1580259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580260 (y : real) : (term255 y) = term256.
Proof. exact (MK_COMB (@lem1580259) (@lem1578871 y)). Qed.
Lemma lem1580261 (y : real) (z : real) : (term193 z y) = (term257 y z).
Proof. exact (MK_COMB (@lem1580260 y) (@lem1579485 y z)). Qed.
Lemma lem1580262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580263 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1580262) (@lem1578828 x y)). Qed.
Lemma lem1580264 (x : real) (y : real) (z : real) : (term497 x z y) = (term498 x y z).
Proof. exact (MK_COMB (@lem1580263 x y) (@lem1580261 y z)). Qed.
Lemma lem1580265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580266 (y : real) (x : real) (z : real) : (term318 x z y) = (term336 y x z).
Proof. exact (MK_COMB (@lem1580265) (@lem1580258 y x z)). Qed.
Lemma lem1580267 (x : real) (y : real) (z : real) : (term528 x z y) = (term533 x y z).
Proof. exact (MK_COMB (@lem1580266 y x z) (@lem1580264 x y z)). Qed.
Lemma lem1580268 (y : real) (x : real) (z : real) : (term338 y x z) = (term339 y x z).
Proof. exact (@lem1483525 y (real_min x z)). Qed.
Lemma lem1580281 (y : real) (x : real) (z : real) : (term340 y x z) = (term341 y x z).
Proof. exact (@lem1483519 y (real_min x z)). Qed.
Lemma lem1580282 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580283 (y : real) (x : real) (z : real) : (term342 y x z) = (term343 y x z).
Proof. exact (MK_COMB (@lem1580282) (@lem1580281 y x z)). Qed.
Lemma lem1580284 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580285 (y : real) (x : real) (z : real) : (term339 y x z) = (term344 y x z).
Proof. exact (MK_COMB (@lem1580283 y x z) (@lem1580284)). Qed.
Lemma lem1580286 (y : real) (x : real) (z : real) : (term338 y x z) = (term344 y x z).
Proof. exact (TRANS (@lem1580268 y x z) (@lem1580285 y x z)). Qed.
Lemma lem1580287 (x : real) (z : real) : (term179 x z) = (term351 x z).
Proof. exact (@lem1483525 (term175 x z) term48). Qed.
Lemma lem1580305 (x : real) (z : real) : (term352 x z) = (term353 x z).
Proof. exact (@lem1483519 (term175 x z) term48). Qed.
Lemma lem1580307 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1580308 : term216 = term48.
Proof. exact (@lem1580307 term36). Qed.
Lemma lem1580309 (x : real) (z : real) : (term354 x z) = (term354 x z).
Proof. exact (eq_refl (term354 x z)). Qed.
Lemma lem1580310 (x : real) (z : real) : (term353 x z) = (term355 x z).
Proof. exact (MK_COMB (@lem1580309 x z) (@lem1580308)). Qed.
Lemma lem1580311 (x : real) (z : real) : (term355 x z) = (term175 x z).
Proof. exact (@lem1483450 (term175 x z)). Qed.
Lemma lem1580312 (x : real) (z : real) : (term353 x z) = (term175 x z).
Proof. exact (TRANS (@lem1580310 x z) (@lem1580311 x z)). Qed.
Lemma lem1580314 (x : real) (z : real) : (term352 x z) = (term175 x z).
Proof. exact (TRANS (@lem1580305 x z) (@lem1580312 x z)). Qed.
Lemma lem1580315 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580316 (x : real) (z : real) : (term356 x z) = (term177 x z).
Proof. exact (MK_COMB (@lem1580315) (@lem1580314 x z)). Qed.
Lemma lem1580317 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580318 (x : real) (z : real) : (term351 x z) = (term179 x z).
Proof. exact (MK_COMB (@lem1580316 x z) (@lem1580317)). Qed.
Lemma lem1580319 (x : real) (z : real) : (term179 x z) = (term179 x z).
Proof. exact (TRANS (@lem1580287 x z) (@lem1580318 x z)). Qed.
Lemma lem1580320 (y : real) (x : real) (z : real) : (term344 y x z) = (term345 y x z).
Proof. exact (@lem1483525 (term341 y x z) term48). Qed.
Lemma lem1580338 (y : real) (x : real) (z : real) : (term346 y x z) = (term347 y x z).
Proof. exact (@lem1483519 (term341 y x z) term48). Qed.
Lemma lem1580340 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1580341 : term216 = term48.
Proof. exact (@lem1580340 term36). Qed.
Lemma lem1580342 (y : real) (x : real) (z : real) : (term348 y x z) = (term348 y x z).
Proof. exact (eq_refl (term348 y x z)). Qed.
Lemma lem1580343 (y : real) (x : real) (z : real) : (term347 y x z) = (term349 y x z).
Proof. exact (MK_COMB (@lem1580342 y x z) (@lem1580341)). Qed.
Lemma lem1580344 (y : real) (x : real) (z : real) : (term349 y x z) = (term341 y x z).
Proof. exact (@lem1483450 (term341 y x z)). Qed.
Lemma lem1580345 (y : real) (x : real) (z : real) : (term347 y x z) = (term341 y x z).
Proof. exact (TRANS (@lem1580343 y x z) (@lem1580344 y x z)). Qed.
Lemma lem1580347 (y : real) (x : real) (z : real) : (term346 y x z) = (term341 y x z).
Proof. exact (TRANS (@lem1580338 y x z) (@lem1580345 y x z)). Qed.
Lemma lem1580348 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580349 (y : real) (x : real) (z : real) : (term350 y x z) = (term343 y x z).
Proof. exact (MK_COMB (@lem1580348) (@lem1580347 y x z)). Qed.
Lemma lem1580350 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580351 (y : real) (x : real) (z : real) : (term345 y x z) = (term344 y x z).
Proof. exact (MK_COMB (@lem1580349 y x z) (@lem1580350)). Qed.
Lemma lem1580352 (y : real) (x : real) (z : real) : (term344 y x z) = (term344 y x z).
Proof. exact (TRANS (@lem1580320 y x z) (@lem1580351 y x z)). Qed.
Lemma lem1580353 (x : real) (z : real) : (term185 x z) = (term359 x z).
Proof. exact (@lem1483525 (term181 x z) term48). Qed.
Lemma lem1580371 (x : real) (z : real) : (term360 x z) = (term361 x z).
Proof. exact (@lem1483519 (term181 x z) term48). Qed.
Lemma lem1580373 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1580374 : term216 = term48.
Proof. exact (@lem1580373 term36). Qed.
Lemma lem1580375 (x : real) (z : real) : (term362 x z) = (term362 x z).
Proof. exact (eq_refl (term362 x z)). Qed.
Lemma lem1580376 (x : real) (z : real) : (term361 x z) = (term363 x z).
Proof. exact (MK_COMB (@lem1580375 x z) (@lem1580374)). Qed.
Lemma lem1580377 (x : real) (z : real) : (term363 x z) = (term181 x z).
Proof. exact (@lem1483450 (term181 x z)). Qed.
Lemma lem1580378 (x : real) (z : real) : (term361 x z) = (term181 x z).
Proof. exact (TRANS (@lem1580376 x z) (@lem1580377 x z)). Qed.
Lemma lem1580380 (x : real) (z : real) : (term360 x z) = (term181 x z).
Proof. exact (TRANS (@lem1580371 x z) (@lem1580378 x z)). Qed.
Lemma lem1580381 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580382 (x : real) (z : real) : (term364 x z) = (term183 x z).
Proof. exact (MK_COMB (@lem1580381) (@lem1580380 x z)). Qed.
Lemma lem1580383 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580384 (x : real) (z : real) : (term359 x z) = (term185 x z).
Proof. exact (MK_COMB (@lem1580382 x z) (@lem1580383)). Qed.
Lemma lem1580385 (x : real) (z : real) : (term185 x z) = (term185 x z).
Proof. exact (TRANS (@lem1580353 x z) (@lem1580384 x z)). Qed.
Lemma lem1580386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580387 (y : real) (x : real) (z : real) : (term357 y x z) = (term357 y x z).
Proof. exact (MK_COMB (@lem1580386) (@lem1580352 y x z)). Qed.
Lemma lem1580388 (y : real) (x : real) (z : real) : (term534 y x z) = (term534 y x z).
Proof. exact (MK_COMB (@lem1580387 y x z) (@lem1580385 x z)). Qed.
Lemma lem1580389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580390 (x : real) (z : real) : (term461 x z) = (term461 x z).
Proof. exact (MK_COMB (@lem1580389) (@lem1580319 x z)). Qed.
Lemma lem1580391 (y : real) (x : real) (z : real) : (term523 y x z) = (term523 y x z).
Proof. exact (MK_COMB (@lem1580390 x z) (@lem1580388 y x z)). Qed.
Lemma lem1580392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580393 (y : real) (x : real) (z : real) : (term313 y x z) = (term357 y x z).
Proof. exact (MK_COMB (@lem1580392) (@lem1580286 y x z)). Qed.
Lemma lem1580394 (y : real) (x : real) (z : real) : (term525 y x z) = (term535 y x z).
Proof. exact (MK_COMB (@lem1580393 y x z) (@lem1580391 y x z)). Qed.
Lemma lem1580395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580396 (x : real) (y : real) (z : real) : (term530 x z y) = (term536 x y z).
Proof. exact (MK_COMB (@lem1580395) (@lem1580267 x y z)). Qed.
Lemma lem1580397 (y : real) (x : real) (z : real) : (term531 y x z) = (term537 y x z).
Proof. exact (MK_COMB (@lem1580396 x y z) (@lem1580394 y x z)). Qed.
Lemma lem1580398 (y : real) (x : real) (z : real) : (term519 y x z) = (term537 y x z).
Proof. exact (TRANS (@lem1580239 y x z) (@lem1580397 y x z)). Qed.
Lemma lem1580400 (y : real) (x : real) (z : real) : (term538 y x z) = (term535 y x z).
Proof. exact (eq_refl (term538 y x z)). Qed.
Lemma lem1580401 (y : real) (x : real) (z : real) : (term535 y x z) = (term538 y x z).
Proof. exact (SYM (@lem1580400 y x z)). Qed.
Lemma lem1580402 (x : real) (y : real) (z : real) : (term538 y x z) = (term539 x y z).
Proof. exact (@lem1483429 x (term540 x y z) z). Qed.
Lemma lem1580403 (x : real) (y : real) (z : real) : (term535 y x z) = (term539 x y z).
Proof. exact (TRANS (@lem1580401 y x z) (@lem1580402 x y z)). Qed.
Lemma lem1580404 (x : real) (y : real) (z : real) : (term541 x y z) = (term542 x y z).
Proof. exact (eq_refl (term541 x y z)). Qed.
Lemma lem1580405 (x : real) (z : real) : (term194 x z) = (term194 x z).
Proof. exact (eq_refl (term194 x z)). Qed.
Lemma lem1580406 (x : real) (y : real) (z : real) : (term543 x y z) = (term544 x y z).
Proof. exact (MK_COMB (@lem1580405 x z) (@lem1580404 x y z)). Qed.
Lemma lem1580407 (y : real) (z : real) (x : real) : (term545 y z x) = (term546 y z x).
Proof. exact (eq_refl (term545 y z x)). Qed.
Lemma lem1580408 (z : real) (x : real) : (term199 z x) = (term199 z x).
Proof. exact (eq_refl (term199 z x)). Qed.
Lemma lem1580409 (y : real) (z : real) (x : real) : (term547 y z x) = (term548 y z x).
Proof. exact (MK_COMB (@lem1580408 z x) (@lem1580407 y z x)). Qed.
Lemma lem1580410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580411 (y : real) (z : real) (x : real) : (term549 y z x) = (term550 y z x).
Proof. exact (MK_COMB (@lem1580410) (@lem1580409 y z x)). Qed.
Lemma lem1580412 (x : real) (y : real) (z : real) : (term539 x y z) = (term551 x y z).
Proof. exact (MK_COMB (@lem1580411 y z x) (@lem1580406 x y z)). Qed.
Lemma lem1580413 (y : real) (x : real) (z : real) : (term552 y x z) = (term552 y x z).
Proof. exact (eq_refl (term552 y x z)). Qed.
Lemma lem1580414 (x : real) (y : real) (z : real) : ((term535 y x z) = (term539 x y z)) = ((term535 y x z) = (term551 x y z)).
Proof. exact (MK_COMB (@lem1580413 y x z) (@lem1580412 x y z)). Qed.
Lemma lem1580415 (x : real) (y : real) (z : real) : (term535 y x z) = (term551 x y z).
Proof. exact (EQ_MP (@lem1580414 x y z) (@lem1580403 x y z)). Qed.
Lemma lem1580416 (z : real) (x : real) : (real_ge z x) = (term206 z x).
Proof. exact (@lem1483527 z x). Qed.
Lemma lem1580422 (z : real) (x : real) : (real_sub z x) = (term207 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1580427 (x : real) (z : real) : (term207 z x) = (term245 x z).
Proof. exact (@lem1483488 (term114 x) z). Qed.
Lemma lem1580429 (x : real) (z : real) : (real_sub z x) = (term245 x z).
Proof. exact (TRANS (@lem1580422 z x) (@lem1580427 x z)). Qed.
Lemma lem1580430 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580431 (x : real) (z : real) : (term208 z x) = (term263 x z).
Proof. exact (MK_COMB (@lem1580430) (@lem1580429 x z)). Qed.
Lemma lem1580432 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580433 (x : real) (z : real) : (term206 z x) = (term264 x z).
Proof. exact (MK_COMB (@lem1580431 x z) (@lem1580432)). Qed.
Lemma lem1580434 (x : real) (z : real) : (real_ge z x) = (term264 x z).
Proof. exact (TRANS (@lem1580416 z x) (@lem1580433 x z)). Qed.
Lemma lem1580435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580436 (x : real) (y : real) : (term240 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1580435) (@lem1578972 x y)). Qed.
Lemma lem1580437 (y : real) (x : real) (z : real) : (term390 y z x) = (term474 y x z).
Proof. exact (MK_COMB (@lem1580436 x y) (@lem1579276 x z)). Qed.
Lemma lem1580438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580439 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1580438) (@lem1578939 x)). Qed.
Lemma lem1580440 (y : real) (x : real) (z : real) : (term493 y z x) = (term494 y x z).
Proof. exact (MK_COMB (@lem1580439 x) (@lem1580437 y x z)). Qed.
Lemma lem1580441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580442 (x : real) (y : real) : (term240 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1580441) (@lem1578972 x y)). Qed.
Lemma lem1580443 (y : real) (x : real) (z : real) : (term546 y z x) = (term553 y x z).
Proof. exact (MK_COMB (@lem1580442 x y) (@lem1580440 y x z)). Qed.
Lemma lem1580444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580445 (x : real) (z : real) : (term199 z x) = (term266 x z).
Proof. exact (MK_COMB (@lem1580444) (@lem1580434 x z)). Qed.
Lemma lem1580446 (y : real) (x : real) (z : real) : (term548 y z x) = (term554 y x z).
Proof. exact (MK_COMB (@lem1580445 x z) (@lem1580443 y x z)). Qed.
Lemma lem1580447 (x : real) (z : real) : (real_gt x z) = (term244 x z).
Proof. exact (@lem1483525 x z). Qed.
Lemma lem1580460 (x : real) (z : real) : (real_sub x z) = (term207 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1580461 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580462 (x : real) (z : real) : (term246 x z) = (term220 x z).
Proof. exact (MK_COMB (@lem1580461) (@lem1580460 x z)). Qed.
Lemma lem1580463 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580464 (x : real) (z : real) : (term244 x z) = (term211 x z).
Proof. exact (MK_COMB (@lem1580462 x z) (@lem1580463)). Qed.
Lemma lem1580465 (x : real) (z : real) : (real_gt x z) = (term211 x z).
Proof. exact (TRANS (@lem1580447 x z) (@lem1580464 x z)). Qed.
Lemma lem1580466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580467 (y : real) (z : real) : (term240 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1580466) (@lem1579579 y z)). Qed.
Lemma lem1580468 (y : real) (z : real) : (term198 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1580467 y z) (@lem1579625 z)). Qed.
Lemma lem1580469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580470 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1580469) (@lem1579546 x z)). Qed.
Lemma lem1580471 (x : real) (y : real) (z : real) : (term442 x y z) = (term469 x y z).
Proof. exact (MK_COMB (@lem1580470 x z) (@lem1580468 y z)). Qed.
Lemma lem1580472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580473 (y : real) (z : real) : (term240 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1580472) (@lem1579579 y z)). Qed.
Lemma lem1580474 (x : real) (y : real) (z : real) : (term542 x y z) = (term555 x y z).
Proof. exact (MK_COMB (@lem1580473 y z) (@lem1580471 x y z)). Qed.
Lemma lem1580475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580476 (x : real) (z : real) : (term194 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1580475) (@lem1580465 x z)). Qed.
Lemma lem1580477 (x : real) (y : real) (z : real) : (term544 x y z) = (term556 x y z).
Proof. exact (MK_COMB (@lem1580476 x z) (@lem1580474 x y z)). Qed.
Lemma lem1580478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580479 (y : real) (x : real) (z : real) : (term550 y z x) = (term557 y x z).
Proof. exact (MK_COMB (@lem1580478) (@lem1580446 y x z)). Qed.
Lemma lem1580480 (x : real) (y : real) (z : real) : (term551 x y z) = (term558 x y z).
Proof. exact (MK_COMB (@lem1580479 y x z) (@lem1580477 x y z)). Qed.
Lemma lem1580492 (x : real) (y : real) (z : real) : (term535 y x z) = (term558 x y z).
Proof. exact (TRANS (@lem1580415 x y z) (@lem1580480 x y z)). Qed.
Lemma lem1580494 (x : real) (a : real) (y : real) (r : real) : (term398 a x y r) = (term399 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580495 (x : real) (y : real) (z : real) : (term332 y x z) = (term400 x y z).
Proof. exact (@lem1580494 x (term114 y) z term48). Qed.
Lemma lem1580512 (y : real) (z : real) : (term264 y z) = (term264 y z).
Proof. exact (eq_refl (term264 y z)). Qed.
Lemma lem1580525 (x : real) (y : real) : (term245 y x) = (term207 x y).
Proof. exact (@lem1483488 x (term114 y)). Qed.
Lemma lem1580526 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580527 (x : real) (y : real) : (term263 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem1580526) (@lem1580525 x y)). Qed.
Lemma lem1580528 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580529 (x : real) (y : real) : (term264 y x) = (term210 x y).
Proof. exact (MK_COMB (@lem1580527 x y) (@lem1580528)). Qed.
Lemma lem1580530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580531 (x : real) (y : real) : (term266 y x) = (term242 x y).
Proof. exact (MK_COMB (@lem1580530) (@lem1580529 x y)). Qed.
Lemma lem1580532 (x : real) (y : real) (z : real) : (term400 x y z) = (term559 x y z).
Proof. exact (MK_COMB (@lem1580531 x y) (@lem1580512 y z)). Qed.
Lemma lem1580533 (x : real) (y : real) (z : real) : (term332 y x z) = (term559 x y z).
Proof. exact (TRANS (@lem1580495 x y z) (@lem1580532 x y z)). Qed.
Lemma lem1580534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580535 (x : real) (y : real) (z : real) : (term336 y x z) = (term560 x y z).
Proof. exact (MK_COMB (@lem1580534) (@lem1580533 x y z)). Qed.
Lemma lem1580536 (x : real) (y : real) (z : real) : (term498 x y z) = (term498 x y z).
Proof. exact (eq_refl (term498 x y z)). Qed.
Lemma lem1580539 (x : real) (y : real) (z : real) : (term533 x y z) = (term561 x y z).
Proof. exact (MK_COMB (@lem1580535 x y z) (@lem1580536 x y z)). Qed.
Lemma lem1580540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580541 (x : real) (y : real) (z : real) : (term536 x y z) = (term562 x y z).
Proof. exact (MK_COMB (@lem1580540) (@lem1580539 x y z)). Qed.
Lemma lem1580542 (x : real) (y : real) (z : real) : (term537 y x z) = (term563 x y z).
Proof. exact (MK_COMB (@lem1580541 x y z) (@lem1580492 x y z)). Qed.
Lemma lem1580543 (x : real) (y : real) (z : real) : (term519 y x z) = (term563 x y z).
Proof. exact (TRANS (@lem1580398 y x z) (@lem1580542 x y z)). Qed.
Lemma lem1580544 (x : real) (y : real) (z : real) : (term105 y x z) = (term563 x y z).
Proof. exact (TRANS (@lem1580223 y x z) (@lem1580543 x y z)). Qed.
Lemma lem1580546 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580547 (y : real) (x : real) (z : real) : (term101 y x z) = (term507 y x z).
Proof. exact (@lem1580546 y (term63 x y z) (real_min x z) term48). Qed.
Lemma lem1580560 (x : real) (y : real) (z : real) : (term508 y x z) = (term509 x y z).
Proof. exact (@lem1483488 (real_min x z) (term63 x y z)). Qed.
Lemma lem1580561 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580562 (x : real) (y : real) (z : real) : (term510 y x z) = (term511 x y z).
Proof. exact (MK_COMB (@lem1580561) (@lem1580560 x y z)). Qed.
Lemma lem1580563 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580564 (x : real) (y : real) (z : real) : (term512 y x z) = (term513 x y z).
Proof. exact (MK_COMB (@lem1580562 x y z) (@lem1580563)). Qed.
Lemma lem1580577 (x : real) (y : real) (z : real) : (term291 x z y) = (term292 x y z).
Proof. exact (@lem1483488 y (term63 x y z)). Qed.
Lemma lem1580578 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580579 (x : real) (y : real) (z : real) : (term293 x z y) = (term294 x y z).
Proof. exact (MK_COMB (@lem1580578) (@lem1580577 x y z)). Qed.
Lemma lem1580580 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580581 (x : real) (y : real) (z : real) : (term295 x z y) = (term296 x y z).
Proof. exact (MK_COMB (@lem1580579 x y z) (@lem1580580)). Qed.
Lemma lem1580582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580583 (x : real) (y : real) (z : real) : (term514 x z y) = (term515 x y z).
Proof. exact (MK_COMB (@lem1580582) (@lem1580581 x y z)). Qed.
Lemma lem1580584 (x : real) (y : real) (z : real) : (term507 y x z) = (term516 x y z).
Proof. exact (MK_COMB (@lem1580583 x y z) (@lem1580564 x y z)). Qed.
Lemma lem1580585 (x : real) (y : real) (z : real) : (term101 y x z) = (term516 x y z).
Proof. exact (TRANS (@lem1580547 y x z) (@lem1580584 x y z)). Qed.
Lemma lem1580587 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580588 (x : real) (y : real) (z : real) : (term513 x y z) = (term517 x y z).
Proof. exact (@lem1580587 x (term63 x y z) z term48). Qed.
Lemma lem1580601 (x : real) (y : real) (z : real) : (term275 x y z) = (term276 x y z).
Proof. exact (@lem1483488 z (term63 x y z)). Qed.
Lemma lem1580602 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580603 (x : real) (y : real) (z : real) : (term277 x y z) = (term278 x y z).
Proof. exact (MK_COMB (@lem1580602) (@lem1580601 x y z)). Qed.
Lemma lem1580604 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580605 (x : real) (y : real) (z : real) : (term279 x y z) = (term280 x y z).
Proof. exact (MK_COMB (@lem1580603 x y z) (@lem1580604)). Qed.
Lemma lem1580618 (x : real) (y : real) (z : real) : (term297 y z x) = (term298 x y z).
Proof. exact (@lem1483488 x (term63 x y z)). Qed.
Lemma lem1580619 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580620 (x : real) (y : real) (z : real) : (term299 y z x) = (term300 x y z).
Proof. exact (MK_COMB (@lem1580619) (@lem1580618 x y z)). Qed.
Lemma lem1580621 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580622 (x : real) (y : real) (z : real) : (term301 y z x) = (term302 x y z).
Proof. exact (MK_COMB (@lem1580620 x y z) (@lem1580621)). Qed.
Lemma lem1580623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580624 (x : real) (y : real) (z : real) : (term303 y z x) = (term304 x y z).
Proof. exact (MK_COMB (@lem1580623) (@lem1580622 x y z)). Qed.
Lemma lem1580625 (x : real) (y : real) (z : real) : (term517 x y z) = (term518 x y z).
Proof. exact (MK_COMB (@lem1580624 x y z) (@lem1580605 x y z)). Qed.
Lemma lem1580626 (x : real) (y : real) (z : real) : (term513 x y z) = (term518 x y z).
Proof. exact (TRANS (@lem1580588 x y z) (@lem1580625 x y z)). Qed.
Lemma lem1580627 (x : real) (y : real) (z : real) : (term515 x y z) = (term515 x y z).
Proof. exact (eq_refl (term515 x y z)). Qed.
Lemma lem1580628 (x : real) (y : real) (z : real) : (term516 x y z) = (term519 x y z).
Proof. exact (MK_COMB (@lem1580627 x y z) (@lem1580626 x y z)). Qed.
Lemma lem1580629 (x : real) (y : real) (z : real) : (term101 y x z) = (term519 x y z).
Proof. exact (TRANS (@lem1580585 x y z) (@lem1580628 x y z)). Qed.
Lemma lem1580630 (x : real) (y : real) (z : real) : (term520 x y z) = (term519 x y z).
Proof. exact (eq_refl (term520 x y z)). Qed.
Lemma lem1580631 (x : real) (y : real) (z : real) : (term519 x y z) = (term520 x y z).
Proof. exact (SYM (@lem1580630 x y z)). Qed.
Lemma lem1580632 (x : real) (y : real) (z : real) : (term520 x y z) = (term521 x y z).
Proof. exact (@lem1483429 x (term440 y x z) (real_min y z)). Qed.
Lemma lem1580633 (x : real) (y : real) (z : real) : (term519 x y z) = (term521 x y z).
Proof. exact (TRANS (@lem1580631 x y z) (@lem1580632 x y z)). Qed.
Lemma lem1580634 (x : real) (y : real) (z : real) : (term522 x y z) = (term523 x y z).
Proof. exact (eq_refl (term522 x y z)). Qed.
Lemma lem1580635 (x : real) (y : real) (z : real) : (term313 x y z) = (term313 x y z).
Proof. exact (eq_refl (term313 x y z)). Qed.
Lemma lem1580636 (x : real) (y : real) (z : real) : (term524 x y z) = (term525 x y z).
Proof. exact (MK_COMB (@lem1580635 x y z) (@lem1580634 x y z)). Qed.
Lemma lem1580637 (y : real) (z : real) (x : real) : (term526 y z x) = (term497 y z x).
Proof. exact (eq_refl (term526 y z x)). Qed.
Lemma lem1580638 (y : real) (z : real) (x : real) : (term318 y z x) = (term318 y z x).
Proof. exact (eq_refl (term318 y z x)). Qed.
Lemma lem1580639 (y : real) (z : real) (x : real) : (term527 y z x) = (term528 y z x).
Proof. exact (MK_COMB (@lem1580638 y z x) (@lem1580637 y z x)). Qed.
Lemma lem1580640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580641 (y : real) (z : real) (x : real) : (term529 y z x) = (term530 y z x).
Proof. exact (MK_COMB (@lem1580640) (@lem1580639 y z x)). Qed.
Lemma lem1580642 (x : real) (y : real) (z : real) : (term521 x y z) = (term531 x y z).
Proof. exact (MK_COMB (@lem1580641 y z x) (@lem1580636 x y z)). Qed.
Lemma lem1580643 (x : real) (y : real) (z : real) : (term532 x y z) = (term532 x y z).
Proof. exact (eq_refl (term532 x y z)). Qed.
Lemma lem1580644 (x : real) (y : real) (z : real) : ((term519 x y z) = (term521 x y z)) = ((term519 x y z) = (term531 x y z)).
Proof. exact (MK_COMB (@lem1580643 x y z) (@lem1580642 x y z)). Qed.
Lemma lem1580645 (x : real) (y : real) (z : real) : (term519 x y z) = (term531 x y z).
Proof. exact (EQ_MP (@lem1580644 x y z) (@lem1580633 x y z)). Qed.
Lemma lem1580646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580647 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1580646) (@lem1578939 x)). Qed.
Lemma lem1580648 (x : real) (z : real) : (term193 z x) = (term257 x z).
Proof. exact (MK_COMB (@lem1580647 x) (@lem1579276 x z)). Qed.
Lemma lem1580649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580650 (x : real) (y : real) : (term240 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1580649) (@lem1578972 x y)). Qed.
Lemma lem1580651 (y : real) (x : real) (z : real) : (term497 y z x) = (term564 y x z).
Proof. exact (MK_COMB (@lem1580650 x y) (@lem1580648 x z)). Qed.
Lemma lem1580652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580653 (x : real) (y : real) (z : real) : (term318 y z x) = (term336 x y z).
Proof. exact (MK_COMB (@lem1580652) (@lem1579240 x y z)). Qed.
Lemma lem1580654 (y : real) (x : real) (z : real) : (term528 y z x) = (term565 y x z).
Proof. exact (MK_COMB (@lem1580653 x y z) (@lem1580651 y x z)). Qed.
Lemma lem1580655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580656 (x : real) (y : real) (z : real) : (term357 x y z) = (term357 x y z).
Proof. exact (MK_COMB (@lem1580655) (@lem1579334 x y z)). Qed.
Lemma lem1580657 (x : real) (y : real) (z : real) : (term534 x y z) = (term534 x y z).
Proof. exact (MK_COMB (@lem1580656 x y z) (@lem1579403 y z)). Qed.
Lemma lem1580658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580659 (y : real) (z : real) : (term461 y z) = (term461 y z).
Proof. exact (MK_COMB (@lem1580658) (@lem1579367 y z)). Qed.
Lemma lem1580660 (x : real) (y : real) (z : real) : (term523 x y z) = (term523 x y z).
Proof. exact (MK_COMB (@lem1580659 y z) (@lem1580657 x y z)). Qed.
Lemma lem1580661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580662 (x : real) (y : real) (z : real) : (term313 x y z) = (term357 x y z).
Proof. exact (MK_COMB (@lem1580661) (@lem1579301 x y z)). Qed.
Lemma lem1580663 (x : real) (y : real) (z : real) : (term525 x y z) = (term535 x y z).
Proof. exact (MK_COMB (@lem1580662 x y z) (@lem1580660 x y z)). Qed.
Lemma lem1580664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580665 (y : real) (x : real) (z : real) : (term530 y z x) = (term566 y x z).
Proof. exact (MK_COMB (@lem1580664) (@lem1580654 y x z)). Qed.
Lemma lem1580666 (x : real) (y : real) (z : real) : (term531 x y z) = (term567 x y z).
Proof. exact (MK_COMB (@lem1580665 y x z) (@lem1580663 x y z)). Qed.
Lemma lem1580667 (x : real) (y : real) (z : real) : (term519 x y z) = (term567 x y z).
Proof. exact (TRANS (@lem1580645 x y z) (@lem1580666 x y z)). Qed.
Lemma lem1580669 (x : real) (y : real) (z : real) : (term538 x y z) = (term535 x y z).
Proof. exact (eq_refl (term538 x y z)). Qed.
Lemma lem1580670 (x : real) (y : real) (z : real) : (term535 x y z) = (term538 x y z).
Proof. exact (SYM (@lem1580669 x y z)). Qed.
Lemma lem1580671 (y : real) (x : real) (z : real) : (term538 x y z) = (term539 y x z).
Proof. exact (@lem1483429 y (term540 y x z) z). Qed.
Lemma lem1580672 (y : real) (x : real) (z : real) : (term535 x y z) = (term539 y x z).
Proof. exact (TRANS (@lem1580670 x y z) (@lem1580671 y x z)). Qed.
Lemma lem1580673 (y : real) (x : real) (z : real) : (term541 y x z) = (term542 y x z).
Proof. exact (eq_refl (term541 y x z)). Qed.
Lemma lem1580674 (y : real) (z : real) : (term194 y z) = (term194 y z).
Proof. exact (eq_refl (term194 y z)). Qed.
Lemma lem1580675 (y : real) (x : real) (z : real) : (term543 y x z) = (term544 y x z).
Proof. exact (MK_COMB (@lem1580674 y z) (@lem1580673 y x z)). Qed.
Lemma lem1580676 (x : real) (z : real) (y : real) : (term545 x z y) = (term546 x z y).
Proof. exact (eq_refl (term545 x z y)). Qed.
Lemma lem1580677 (z : real) (y : real) : (term199 z y) = (term199 z y).
Proof. exact (eq_refl (term199 z y)). Qed.
Lemma lem1580678 (x : real) (z : real) (y : real) : (term547 x z y) = (term548 x z y).
Proof. exact (MK_COMB (@lem1580677 z y) (@lem1580676 x z y)). Qed.
Lemma lem1580679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580680 (x : real) (z : real) (y : real) : (term549 x z y) = (term550 x z y).
Proof. exact (MK_COMB (@lem1580679) (@lem1580678 x z y)). Qed.
Lemma lem1580681 (y : real) (x : real) (z : real) : (term539 y x z) = (term551 y x z).
Proof. exact (MK_COMB (@lem1580680 x z y) (@lem1580675 y x z)). Qed.
Lemma lem1580682 (x : real) (y : real) (z : real) : (term552 x y z) = (term552 x y z).
Proof. exact (eq_refl (term552 x y z)). Qed.
Lemma lem1580683 (y : real) (x : real) (z : real) : ((term535 x y z) = (term539 y x z)) = ((term535 x y z) = (term551 y x z)).
Proof. exact (MK_COMB (@lem1580682 x y z) (@lem1580681 y x z)). Qed.
Lemma lem1580684 (y : real) (x : real) (z : real) : (term535 x y z) = (term551 y x z).
Proof. exact (EQ_MP (@lem1580683 y x z) (@lem1580672 y x z)). Qed.
Lemma lem1580685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580686 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1580685) (@lem1578828 x y)). Qed.
Lemma lem1580687 (x : real) (y : real) (z : real) : (term390 x z y) = (term568 x y z).
Proof. exact (MK_COMB (@lem1580686 x y) (@lem1579485 y z)). Qed.
Lemma lem1580688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580689 (y : real) : (term255 y) = term256.
Proof. exact (MK_COMB (@lem1580688) (@lem1578871 y)). Qed.
Lemma lem1580690 (x : real) (y : real) (z : real) : (term493 x z y) = (term569 x y z).
Proof. exact (MK_COMB (@lem1580689 y) (@lem1580687 x y z)). Qed.
Lemma lem1580691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580692 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1580691) (@lem1578828 x y)). Qed.
Lemma lem1580693 (x : real) (y : real) (z : real) : (term546 x z y) = (term570 x y z).
Proof. exact (MK_COMB (@lem1580692 x y) (@lem1580690 x y z)). Qed.
Lemma lem1580694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580695 (y : real) (z : real) : (term199 z y) = (term266 y z).
Proof. exact (MK_COMB (@lem1580694) (@lem1579449 y z)). Qed.
Lemma lem1580696 (x : real) (y : real) (z : real) : (term548 x z y) = (term571 x y z).
Proof. exact (MK_COMB (@lem1580695 y z) (@lem1580693 x y z)). Qed.
Lemma lem1580697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580698 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1580697) (@lem1579546 x z)). Qed.
Lemma lem1580699 (x : real) (z : real) : (term198 x z) = (term241 x z).
Proof. exact (MK_COMB (@lem1580698 x z) (@lem1579625 z)). Qed.
Lemma lem1580700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580701 (y : real) (z : real) : (term240 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1580700) (@lem1579579 y z)). Qed.
Lemma lem1580702 (y : real) (x : real) (z : real) : (term442 y x z) = (term469 y x z).
Proof. exact (MK_COMB (@lem1580701 y z) (@lem1580699 x z)). Qed.
Lemma lem1580703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580704 (x : real) (z : real) : (term240 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1580703) (@lem1579546 x z)). Qed.
Lemma lem1580705 (y : real) (x : real) (z : real) : (term542 y x z) = (term555 y x z).
Proof. exact (MK_COMB (@lem1580704 x z) (@lem1580702 y x z)). Qed.
Lemma lem1580706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580707 (y : real) (z : real) : (term194 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1580706) (@lem1579513 y z)). Qed.
Lemma lem1580708 (y : real) (x : real) (z : real) : (term544 y x z) = (term556 y x z).
Proof. exact (MK_COMB (@lem1580707 y z) (@lem1580705 y x z)). Qed.
Lemma lem1580709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580710 (x : real) (y : real) (z : real) : (term550 x z y) = (term572 x y z).
Proof. exact (MK_COMB (@lem1580709) (@lem1580696 x y z)). Qed.
Lemma lem1580711 (y : real) (x : real) (z : real) : (term551 y x z) = (term573 y x z).
Proof. exact (MK_COMB (@lem1580710 x y z) (@lem1580708 y x z)). Qed.
Lemma lem1580723 (y : real) (x : real) (z : real) : (term535 x y z) = (term573 y x z).
Proof. exact (TRANS (@lem1580684 y x z) (@lem1580711 y x z)). Qed.
Lemma lem1580725 (x : real) (a : real) (y : real) (r : real) : (term398 a x y r) = (term399 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580764 (y : real) (x : real) (z : real) : (term332 x y z) = (term400 y x z).
Proof. exact (@lem1580725 y (term114 x) z term48). Qed.
Lemma lem1580765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580766 (y : real) (x : real) (z : real) : (term336 x y z) = (term401 y x z).
Proof. exact (MK_COMB (@lem1580765) (@lem1580764 y x z)). Qed.
Lemma lem1580767 (y : real) (x : real) (z : real) : (term564 y x z) = (term564 y x z).
Proof. exact (eq_refl (term564 y x z)). Qed.
Lemma lem1580770 (y : real) (x : real) (z : real) : (term565 y x z) = (term574 y x z).
Proof. exact (MK_COMB (@lem1580766 y x z) (@lem1580767 y x z)). Qed.
Lemma lem1580771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580772 (y : real) (x : real) (z : real) : (term566 y x z) = (term575 y x z).
Proof. exact (MK_COMB (@lem1580771) (@lem1580770 y x z)). Qed.
Lemma lem1580773 (y : real) (x : real) (z : real) : (term567 x y z) = (term576 y x z).
Proof. exact (MK_COMB (@lem1580772 y x z) (@lem1580723 y x z)). Qed.
Lemma lem1580774 (y : real) (x : real) (z : real) : (term519 x y z) = (term576 y x z).
Proof. exact (TRANS (@lem1580667 x y z) (@lem1580773 y x z)). Qed.
Lemma lem1580775 (y : real) (x : real) (z : real) : (term101 y x z) = (term576 y x z).
Proof. exact (TRANS (@lem1580629 x y z) (@lem1580774 y x z)). Qed.
Lemma lem1580776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580777 (x : real) (y : real) (z : real) : (term107 y x z) = (term577 x y z).
Proof. exact (MK_COMB (@lem1580776) (@lem1580544 x y z)). Qed.
Lemma lem1580778 (y : real) (x : real) (z : real) : (term108 y x z) = (term578 y x z).
Proof. exact (MK_COMB (@lem1580777 x y z) (@lem1580775 y x z)). Qed.
Lemma lem1580780 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580781 (x : real) : (term133 x) = (term579 x).
Proof. exact (@lem1580780 x (term114 x) x term48). Qed.
Lemma lem1580793 (x : real) : (term580 x) = (term224 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1580795 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1580796 : term226 = term48.
Proof. exact (@lem1580795 term36). Qed.
Lemma lem1580797 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1580798 : term227 = term228.
Proof. exact (MK_COMB (@lem1580797) (@lem1580796)). Qed.
Lemma lem1580799 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1580800 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1580798) (@lem1580799 x)). Qed.
Lemma lem1580801 (x : real) : (term580 x) = (term229 x).
Proof. exact (TRANS (@lem1580793 x) (@lem1580800 x)). Qed.
Lemma lem1580802 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1580804 (x : real) : (term580 x) = term48.
Proof. exact (TRANS (@lem1580801 x) (@lem1580802 x)). Qed.
Lemma lem1580805 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580806 (x : real) : (term581 x) = term238.
Proof. exact (MK_COMB (@lem1580805) (@lem1580804 x)). Qed.
Lemma lem1580807 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580808 (x : real) : (term582 x) = term239.
Proof. exact (MK_COMB (@lem1580806 x) (@lem1580807)). Qed.
Lemma lem1580820 (x : real) : (term580 x) = (term224 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1580822 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1580823 : term226 = term48.
Proof. exact (@lem1580822 term36). Qed.
Lemma lem1580824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1580825 : term227 = term228.
Proof. exact (MK_COMB (@lem1580824) (@lem1580823)). Qed.
Lemma lem1580826 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1580827 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1580825) (@lem1580826 x)). Qed.
Lemma lem1580828 (x : real) : (term580 x) = (term229 x).
Proof. exact (TRANS (@lem1580820 x) (@lem1580827 x)). Qed.
Lemma lem1580829 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1580831 (x : real) : (term580 x) = term48.
Proof. exact (TRANS (@lem1580828 x) (@lem1580829 x)). Qed.
Lemma lem1580832 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580833 (x : real) : (term581 x) = term238.
Proof. exact (MK_COMB (@lem1580832) (@lem1580831 x)). Qed.
Lemma lem1580834 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580835 (x : real) : (term582 x) = term239.
Proof. exact (MK_COMB (@lem1580833 x) (@lem1580834)). Qed.
Lemma lem1580836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580837 (x : real) : (term583 x) = term256.
Proof. exact (MK_COMB (@lem1580836) (@lem1580835 x)). Qed.
Lemma lem1580838 (x : real) : (term579 x) = term584.
Proof. exact (MK_COMB (@lem1580837 x) (@lem1580808 x)). Qed.
Lemma lem1580841 (x : real) : (term133 x) = term584.
Proof. exact (TRANS (@lem1580781 x) (@lem1580838 x)). Qed.
Lemma lem1580843 (x : real) : (term585 x) = (term129 x).
Proof. exact (eq_refl (term585 x)). Qed.
Lemma lem1580844 (x : real) : (term129 x) = (term585 x).
Proof. exact (SYM (@lem1580843 x)). Qed.
Lemma lem1580845 (x : real) : (term585 x) = (term586 x).
Proof. exact (@lem1483429 x (term587 x) x). Qed.
Lemma lem1580846 (x : real) : (term129 x) = (term586 x).
Proof. exact (TRANS (@lem1580844 x) (@lem1580845 x)). Qed.
Lemma lem1580847 (x : real) : (term588 x) = (term221 x).
Proof. exact (eq_refl (term588 x)). Qed.
Lemma lem1580848 (x : real) : (term589 x) = (term589 x).
Proof. exact (eq_refl (term589 x)). Qed.
Lemma lem1580849 (x : real) : (term590 x) = (term591 x).
Proof. exact (MK_COMB (@lem1580848 x) (@lem1580847 x)). Qed.
Lemma lem1580850 (x : real) : (term588 x) = (term221 x).
Proof. exact (eq_refl (term588 x)). Qed.
Lemma lem1580851 (x : real) : (term592 x) = (term592 x).
Proof. exact (eq_refl (term592 x)). Qed.
Lemma lem1580852 (x : real) : (term593 x) = (term594 x).
Proof. exact (MK_COMB (@lem1580851 x) (@lem1580850 x)). Qed.
Lemma lem1580853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580854 (x : real) : (term595 x) = (term596 x).
Proof. exact (MK_COMB (@lem1580853) (@lem1580852 x)). Qed.
Lemma lem1580855 (x : real) : (term586 x) = (term597 x).
Proof. exact (MK_COMB (@lem1580854 x) (@lem1580849 x)). Qed.
Lemma lem1580856 (x : real) : (term598 x) = (term598 x).
Proof. exact (eq_refl (term598 x)). Qed.
Lemma lem1580857 (x : real) : ((term129 x) = (term586 x)) = ((term129 x) = (term597 x)).
Proof. exact (MK_COMB (@lem1580856 x) (@lem1580855 x)). Qed.
Lemma lem1580858 (x : real) : (term129 x) = (term597 x).
Proof. exact (EQ_MP (@lem1580857 x) (@lem1580846 x)). Qed.
Lemma lem1580859 (x : real) : (real_ge x x) = (term599 x).
Proof. exact (@lem1483527 x x). Qed.
Lemma lem1580865 (x : real) : (real_sub x x) = (term223 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1580869 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1580871 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1580872 : term226 = term48.
Proof. exact (@lem1580871 term36). Qed.
Lemma lem1580873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1580874 : term227 = term228.
Proof. exact (MK_COMB (@lem1580873) (@lem1580872)). Qed.
Lemma lem1580875 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1580876 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1580874) (@lem1580875 x)). Qed.
Lemma lem1580877 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1580869 x) (@lem1580876 x)). Qed.
Lemma lem1580878 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1580880 (x : real) : (term223 x) = term48.
Proof. exact (TRANS (@lem1580877 x) (@lem1580878 x)). Qed.
Lemma lem1580882 (x : real) : (real_sub x x) = term48.
Proof. exact (TRANS (@lem1580865 x) (@lem1580880 x)). Qed.
Lemma lem1580883 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1580884 (x : real) : (term600 x) = term601.
Proof. exact (MK_COMB (@lem1580883) (@lem1580882 x)). Qed.
Lemma lem1580885 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580886 (x : real) : (term599 x) = term602.
Proof. exact (MK_COMB (@lem1580884 x) (@lem1580885)). Qed.
Lemma lem1580887 (x : real) : (real_ge x x) = term602.
Proof. exact (TRANS (@lem1580859 x) (@lem1580886 x)). Qed.
Lemma lem1580888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580889 (x : real) : (term592 x) = term603.
Proof. exact (MK_COMB (@lem1580888) (@lem1580887 x)). Qed.
Lemma lem1580890 (x : real) : (term594 x) = term604.
Proof. exact (MK_COMB (@lem1580889 x) (@lem1578939 x)). Qed.
Lemma lem1580891 (x : real) : (real_gt x x) = (term605 x).
Proof. exact (@lem1483525 x x). Qed.
Lemma lem1580897 (x : real) : (real_sub x x) = (term223 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1580901 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1580903 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1580904 : term226 = term48.
Proof. exact (@lem1580903 term36). Qed.
Lemma lem1580905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1580906 : term227 = term228.
Proof. exact (MK_COMB (@lem1580905) (@lem1580904)). Qed.
Lemma lem1580907 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1580908 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1580906) (@lem1580907 x)). Qed.
Lemma lem1580909 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1580901 x) (@lem1580908 x)). Qed.
Lemma lem1580910 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1580912 (x : real) : (term223 x) = term48.
Proof. exact (TRANS (@lem1580909 x) (@lem1580910 x)). Qed.
Lemma lem1580914 (x : real) : (real_sub x x) = term48.
Proof. exact (TRANS (@lem1580897 x) (@lem1580912 x)). Qed.
Lemma lem1580915 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580916 (x : real) : (term606 x) = term238.
Proof. exact (MK_COMB (@lem1580915) (@lem1580914 x)). Qed.
Lemma lem1580917 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580918 (x : real) : (term605 x) = term239.
Proof. exact (MK_COMB (@lem1580916 x) (@lem1580917)). Qed.
Lemma lem1580919 (x : real) : (real_gt x x) = term239.
Proof. exact (TRANS (@lem1580891 x) (@lem1580918 x)). Qed.
Lemma lem1580920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580921 (x : real) : (term589 x) = term256.
Proof. exact (MK_COMB (@lem1580920) (@lem1580919 x)). Qed.
Lemma lem1580922 (x : real) : (term591 x) = term584.
Proof. exact (MK_COMB (@lem1580921 x) (@lem1578939 x)). Qed.
Lemma lem1580923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580924 (x : real) : (term596 x) = term607.
Proof. exact (MK_COMB (@lem1580923) (@lem1580890 x)). Qed.
Lemma lem1580925 (x : real) : (term597 x) = term608.
Proof. exact (MK_COMB (@lem1580924 x) (@lem1580922 x)). Qed.
Lemma lem1580937 (x : real) : (term129 x) = term608.
Proof. exact (TRANS (@lem1580858 x) (@lem1580925 x)). Qed.
Lemma lem1580938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1580939 (x : real) : (term135 x) = term609.
Proof. exact (MK_COMB (@lem1580938) (@lem1580841 x)). Qed.
Lemma lem1580940 (x : real) : (term136 x) = term610.
Proof. exact (MK_COMB (@lem1580939 x) (@lem1580937 x)). Qed.
Lemma lem1580942 (x : real) (a : real) (y : real) (r : real) : (term262 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1580943 (x : real) (y : real) : (term158 x y) = (term611 x y).
Proof. exact (@lem1580942 x (term29 x y) (real_min x y) term48). Qed.
Lemma lem1580955 (x : real) (y : real) : (term612 x y) = (term613 x y).
Proof. exact (@lem1483440 term28 (real_min x y)). Qed.
Lemma lem1580957 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1580958 : term226 = term48.
Proof. exact (@lem1580957 term36). Qed.
Lemma lem1580959 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1580960 : term227 = term228.
Proof. exact (MK_COMB (@lem1580959) (@lem1580958)). Qed.
Lemma lem1580961 (x : real) (y : real) : (real_min x y) = (real_min x y).
Proof. exact (eq_refl (real_min x y)). Qed.
Lemma lem1580962 (x : real) (y : real) : (term613 x y) = (term614 x y).
Proof. exact (MK_COMB (@lem1580960) (@lem1580961 x y)). Qed.
Lemma lem1580963 (x : real) (y : real) : (term612 x y) = (term614 x y).
Proof. exact (TRANS (@lem1580955 x y) (@lem1580962 x y)). Qed.
Lemma lem1580964 (x : real) (y : real) : (term614 x y) = term48.
Proof. exact (@lem1483446 (real_min x y)). Qed.
Lemma lem1580966 (x : real) (y : real) : (term612 x y) = term48.
Proof. exact (TRANS (@lem1580963 x y) (@lem1580964 x y)). Qed.
Lemma lem1580967 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580968 (x : real) (y : real) : (term615 x y) = term238.
Proof. exact (MK_COMB (@lem1580967) (@lem1580966 x y)). Qed.
Lemma lem1580969 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580970 (x : real) (y : real) : (term616 x y) = term239.
Proof. exact (MK_COMB (@lem1580968 x y) (@lem1580969)). Qed.
Lemma lem1580983 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 x (term29 x y)). Qed.
Lemma lem1580984 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1580985 (x : real) (y : real) : (term176 y x) = (term177 x y).
Proof. exact (MK_COMB (@lem1580984) (@lem1580983 x y)). Qed.
Lemma lem1580986 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1580987 (x : real) (y : real) : (term178 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1580985 x y) (@lem1580986)). Qed.
Lemma lem1580988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1580989 (x : real) (y : real) : (term617 y x) = (term461 x y).
Proof. exact (MK_COMB (@lem1580988) (@lem1580987 x y)). Qed.
Lemma lem1580990 (x : real) (y : real) : (term611 x y) = (term618 x y).
Proof. exact (MK_COMB (@lem1580989 x y) (@lem1580970 x y)). Qed.
Lemma lem1580991 (x : real) (y : real) : (term158 x y) = (term618 x y).
Proof. exact (TRANS (@lem1580943 x y) (@lem1580990 x y)). Qed.
Lemma lem1580992 (x : real) (y : real) : (term619 x y) = (term618 x y).
Proof. exact (eq_refl (term619 x y)). Qed.
Lemma lem1580993 (x : real) (y : real) : (term618 x y) = (term619 x y).
Proof. exact (SYM (@lem1580992 x y)). Qed.
Lemma lem1580994 (x : real) (y : real) : (term619 x y) = (term620 x y).
Proof. exact (@lem1483429 x (term621 x) y). Qed.
Lemma lem1580995 (x : real) (y : real) : (term618 x y) = (term620 x y).
Proof. exact (TRANS (@lem1580993 x y) (@lem1580994 x y)). Qed.
Lemma lem1580996 (x : real) (y : real) : (term622 x y) = (term241 x y).
Proof. exact (eq_refl (term622 x y)). Qed.
Lemma lem1580997 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1580998 (x : real) (y : real) : (term623 x y) = (term624 x y).
Proof. exact (MK_COMB (@lem1580997 x y) (@lem1580996 x y)). Qed.
Lemma lem1580999 (x : real) : (term625 x) = (term626 x).
Proof. exact (eq_refl (term625 x)). Qed.
Lemma lem1581000 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1581001 (y : real) (x : real) : (term627 y x) = (term628 y x).
Proof. exact (MK_COMB (@lem1581000 y x) (@lem1580999 x)). Qed.
Lemma lem1581002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581003 (y : real) (x : real) : (term629 y x) = (term630 y x).
Proof. exact (MK_COMB (@lem1581002) (@lem1581001 y x)). Qed.
Lemma lem1581004 (x : real) (y : real) : (term620 x y) = (term631 x y).
Proof. exact (MK_COMB (@lem1581003 y x) (@lem1580998 x y)). Qed.
Lemma lem1581005 (x : real) (y : real) : (term632 x y) = (term632 x y).
Proof. exact (eq_refl (term632 x y)). Qed.
Lemma lem1581006 (x : real) (y : real) : ((term618 x y) = (term620 x y)) = ((term618 x y) = (term631 x y)).
Proof. exact (MK_COMB (@lem1581005 x y) (@lem1581004 x y)). Qed.
Lemma lem1581007 (x : real) (y : real) : (term618 x y) = (term631 x y).
Proof. exact (EQ_MP (@lem1581006 x y) (@lem1580995 x y)). Qed.
Lemma lem1581008 : term239 = term633.
Proof. exact (@lem1483525 term48 term48). Qed.
Lemma lem1581014 : term233 = term234.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1581016 (x : nat) : (term215 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1581017 : term216 = term48.
Proof. exact (@lem1581016 term36). Qed.
Lemma lem1581018 : term235 = term235.
Proof. exact (eq_refl term235). Qed.
Lemma lem1581019 : term234 = term236.
Proof. exact (MK_COMB (@lem1581018) (@lem1581017)). Qed.
Lemma lem1581020 : term236 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1581021 : term234 = term48.
Proof. exact (TRANS (@lem1581019) (@lem1581020)). Qed.
Lemma lem1581023 : term233 = term48.
Proof. exact (TRANS (@lem1581014) (@lem1581021)). Qed.
Lemma lem1581024 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1581025 : term634 = term238.
Proof. exact (MK_COMB (@lem1581024) (@lem1581023)). Qed.
Lemma lem1581026 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581027 : term633 = term239.
Proof. exact (MK_COMB (@lem1581025) (@lem1581026)). Qed.
Lemma lem1581028 : term239 = term239.
Proof. exact (TRANS (@lem1581008) (@lem1581027)). Qed.
Lemma lem1581029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581030 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1581029) (@lem1578939 x)). Qed.
Lemma lem1581031 (x : real) : (term626 x) = term584.
Proof. exact (MK_COMB (@lem1581030 x) (@lem1581028)). Qed.
Lemma lem1581032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581033 (x : real) (y : real) : (term199 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem1581032) (@lem1579069 x y)). Qed.
Lemma lem1581034 (x : real) (y : real) : (term628 y x) = (term635 x y).
Proof. exact (MK_COMB (@lem1581033 x y) (@lem1581031 x)). Qed.
Lemma lem1581035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581036 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1581035) (@lem1578828 x y)). Qed.
Lemma lem1581037 (x : real) (y : real) : (term241 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1581036 x y) (@lem1581028)). Qed.
Lemma lem1581038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581039 (x : real) (y : real) : (term194 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1581038) (@lem1579094 x y)). Qed.
Lemma lem1581040 (x : real) (y : real) : (term624 x y) = (term636 x y).
Proof. exact (MK_COMB (@lem1581039 x y) (@lem1581037 x y)). Qed.
Lemma lem1581041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581042 (x : real) (y : real) : (term630 y x) = (term637 x y).
Proof. exact (MK_COMB (@lem1581041) (@lem1581034 x y)). Qed.
Lemma lem1581043 (x : real) (y : real) : (term631 x y) = (term638 x y).
Proof. exact (MK_COMB (@lem1581042 x y) (@lem1581040 x y)). Qed.
Lemma lem1581054 (x : real) (y : real) : (term618 x y) = (term638 x y).
Proof. exact (TRANS (@lem1581007 x y) (@lem1581043 x y)). Qed.
Lemma lem1581055 (x : real) (y : real) : (term158 x y) = (term638 x y).
Proof. exact (TRANS (@lem1580991 x y) (@lem1581054 x y)). Qed.
Lemma lem1581057 (x : real) (a : real) (y : real) (r : real) : (term171 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1581058 (x : real) (y : real) : (term154 x y) = (term639 x y).
Proof. exact (@lem1581057 x (term146 x y) y term48). Qed.
Lemma lem1581071 (x : real) (y : real) : (term640 x y) = (term641 x y).
Proof. exact (@lem1483488 y (term146 x y)). Qed.
Lemma lem1581072 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1581073 (x : real) (y : real) : (term642 x y) = (term643 x y).
Proof. exact (MK_COMB (@lem1581072) (@lem1581071 x y)). Qed.
Lemma lem1581074 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581075 (x : real) (y : real) : (term644 x y) = (term645 x y).
Proof. exact (MK_COMB (@lem1581073 x y) (@lem1581074)). Qed.
Lemma lem1581088 (x : real) (y : real) : (term646 y x) = (term647 x y).
Proof. exact (@lem1483488 x (term146 x y)). Qed.
Lemma lem1581089 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1581090 (x : real) (y : real) : (term648 y x) = (term649 x y).
Proof. exact (MK_COMB (@lem1581089) (@lem1581088 x y)). Qed.
Lemma lem1581091 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581092 (x : real) (y : real) : (term650 y x) = (term651 x y).
Proof. exact (MK_COMB (@lem1581090 x y) (@lem1581091)). Qed.
Lemma lem1581093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581094 (x : real) (y : real) : (term652 y x) = (term653 x y).
Proof. exact (MK_COMB (@lem1581093) (@lem1581092 x y)). Qed.
Lemma lem1581095 (x : real) (y : real) : (term639 x y) = (term654 x y).
Proof. exact (MK_COMB (@lem1581094 x y) (@lem1581075 x y)). Qed.
Lemma lem1581096 (x : real) (y : real) : (term154 x y) = (term654 x y).
Proof. exact (TRANS (@lem1581058 x y) (@lem1581095 x y)). Qed.
Lemma lem1581097 (x : real) (y : real) : (term655 x y) = (term654 x y).
Proof. exact (eq_refl (term655 x y)). Qed.
Lemma lem1581098 (x : real) (y : real) : (term654 x y) = (term655 x y).
Proof. exact (SYM (@lem1581097 x y)). Qed.
Lemma lem1581099 (x : real) (y : real) : (term655 x y) = (term656 x y).
Proof. exact (@lem1483429 x (term191 x y) (real_min x y)). Qed.
Lemma lem1581100 (x : real) (y : real) : (term654 x y) = (term656 x y).
Proof. exact (TRANS (@lem1581098 x y) (@lem1581099 x y)). Qed.
Lemma lem1581101 (x : real) (y : real) : (term657 x y) = (term658 x y).
Proof. exact (eq_refl (term657 x y)). Qed.
Lemma lem1581102 (x : real) (y : real) : (term659 x y) = (term659 x y).
Proof. exact (eq_refl (term659 x y)). Qed.
Lemma lem1581103 (x : real) (y : real) : (term660 x y) = (term661 x y).
Proof. exact (MK_COMB (@lem1581102 x y) (@lem1581101 x y)). Qed.
Lemma lem1581104 (y : real) (x : real) : (term192 y x) = (term193 y x).
Proof. exact (eq_refl (term192 y x)). Qed.
Lemma lem1581105 (y : real) (x : real) : (term662 y x) = (term662 y x).
Proof. exact (eq_refl (term662 y x)). Qed.
Lemma lem1581106 (y : real) (x : real) : (term663 y x) = (term664 y x).
Proof. exact (MK_COMB (@lem1581105 y x) (@lem1581104 y x)). Qed.
Lemma lem1581107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581108 (y : real) (x : real) : (term665 y x) = (term666 y x).
Proof. exact (MK_COMB (@lem1581107) (@lem1581106 y x)). Qed.
Lemma lem1581109 (x : real) (y : real) : (term656 x y) = (term667 x y).
Proof. exact (MK_COMB (@lem1581108 y x) (@lem1581103 x y)). Qed.
Lemma lem1581110 (x : real) (y : real) : (term668 x y) = (term668 x y).
Proof. exact (eq_refl (term668 x y)). Qed.
Lemma lem1581111 (x : real) (y : real) : ((term654 x y) = (term656 x y)) = ((term654 x y) = (term667 x y)).
Proof. exact (MK_COMB (@lem1581110 x y) (@lem1581109 x y)). Qed.
Lemma lem1581112 (x : real) (y : real) : (term654 x y) = (term667 x y).
Proof. exact (EQ_MP (@lem1581111 x y) (@lem1581100 x y)). Qed.
Lemma lem1581113 (y : real) (x : real) : (term669 y x) = (term670 y x).
Proof. exact (@lem1483527 (real_min x y) x). Qed.
Lemma lem1581119 (y : real) (x : real) : (term671 y x) = (term672 y x).
Proof. exact (@lem1483519 (real_min x y) x). Qed.
Lemma lem1581124 (x : real) (y : real) : (term672 y x) = (term673 x y).
Proof. exact (@lem1483488 (term114 x) (real_min x y)). Qed.
Lemma lem1581126 (x : real) (y : real) : (term671 y x) = (term673 x y).
Proof. exact (TRANS (@lem1581119 y x) (@lem1581124 x y)). Qed.
Lemma lem1581127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1581128 (x : real) (y : real) : (term674 y x) = (term675 x y).
Proof. exact (MK_COMB (@lem1581127) (@lem1581126 x y)). Qed.
Lemma lem1581129 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581130 (x : real) (y : real) : (term670 y x) = (term676 x y).
Proof. exact (MK_COMB (@lem1581128 x y) (@lem1581129)). Qed.
Lemma lem1581131 (x : real) (y : real) : (term669 y x) = (term676 x y).
Proof. exact (TRANS (@lem1581113 y x) (@lem1581130 x y)). Qed.
Lemma lem1581132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581133 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1581132) (@lem1578939 x)). Qed.
Lemma lem1581134 (x : real) (y : real) : (term193 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1581133 x) (@lem1578972 x y)). Qed.
Lemma lem1581135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581136 (x : real) (y : real) : (term662 y x) = (term677 x y).
Proof. exact (MK_COMB (@lem1581135) (@lem1581131 x y)). Qed.
Lemma lem1581137 (x : real) (y : real) : (term664 y x) = (term678 x y).
Proof. exact (MK_COMB (@lem1581136 x y) (@lem1581134 x y)). Qed.
Lemma lem1581138 (x : real) (y : real) : (term679 x y) = (term680 x y).
Proof. exact (@lem1483525 x (real_min x y)). Qed.
Lemma lem1581151 (x : real) (y : real) : (term681 x y) = (term175 x y).
Proof. exact (@lem1483519 x (real_min x y)). Qed.
Lemma lem1581152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1581153 (x : real) (y : real) : (term682 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem1581152) (@lem1581151 x y)). Qed.
Lemma lem1581154 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581155 (x : real) (y : real) : (term680 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1581153 x y) (@lem1581154)). Qed.
Lemma lem1581156 (x : real) (y : real) : (term679 x y) = (term179 x y).
Proof. exact (TRANS (@lem1581138 x y) (@lem1581155 x y)). Qed.
Lemma lem1581157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581158 (x : real) (y : real) : (term461 x y) = (term461 x y).
Proof. exact (MK_COMB (@lem1581157) (@lem1579854 x y)). Qed.
Lemma lem1581159 (x : real) (y : real) : (term658 x y) = (term658 x y).
Proof. exact (MK_COMB (@lem1581158 x y) (@lem1579887 x y)). Qed.
Lemma lem1581160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581161 (x : real) (y : real) : (term659 x y) = (term461 x y).
Proof. exact (MK_COMB (@lem1581160) (@lem1581156 x y)). Qed.
Lemma lem1581162 (x : real) (y : real) : (term661 x y) = (term683 x y).
Proof. exact (MK_COMB (@lem1581161 x y) (@lem1581159 x y)). Qed.
Lemma lem1581163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581164 (x : real) (y : real) : (term666 y x) = (term684 x y).
Proof. exact (MK_COMB (@lem1581163) (@lem1581137 x y)). Qed.
Lemma lem1581165 (x : real) (y : real) : (term667 x y) = (term685 x y).
Proof. exact (MK_COMB (@lem1581164 x y) (@lem1581162 x y)). Qed.
Lemma lem1581166 (x : real) (y : real) : (term654 x y) = (term685 x y).
Proof. exact (TRANS (@lem1581112 x y) (@lem1581165 x y)). Qed.
Lemma lem1581168 (x : real) (y : real) : (term686 x y) = (term683 x y).
Proof. exact (eq_refl (term686 x y)). Qed.
Lemma lem1581169 (x : real) (y : real) : (term683 x y) = (term686 x y).
Proof. exact (SYM (@lem1581168 x y)). Qed.
Lemma lem1581170 (x : real) (y : real) : (term686 x y) = (term687 x y).
Proof. exact (@lem1483429 x (term688 x y) y). Qed.
Lemma lem1581171 (x : real) (y : real) : (term683 x y) = (term687 x y).
Proof. exact (TRANS (@lem1581169 x y) (@lem1581170 x y)). Qed.
Lemma lem1581172 (x : real) (y : real) : (term689 x y) = (term690 x y).
Proof. exact (eq_refl (term689 x y)). Qed.
Lemma lem1581173 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1581174 (x : real) (y : real) : (term691 x y) = (term692 x y).
Proof. exact (MK_COMB (@lem1581173 x y) (@lem1581172 x y)). Qed.
Lemma lem1581175 (y : real) (x : real) : (term693 y x) = (term694 y x).
Proof. exact (eq_refl (term693 y x)). Qed.
Lemma lem1581176 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1581177 (y : real) (x : real) : (term695 y x) = (term696 y x).
Proof. exact (MK_COMB (@lem1581176 y x) (@lem1581175 y x)). Qed.
Lemma lem1581178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581179 (y : real) (x : real) : (term697 y x) = (term698 y x).
Proof. exact (MK_COMB (@lem1581178) (@lem1581177 y x)). Qed.
Lemma lem1581180 (x : real) (y : real) : (term687 x y) = (term699 x y).
Proof. exact (MK_COMB (@lem1581179 y x) (@lem1581174 x y)). Qed.
Lemma lem1581181 (x : real) (y : real) : (term700 x y) = (term700 x y).
Proof. exact (eq_refl (term700 x y)). Qed.
Lemma lem1581182 (x : real) (y : real) : ((term683 x y) = (term687 x y)) = ((term683 x y) = (term699 x y)).
Proof. exact (MK_COMB (@lem1581181 x y) (@lem1581180 x y)). Qed.
Lemma lem1581183 (x : real) (y : real) : (term683 x y) = (term699 x y).
Proof. exact (EQ_MP (@lem1581182 x y) (@lem1581171 x y)). Qed.
Lemma lem1581184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581185 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1581184) (@lem1578939 x)). Qed.
Lemma lem1581186 (x : real) (y : real) : (term193 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1581185 x) (@lem1578972 x y)). Qed.
Lemma lem1581187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581188 (x : real) : (term255 x) = term256.
Proof. exact (MK_COMB (@lem1581187) (@lem1578939 x)). Qed.
Lemma lem1581189 (x : real) (y : real) : (term694 y x) = (term701 x y).
Proof. exact (MK_COMB (@lem1581188 x) (@lem1581186 x y)). Qed.
Lemma lem1581190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581191 (x : real) (y : real) : (term199 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem1581190) (@lem1579069 x y)). Qed.
Lemma lem1581192 (x : real) (y : real) : (term696 y x) = (term702 x y).
Proof. exact (MK_COMB (@lem1581191 x y) (@lem1581189 x y)). Qed.
Lemma lem1581193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581194 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1581193) (@lem1578828 x y)). Qed.
Lemma lem1581195 (x : real) (y : real) : (term198 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1581194 x y) (@lem1578871 y)). Qed.
Lemma lem1581196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581197 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1581196) (@lem1578828 x y)). Qed.
Lemma lem1581198 (x : real) (y : real) : (term690 x y) = (term636 x y).
Proof. exact (MK_COMB (@lem1581197 x y) (@lem1581195 x y)). Qed.
Lemma lem1581199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581200 (x : real) (y : real) : (term194 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1581199) (@lem1579094 x y)). Qed.
Lemma lem1581201 (x : real) (y : real) : (term692 x y) = (term703 x y).
Proof. exact (MK_COMB (@lem1581200 x y) (@lem1581198 x y)). Qed.
Lemma lem1581202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581203 (x : real) (y : real) : (term698 y x) = (term704 x y).
Proof. exact (MK_COMB (@lem1581202) (@lem1581192 x y)). Qed.
Lemma lem1581204 (x : real) (y : real) : (term699 x y) = (term705 x y).
Proof. exact (MK_COMB (@lem1581203 x y) (@lem1581201 x y)). Qed.
Lemma lem1581216 (x : real) (y : real) : (term683 x y) = (term705 x y).
Proof. exact (TRANS (@lem1581183 x y) (@lem1581204 x y)). Qed.
Lemma lem1581218 (x : real) (a : real) (y : real) (r : real) : (term398 a x y r) = (term399 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1581219 (x : real) (y : real) : (term676 x y) = (term706 x y).
Proof. exact (@lem1581218 x (term114 x) y term48). Qed.
Lemma lem1581236 (x : real) (y : real) : (term264 x y) = (term264 x y).
Proof. exact (eq_refl (term264 x y)). Qed.
Lemma lem1581248 (x : real) : (term580 x) = (term224 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1581250 (m : nat) : (term225 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1581251 : term226 = term48.
Proof. exact (@lem1581250 term36). Qed.
Lemma lem1581252 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1581253 : term227 = term228.
Proof. exact (MK_COMB (@lem1581252) (@lem1581251)). Qed.
Lemma lem1581254 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1581255 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1581253) (@lem1581254 x)). Qed.
Lemma lem1581256 (x : real) : (term580 x) = (term229 x).
Proof. exact (TRANS (@lem1581248 x) (@lem1581255 x)). Qed.
Lemma lem1581257 (x : real) : (term229 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1581259 (x : real) : (term580 x) = term48.
Proof. exact (TRANS (@lem1581256 x) (@lem1581257 x)). Qed.
Lemma lem1581260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1581261 (x : real) : (term707 x) = term601.
Proof. exact (MK_COMB (@lem1581260) (@lem1581259 x)). Qed.
Lemma lem1581262 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1581263 (x : real) : (term708 x) = term602.
Proof. exact (MK_COMB (@lem1581261 x) (@lem1581262)). Qed.
Lemma lem1581264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581265 (x : real) : (term709 x) = term603.
Proof. exact (MK_COMB (@lem1581264) (@lem1581263 x)). Qed.
Lemma lem1581266 (x : real) (y : real) : (term706 x y) = (term710 x y).
Proof. exact (MK_COMB (@lem1581265 x) (@lem1581236 x y)). Qed.
Lemma lem1581267 (x : real) (y : real) : (term676 x y) = (term710 x y).
Proof. exact (TRANS (@lem1581219 x y) (@lem1581266 x y)). Qed.
Lemma lem1581268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1581269 (x : real) (y : real) : (term677 x y) = (term711 x y).
Proof. exact (MK_COMB (@lem1581268) (@lem1581267 x y)). Qed.
Lemma lem1581270 (x : real) (y : real) : (term257 x y) = (term257 x y).
Proof. exact (eq_refl (term257 x y)). Qed.
Lemma lem1581273 (x : real) (y : real) : (term678 x y) = (term712 x y).
Proof. exact (MK_COMB (@lem1581269 x y) (@lem1581270 x y)). Qed.
Lemma lem1581274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581275 (x : real) (y : real) : (term684 x y) = (term713 x y).
Proof. exact (MK_COMB (@lem1581274) (@lem1581273 x y)). Qed.
Lemma lem1581276 (x : real) (y : real) : (term685 x y) = (term714 x y).
Proof. exact (MK_COMB (@lem1581275 x y) (@lem1581216 x y)). Qed.
Lemma lem1581277 (x : real) (y : real) : (term654 x y) = (term714 x y).
Proof. exact (TRANS (@lem1581166 x y) (@lem1581276 x y)). Qed.
Lemma lem1581278 (x : real) (y : real) : (term154 x y) = (term714 x y).
Proof. exact (TRANS (@lem1581096 x y) (@lem1581277 x y)). Qed.
Lemma lem1581279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581280 (x : real) (y : real) : (term160 x y) = (term715 x y).
Proof. exact (MK_COMB (@lem1581279) (@lem1581055 x y)). Qed.
Lemma lem1581281 (x : real) (y : real) : (term161 x y) = (term716 x y).
Proof. exact (MK_COMB (@lem1581280 x y) (@lem1581278 x y)). Qed.
Lemma lem1581282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581283 (x : real) : (term163 x) = term717.
Proof. exact (MK_COMB (@lem1581282) (@lem1580940 x)). Qed.
Lemma lem1581284 (x : real) (y : real) : (term164 x y) = (term718 x y).
Proof. exact (MK_COMB (@lem1581283 x) (@lem1581281 x y)). Qed.
Lemma lem1581285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581286 (y : real) (x : real) (z : real) : (term165 y x z) = (term719 y x z).
Proof. exact (MK_COMB (@lem1581285) (@lem1580778 y x z)). Qed.
Lemma lem1581287 (z : real) (x : real) (y : real) : (term166 z x y) = (term720 z x y).
Proof. exact (MK_COMB (@lem1581286 y x z) (@lem1581284 x y)). Qed.
Lemma lem1581288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581289 (x : real) (y : real) (z : real) : (term167 x y z) = (term721 x y z).
Proof. exact (MK_COMB (@lem1581288) (@lem1580138 x y z)). Qed.
Lemma lem1581290 (z : real) (x : real) (y : real) : (term168 z x y) = (term722 z x y).
Proof. exact (MK_COMB (@lem1581289 x y z) (@lem1581287 z x y)). Qed.
Lemma lem1581291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1581292 (x : real) (y : real) : (term169 y x) = (term723 x y).
Proof. exact (MK_COMB (@lem1581291) (@lem1579118 x y)). Qed.
Lemma lem1581293 (z : real) (x : real) (y : real) : (term170 z x y) = (term724 z x y).
Proof. exact (MK_COMB (@lem1581292 x y) (@lem1581290 z x y)). Qed.
Lemma lem1581294 (z : real) (x : real) (y : real) (h1 : term724 z x y) : term724 z x y.
Proof. exact (h1). Qed.
Lemma lem1581295 (x : real) (y : real) (h1 : term273 x y) : term273 x y.
Proof. exact (h1). Qed.
Lemma lem1581296 (x : real) (y : real) (h1 : term261 x y) : term261 x y.
Proof. exact (h1). Qed.
Lemma lem1581297 (x : real) (y : real) (h1 : term243 x y) : term243 x y.
Proof. exact (h1). Qed.
Lemma lem1581298 (x : real) (y : real) (h1 : term243 x y) : term241 x y.
Proof. exact (proj2 (@lem1581297 x y h1)). Qed.
Lemma lem1581300 (x : real) (y : real) (h1 : term243 x y) : term239.
Proof. exact (proj2 (@lem1581298 x y h1)). Qed.
Lemma lem1581303 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581304 : term239 = term726.
Proof. exact (@lem1581303 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581305 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581306 : term239 = False.
Proof. exact (TRANS (@lem1581304) (@lem1581305)). Qed.
Lemma lem1581307 (x : real) (y : real) (h1 : term243 x y) : False.
Proof. exact (EQ_MP (@lem1581306) (@lem1581300 x y h1)). Qed.
Lemma lem1581308 (x : real) (y : real) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1581309 (x : real) (y : real) (h1 : term259 x y) : term257 x y.
Proof. exact (proj2 (@lem1581308 x y h1)). Qed.
Lemma lem1581312 (x : real) (y : real) (h1 : term259 x y) : term239.
Proof. exact (proj1 (@lem1581309 x y h1)). Qed.
Lemma lem1581314 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581315 : term239 = term726.
Proof. exact (@lem1581314 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581316 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581317 : term239 = False.
Proof. exact (TRANS (@lem1581315) (@lem1581316)). Qed.
Lemma lem1581318 (x : real) (y : real) (h1 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1581317) (@lem1581312 x y h1)). Qed.
Lemma lem1581319 (x : real) (y : real) (h1 : term261 x y) : False.
Proof. exact (or_elim (@lem1581296 x y h1) (fun h0 : term243 x y => @lem1581307 x y h0) (fun h0 : term259 x y => @lem1581318 x y h0)). Qed.
Lemma lem1581320 (x : real) (y : real) (h1 : term271 x y) : term271 x y.
Proof. exact (h1). Qed.
Lemma lem1581321 (x : real) (y : real) (h1 : term267 x y) : term267 x y.
Proof. exact (h1). Qed.
Lemma lem1581322 (x : real) (y : real) (h1 : term267 x y) : term265 x y.
Proof. exact (proj2 (@lem1581321 x y h1)). Qed.
Lemma lem1581324 (x : real) (y : real) (h1 : term267 x y) : term239.
Proof. exact (proj2 (@lem1581322 x y h1)). Qed.
Lemma lem1581327 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581328 : term239 = term726.
Proof. exact (@lem1581327 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581329 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581330 : term239 = False.
Proof. exact (TRANS (@lem1581328) (@lem1581329)). Qed.
Lemma lem1581331 (x : real) (y : real) (h1 : term267 x y) : False.
Proof. exact (EQ_MP (@lem1581330) (@lem1581324 x y h1)). Qed.
Lemma lem1581332 (x : real) (y : real) (h1 : term269 x y) : term269 x y.
Proof. exact (h1). Qed.
Lemma lem1581333 (x : real) (y : real) (h1 : term269 x y) : term268 x y.
Proof. exact (proj2 (@lem1581332 x y h1)). Qed.
Lemma lem1581336 (x : real) (y : real) (h1 : term269 x y) : term239.
Proof. exact (proj1 (@lem1581333 x y h1)). Qed.
Lemma lem1581338 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581339 : term239 = term726.
Proof. exact (@lem1581338 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581340 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581341 : term239 = False.
Proof. exact (TRANS (@lem1581339) (@lem1581340)). Qed.
Lemma lem1581342 (x : real) (y : real) (h1 : term269 x y) : False.
Proof. exact (EQ_MP (@lem1581341) (@lem1581336 x y h1)). Qed.
Lemma lem1581343 (x : real) (y : real) (h1 : term271 x y) : False.
Proof. exact (or_elim (@lem1581320 x y h1) (fun h0 : term267 x y => @lem1581331 x y h0) (fun h0 : term269 x y => @lem1581342 x y h0)). Qed.
Lemma lem1581344 (x : real) (y : real) (h1 : term273 x y) : False.
Proof. exact (or_elim (@lem1581295 x y h1) (fun h0 : term261 x y => @lem1581319 x y h0) (fun h0 : term271 x y => @lem1581343 x y h0)). Qed.
Lemma lem1581345 (z : real) (x : real) (y : real) (h1 : term722 z x y) : term722 z x y.
Proof. exact (h1). Qed.
Lemma lem1581346 (x : real) (y : real) (z : real) (h1 : term506 x y z) : term506 x y z.
Proof. exact (h1). Qed.
Lemma lem1581347 (x : real) (y : real) (z : real) (h1 : term404 x y z) : term404 x y z.
Proof. exact (h1). Qed.
Lemma lem1581348 (y : real) (x : real) (z : real) (h1 : term402 y x z) : term402 y x z.
Proof. exact (h1). Qed.
Lemma lem1581349 (y : real) (x : real) (z : real) (h1 : term402 y x z) : term335 y x z.
Proof. exact (proj2 (@lem1581348 y x z h1)). Qed.
Lemma lem1581354 (y : real) (x : real) (z : real) (h1 : term402 y x z) : term257 x y.
Proof. exact (proj1 (@lem1581349 y x z h1)). Qed.
Lemma lem1581356 (y : real) (x : real) (z : real) (h1 : term402 y x z) : term239.
Proof. exact (proj1 (@lem1581354 y x z h1)). Qed.
Lemma lem1581358 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581359 : term239 = term726.
Proof. exact (@lem1581358 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581360 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581361 : term239 = False.
Proof. exact (TRANS (@lem1581359) (@lem1581360)). Qed.
Lemma lem1581362 (y : real) (x : real) (z : real) (h1 : term402 y x z) : False.
Proof. exact (EQ_MP (@lem1581361) (@lem1581356 y x z h1)). Qed.
Lemma lem1581363 (x : real) (y : real) (z : real) (h1 : term397 x y z) : term397 x y z.
Proof. exact (h1). Qed.
Lemma lem1581364 (x : real) (y : real) (z : real) (h1 : term389 x y z) : term389 x y z.
Proof. exact (h1). Qed.
Lemma lem1581365 (x : real) (y : real) (z : real) (h1 : term389 x y z) : term388 x y z.
Proof. exact (proj2 (@lem1581364 x y z h1)). Qed.
Lemma lem1581367 (x : real) (y : real) (z : real) (h1 : term389 x y z) : term387 x y z.
Proof. exact (proj2 (@lem1581365 x y z h1)). Qed.
Lemma lem1581370 (x : real) (y : real) (z : real) (h1 : term389 x y z) : term241 x y.
Proof. exact (proj1 (@lem1581367 x y z h1)). Qed.
Lemma lem1581371 (x : real) (y : real) (z : real) (h1 : term389 x y z) : term239.
Proof. exact (proj2 (@lem1581370 x y z h1)). Qed.
Lemma lem1581374 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581375 : term239 = term726.
Proof. exact (@lem1581374 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581376 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581377 : term239 = False.
Proof. exact (TRANS (@lem1581375) (@lem1581376)). Qed.
Lemma lem1581378 (x : real) (y : real) (z : real) (h1 : term389 x y z) : False.
Proof. exact (EQ_MP (@lem1581377) (@lem1581371 x y z h1)). Qed.
Lemma lem1581379 (x : real) (y : real) (z : real) (h1 : term395 x y z) : term395 x y z.
Proof. exact (h1). Qed.
Lemma lem1581380 (x : real) (y : real) (z : real) (h1 : term395 x y z) : term394 x y z.
Proof. exact (proj2 (@lem1581379 x y z h1)). Qed.
Lemma lem1581382 (x : real) (y : real) (z : real) (h1 : term395 x y z) : term393 x y z.
Proof. exact (proj2 (@lem1581380 x y z h1)). Qed.
Lemma lem1581384 (x : real) (y : real) (z : real) (h1 : term395 x y z) : term239.
Proof. exact (proj2 (@lem1581382 x y z h1)). Qed.
Lemma lem1581389 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581390 : term239 = term726.
Proof. exact (@lem1581389 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581391 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581392 : term239 = False.
Proof. exact (TRANS (@lem1581390) (@lem1581391)). Qed.
Lemma lem1581393 (x : real) (y : real) (z : real) (h1 : term395 x y z) : False.
Proof. exact (EQ_MP (@lem1581392) (@lem1581384 x y z h1)). Qed.
Lemma lem1581394 (x : real) (y : real) (z : real) (h1 : term397 x y z) : False.
Proof. exact (or_elim (@lem1581363 x y z h1) (fun h0 : term389 x y z => @lem1581378 x y z h0) (fun h0 : term395 x y z => @lem1581393 x y z h0)). Qed.
Lemma lem1581395 (x : real) (y : real) (z : real) (h1 : term404 x y z) : False.
Proof. exact (or_elim (@lem1581347 x y z h1) (fun h0 : term402 y x z => @lem1581362 y x z h0) (fun h0 : term397 x y z => @lem1581394 x y z h0)). Qed.
Lemma lem1581396 (x : real) (y : real) (z : real) (h1 : term504 x y z) : term504 x y z.
Proof. exact (h1). Qed.
Lemma lem1581397 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term502 x y z.
Proof. exact (h1). Qed.
Lemma lem1581398 (y : real) (x : real) (z : real) (h1 : term496 y x z) : term496 y x z.
Proof. exact (h1). Qed.
Lemma lem1581399 (y : real) (x : real) (z : real) (h1 : term496 y x z) : term495 y x z.
Proof. exact (proj2 (@lem1581398 y x z h1)). Qed.
Lemma lem1581401 (y : real) (x : real) (z : real) (h1 : term496 y x z) : term494 y x z.
Proof. exact (proj2 (@lem1581399 y x z h1)). Qed.
Lemma lem1581404 (y : real) (x : real) (z : real) (h1 : term496 y x z) : term239.
Proof. exact (proj1 (@lem1581401 y x z h1)). Qed.
Lemma lem1581408 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581409 : term239 = term726.
Proof. exact (@lem1581408 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581410 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581411 : term239 = False.
Proof. exact (TRANS (@lem1581409) (@lem1581410)). Qed.
Lemma lem1581412 (y : real) (x : real) (z : real) (h1 : term496 y x z) : False.
Proof. exact (EQ_MP (@lem1581411) (@lem1581404 y x z h1)). Qed.
Lemma lem1581413 (x : real) (y : real) (z : real) (h1 : term500 x y z) : term500 x y z.
Proof. exact (h1). Qed.
Lemma lem1581414 (x : real) (y : real) (z : real) (h1 : term500 x y z) : term499 x y z.
Proof. exact (proj2 (@lem1581413 x y z h1)). Qed.
Lemma lem1581416 (x : real) (y : real) (z : real) (h1 : term500 x y z) : term498 x y z.
Proof. exact (proj2 (@lem1581414 x y z h1)). Qed.
Lemma lem1581418 (x : real) (y : real) (z : real) (h1 : term500 x y z) : term257 y z.
Proof. exact (proj2 (@lem1581416 x y z h1)). Qed.
Lemma lem1581421 (x : real) (y : real) (z : real) (h1 : term500 x y z) : term239.
Proof. exact (proj1 (@lem1581418 x y z h1)). Qed.
Lemma lem1581423 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581424 : term239 = term726.
Proof. exact (@lem1581423 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581425 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581426 : term239 = False.
Proof. exact (TRANS (@lem1581424) (@lem1581425)). Qed.
Lemma lem1581427 (x : real) (y : real) (z : real) (h1 : term500 x y z) : False.
Proof. exact (EQ_MP (@lem1581426) (@lem1581421 x y z h1)). Qed.
Lemma lem1581428 (x : real) (y : real) (z : real) (h1 : term502 x y z) : False.
Proof. exact (or_elim (@lem1581397 x y z h1) (fun h0 : term496 y x z => @lem1581412 y x z h0) (fun h0 : term500 x y z => @lem1581427 x y z h0)). Qed.
Lemma lem1581429 (x : real) (y : real) (z : real) (h1 : term475 x y z) : term475 x y z.
Proof. exact (h1). Qed.
Lemma lem1581430 (x : real) (y : real) (z : real) (h1 : term475 x y z) : term469 x y z.
Proof. exact (proj2 (@lem1581429 x y z h1)). Qed.
Lemma lem1581434 (x : real) (y : real) (z : real) (h1 : term475 x y z) : term241 y z.
Proof. exact (proj2 (@lem1581430 x y z h1)). Qed.
Lemma lem1581436 (x : real) (y : real) (z : real) (h1 : term475 x y z) : term239.
Proof. exact (proj2 (@lem1581434 x y z h1)). Qed.
Lemma lem1581439 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581440 : term239 = term726.
Proof. exact (@lem1581439 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581441 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581442 : term239 = False.
Proof. exact (TRANS (@lem1581440) (@lem1581441)). Qed.
Lemma lem1581443 (x : real) (y : real) (z : real) (h1 : term475 x y z) : False.
Proof. exact (EQ_MP (@lem1581442) (@lem1581436 x y z h1)). Qed.
Lemma lem1581444 (x : real) (y : real) (z : real) (h1 : term504 x y z) : False.
Proof. exact (or_elim (@lem1581396 x y z h1) (fun h0 : term502 x y z => @lem1581428 x y z h0) (fun h0 : term475 x y z => @lem1581443 x y z h0)). Qed.
Lemma lem1581445 (x : real) (y : real) (z : real) (h1 : term506 x y z) : False.
Proof. exact (or_elim (@lem1581346 x y z h1) (fun h0 : term404 x y z => @lem1581395 x y z h0) (fun h0 : term504 x y z => @lem1581444 x y z h0)). Qed.
Lemma lem1581446 (z : real) (x : real) (y : real) (h1 : term720 z x y) : term720 z x y.
Proof. exact (h1). Qed.
Lemma lem1581447 (y : real) (x : real) (z : real) (h1 : term578 y x z) : term578 y x z.
Proof. exact (h1). Qed.
Lemma lem1581448 (x : real) (y : real) (z : real) (h1 : term563 x y z) : term563 x y z.
Proof. exact (h1). Qed.
Lemma lem1581449 (x : real) (y : real) (z : real) (h1 : term561 x y z) : term561 x y z.
Proof. exact (h1). Qed.
Lemma lem1581450 (x : real) (y : real) (z : real) (h1 : term561 x y z) : term498 x y z.
Proof. exact (proj2 (@lem1581449 x y z h1)). Qed.
Lemma lem1581454 (x : real) (y : real) (z : real) (h1 : term561 x y z) : term257 y z.
Proof. exact (proj2 (@lem1581450 x y z h1)). Qed.
Lemma lem1581457 (x : real) (y : real) (z : real) (h1 : term561 x y z) : term239.
Proof. exact (proj1 (@lem1581454 x y z h1)). Qed.
Lemma lem1581459 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581460 : term239 = term726.
Proof. exact (@lem1581459 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581461 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581462 : term239 = False.
Proof. exact (TRANS (@lem1581460) (@lem1581461)). Qed.
Lemma lem1581463 (x : real) (y : real) (z : real) (h1 : term561 x y z) : False.
Proof. exact (EQ_MP (@lem1581462) (@lem1581457 x y z h1)). Qed.
Lemma lem1581464 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term558 x y z.
Proof. exact (h1). Qed.
Lemma lem1581465 (y : real) (x : real) (z : real) (h1 : term554 y x z) : term554 y x z.
Proof. exact (h1). Qed.
Lemma lem1581466 (y : real) (x : real) (z : real) (h1 : term554 y x z) : term553 y x z.
Proof. exact (proj2 (@lem1581465 y x z h1)). Qed.
Lemma lem1581468 (y : real) (x : real) (z : real) (h1 : term554 y x z) : term494 y x z.
Proof. exact (proj2 (@lem1581466 y x z h1)). Qed.
Lemma lem1581471 (y : real) (x : real) (z : real) (h1 : term554 y x z) : term239.
Proof. exact (proj1 (@lem1581468 y x z h1)). Qed.
Lemma lem1581475 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581476 : term239 = term726.
Proof. exact (@lem1581475 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581477 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581478 : term239 = False.
Proof. exact (TRANS (@lem1581476) (@lem1581477)). Qed.
Lemma lem1581479 (y : real) (x : real) (z : real) (h1 : term554 y x z) : False.
Proof. exact (EQ_MP (@lem1581478) (@lem1581471 y x z h1)). Qed.
Lemma lem1581480 (x : real) (y : real) (z : real) (h1 : term556 x y z) : term556 x y z.
Proof. exact (h1). Qed.
Lemma lem1581481 (x : real) (y : real) (z : real) (h1 : term556 x y z) : term555 x y z.
Proof. exact (proj2 (@lem1581480 x y z h1)). Qed.
Lemma lem1581483 (x : real) (y : real) (z : real) (h1 : term556 x y z) : term469 x y z.
Proof. exact (proj2 (@lem1581481 x y z h1)). Qed.
Lemma lem1581485 (x : real) (y : real) (z : real) (h1 : term556 x y z) : term241 y z.
Proof. exact (proj2 (@lem1581483 x y z h1)). Qed.
Lemma lem1581487 (x : real) (y : real) (z : real) (h1 : term556 x y z) : term239.
Proof. exact (proj2 (@lem1581485 x y z h1)). Qed.
Lemma lem1581490 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581491 : term239 = term726.
Proof. exact (@lem1581490 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581492 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581493 : term239 = False.
Proof. exact (TRANS (@lem1581491) (@lem1581492)). Qed.
Lemma lem1581494 (x : real) (y : real) (z : real) (h1 : term556 x y z) : False.
Proof. exact (EQ_MP (@lem1581493) (@lem1581487 x y z h1)). Qed.
Lemma lem1581495 (x : real) (y : real) (z : real) (h1 : term558 x y z) : False.
Proof. exact (or_elim (@lem1581464 x y z h1) (fun h0 : term554 y x z => @lem1581479 y x z h0) (fun h0 : term556 x y z => @lem1581494 x y z h0)). Qed.
Lemma lem1581496 (x : real) (y : real) (z : real) (h1 : term563 x y z) : False.
Proof. exact (or_elim (@lem1581448 x y z h1) (fun h0 : term561 x y z => @lem1581463 x y z h0) (fun h0 : term558 x y z => @lem1581495 x y z h0)). Qed.
Lemma lem1581497 (y : real) (x : real) (z : real) (h1 : term576 y x z) : term576 y x z.
Proof. exact (h1). Qed.
Lemma lem1581498 (y : real) (x : real) (z : real) (h1 : term574 y x z) : term574 y x z.
Proof. exact (h1). Qed.
Lemma lem1581499 (y : real) (x : real) (z : real) (h1 : term574 y x z) : term564 y x z.
Proof. exact (proj2 (@lem1581498 y x z h1)). Qed.
Lemma lem1581503 (y : real) (x : real) (z : real) (h1 : term574 y x z) : term257 x z.
Proof. exact (proj2 (@lem1581499 y x z h1)). Qed.
Lemma lem1581506 (y : real) (x : real) (z : real) (h1 : term574 y x z) : term239.
Proof. exact (proj1 (@lem1581503 y x z h1)). Qed.
Lemma lem1581508 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581509 : term239 = term726.
Proof. exact (@lem1581508 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581510 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581511 : term239 = False.
Proof. exact (TRANS (@lem1581509) (@lem1581510)). Qed.
Lemma lem1581512 (y : real) (x : real) (z : real) (h1 : term574 y x z) : False.
Proof. exact (EQ_MP (@lem1581511) (@lem1581506 y x z h1)). Qed.
Lemma lem1581513 (y : real) (x : real) (z : real) (h1 : term573 y x z) : term573 y x z.
Proof. exact (h1). Qed.
Lemma lem1581514 (x : real) (y : real) (z : real) (h1 : term571 x y z) : term571 x y z.
Proof. exact (h1). Qed.
Lemma lem1581515 (x : real) (y : real) (z : real) (h1 : term571 x y z) : term570 x y z.
Proof. exact (proj2 (@lem1581514 x y z h1)). Qed.
Lemma lem1581517 (x : real) (y : real) (z : real) (h1 : term571 x y z) : term569 x y z.
Proof. exact (proj2 (@lem1581515 x y z h1)). Qed.
Lemma lem1581520 (x : real) (y : real) (z : real) (h1 : term571 x y z) : term239.
Proof. exact (proj1 (@lem1581517 x y z h1)). Qed.
Lemma lem1581524 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581525 : term239 = term726.
Proof. exact (@lem1581524 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581526 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581527 : term239 = False.
Proof. exact (TRANS (@lem1581525) (@lem1581526)). Qed.
Lemma lem1581528 (x : real) (y : real) (z : real) (h1 : term571 x y z) : False.
Proof. exact (EQ_MP (@lem1581527) (@lem1581520 x y z h1)). Qed.
Lemma lem1581529 (y : real) (x : real) (z : real) (h1 : term556 y x z) : term556 y x z.
Proof. exact (h1). Qed.
Lemma lem1581530 (y : real) (x : real) (z : real) (h1 : term556 y x z) : term555 y x z.
Proof. exact (proj2 (@lem1581529 y x z h1)). Qed.
Lemma lem1581532 (y : real) (x : real) (z : real) (h1 : term556 y x z) : term469 y x z.
Proof. exact (proj2 (@lem1581530 y x z h1)). Qed.
Lemma lem1581534 (y : real) (x : real) (z : real) (h1 : term556 y x z) : term241 x z.
Proof. exact (proj2 (@lem1581532 y x z h1)). Qed.
Lemma lem1581536 (y : real) (x : real) (z : real) (h1 : term556 y x z) : term239.
Proof. exact (proj2 (@lem1581534 y x z h1)). Qed.
Lemma lem1581539 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581540 : term239 = term726.
Proof. exact (@lem1581539 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581541 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581542 : term239 = False.
Proof. exact (TRANS (@lem1581540) (@lem1581541)). Qed.
Lemma lem1581543 (y : real) (x : real) (z : real) (h1 : term556 y x z) : False.
Proof. exact (EQ_MP (@lem1581542) (@lem1581536 y x z h1)). Qed.
Lemma lem1581544 (y : real) (x : real) (z : real) (h1 : term573 y x z) : False.
Proof. exact (or_elim (@lem1581513 y x z h1) (fun h0 : term571 x y z => @lem1581528 x y z h0) (fun h0 : term556 y x z => @lem1581543 y x z h0)). Qed.
Lemma lem1581545 (y : real) (x : real) (z : real) (h1 : term576 y x z) : False.
Proof. exact (or_elim (@lem1581497 y x z h1) (fun h0 : term574 y x z => @lem1581512 y x z h0) (fun h0 : term573 y x z => @lem1581544 y x z h0)). Qed.
Lemma lem1581546 (y : real) (x : real) (z : real) (h1 : term578 y x z) : False.
Proof. exact (or_elim (@lem1581447 y x z h1) (fun h0 : term563 x y z => @lem1581496 x y z h0) (fun h0 : term576 y x z => @lem1581545 y x z h0)). Qed.
Lemma lem1581547 (x : real) (y : real) (h1 : term718 x y) : term718 x y.
Proof. exact (h1). Qed.
Lemma lem1581548 (h1 : term610) : term610.
Proof. exact (h1). Qed.
Lemma lem1581549 (h1 : term584) : term584.
Proof. exact (h1). Qed.
Lemma lem1581550 (h1 : term584) : term239.
Proof. exact (proj2 (@lem1581549 h1)). Qed.
Lemma lem1581553 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581554 : term239 = term726.
Proof. exact (@lem1581553 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581555 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581556 : term239 = False.
Proof. exact (TRANS (@lem1581554) (@lem1581555)). Qed.
Lemma lem1581557 (h1 : term584) : False.
Proof. exact (EQ_MP (@lem1581556) (@lem1581550 h1)). Qed.
Lemma lem1581558 (h1 : term608) : term608.
Proof. exact (h1). Qed.
Lemma lem1581559 (h1 : term604) : term604.
Proof. exact (h1). Qed.
Lemma lem1581560 (h1 : term604) : term239.
Proof. exact (proj2 (@lem1581559 h1)). Qed.
Lemma lem1581563 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581564 : term239 = term726.
Proof. exact (@lem1581563 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581565 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581566 : term239 = False.
Proof. exact (TRANS (@lem1581564) (@lem1581565)). Qed.
Lemma lem1581567 (h1 : term604) : False.
Proof. exact (EQ_MP (@lem1581566) (@lem1581560 h1)). Qed.
Lemma lem1581568 (h1 : term584) : term584.
Proof. exact (h1). Qed.
Lemma lem1581569 (h1 : term584) : term239.
Proof. exact (proj2 (@lem1581568 h1)). Qed.
Lemma lem1581572 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581573 : term239 = term726.
Proof. exact (@lem1581572 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581574 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581575 : term239 = False.
Proof. exact (TRANS (@lem1581573) (@lem1581574)). Qed.
Lemma lem1581576 (h1 : term584) : False.
Proof. exact (EQ_MP (@lem1581575) (@lem1581569 h1)). Qed.
Lemma lem1581577 (h1 : term608) : False.
Proof. exact (or_elim (@lem1581558 h1) (fun h0 : term604 => @lem1581567 h0) (fun h0 : term584 => @lem1581576 h0)). Qed.
Lemma lem1581578 (h1 : term610) : False.
Proof. exact (or_elim (@lem1581548 h1) (fun h0 : term584 => @lem1581557 h0) (fun h0 : term608 => @lem1581577 h0)). Qed.
Lemma lem1581579 (x : real) (y : real) (h1 : term716 x y) : term716 x y.
Proof. exact (h1). Qed.
Lemma lem1581580 (x : real) (y : real) (h1 : term638 x y) : term638 x y.
Proof. exact (h1). Qed.
Lemma lem1581581 (x : real) (y : real) (h1 : term635 x y) : term635 x y.
Proof. exact (h1). Qed.
Lemma lem1581582 (x : real) (y : real) (h1 : term635 x y) : term584.
Proof. exact (proj2 (@lem1581581 x y h1)). Qed.
Lemma lem1581584 (x : real) (y : real) (h1 : term635 x y) : term239.
Proof. exact (proj2 (@lem1581582 x y h1)). Qed.
Lemma lem1581587 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581588 : term239 = term726.
Proof. exact (@lem1581587 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581589 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581590 : term239 = False.
Proof. exact (TRANS (@lem1581588) (@lem1581589)). Qed.
Lemma lem1581591 (x : real) (y : real) (h1 : term635 x y) : False.
Proof. exact (EQ_MP (@lem1581590) (@lem1581584 x y h1)). Qed.
Lemma lem1581592 (x : real) (y : real) (h1 : term636 x y) : term636 x y.
Proof. exact (h1). Qed.
Lemma lem1581593 (x : real) (y : real) (h1 : term636 x y) : term241 x y.
Proof. exact (proj2 (@lem1581592 x y h1)). Qed.
Lemma lem1581595 (x : real) (y : real) (h1 : term636 x y) : term239.
Proof. exact (proj2 (@lem1581593 x y h1)). Qed.
Lemma lem1581598 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581599 : term239 = term726.
Proof. exact (@lem1581598 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581600 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581601 : term239 = False.
Proof. exact (TRANS (@lem1581599) (@lem1581600)). Qed.
Lemma lem1581602 (x : real) (y : real) (h1 : term636 x y) : False.
Proof. exact (EQ_MP (@lem1581601) (@lem1581595 x y h1)). Qed.
Lemma lem1581603 (x : real) (y : real) (h1 : term638 x y) : False.
Proof. exact (or_elim (@lem1581580 x y h1) (fun h0 : term635 x y => @lem1581591 x y h0) (fun h0 : term636 x y => @lem1581602 x y h0)). Qed.
Lemma lem1581604 (x : real) (y : real) (h1 : term714 x y) : term714 x y.
Proof. exact (h1). Qed.
Lemma lem1581605 (x : real) (y : real) (h1 : term712 x y) : term712 x y.
Proof. exact (h1). Qed.
Lemma lem1581606 (x : real) (y : real) (h1 : term712 x y) : term257 x y.
Proof. exact (proj2 (@lem1581605 x y h1)). Qed.
Lemma lem1581611 (x : real) (y : real) (h1 : term712 x y) : term239.
Proof. exact (proj1 (@lem1581606 x y h1)). Qed.
Lemma lem1581613 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581614 : term239 = term726.
Proof. exact (@lem1581613 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581615 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581616 : term239 = False.
Proof. exact (TRANS (@lem1581614) (@lem1581615)). Qed.
Lemma lem1581617 (x : real) (y : real) (h1 : term712 x y) : False.
Proof. exact (EQ_MP (@lem1581616) (@lem1581611 x y h1)). Qed.
Lemma lem1581618 (x : real) (y : real) (h1 : term705 x y) : term705 x y.
Proof. exact (h1). Qed.
Lemma lem1581619 (x : real) (y : real) (h1 : term702 x y) : term702 x y.
Proof. exact (h1). Qed.
Lemma lem1581620 (x : real) (y : real) (h1 : term702 x y) : term701 x y.
Proof. exact (proj2 (@lem1581619 x y h1)). Qed.
Lemma lem1581622 (x : real) (y : real) (h1 : term702 x y) : term257 x y.
Proof. exact (proj2 (@lem1581620 x y h1)). Qed.
Lemma lem1581625 (x : real) (y : real) (h1 : term702 x y) : term239.
Proof. exact (proj1 (@lem1581622 x y h1)). Qed.
Lemma lem1581627 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581628 : term239 = term726.
Proof. exact (@lem1581627 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581629 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581630 : term239 = False.
Proof. exact (TRANS (@lem1581628) (@lem1581629)). Qed.
Lemma lem1581631 (x : real) (y : real) (h1 : term702 x y) : False.
Proof. exact (EQ_MP (@lem1581630) (@lem1581625 x y h1)). Qed.
Lemma lem1581632 (x : real) (y : real) (h1 : term703 x y) : term703 x y.
Proof. exact (h1). Qed.
Lemma lem1581633 (x : real) (y : real) (h1 : term703 x y) : term636 x y.
Proof. exact (proj2 (@lem1581632 x y h1)). Qed.
Lemma lem1581635 (x : real) (y : real) (h1 : term703 x y) : term241 x y.
Proof. exact (proj2 (@lem1581633 x y h1)). Qed.
Lemma lem1581637 (x : real) (y : real) (h1 : term703 x y) : term239.
Proof. exact (proj2 (@lem1581635 x y h1)). Qed.
Lemma lem1581640 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1581641 : term239 = term726.
Proof. exact (@lem1581640 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1581642 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1581643 : term239 = False.
Proof. exact (TRANS (@lem1581641) (@lem1581642)). Qed.
Lemma lem1581644 (x : real) (y : real) (h1 : term703 x y) : False.
Proof. exact (EQ_MP (@lem1581643) (@lem1581637 x y h1)). Qed.
Lemma lem1581645 (x : real) (y : real) (h1 : term705 x y) : False.
Proof. exact (or_elim (@lem1581618 x y h1) (fun h0 : term702 x y => @lem1581631 x y h0) (fun h0 : term703 x y => @lem1581644 x y h0)). Qed.
Lemma lem1581646 (x : real) (y : real) (h1 : term714 x y) : False.
Proof. exact (or_elim (@lem1581604 x y h1) (fun h0 : term712 x y => @lem1581617 x y h0) (fun h0 : term705 x y => @lem1581645 x y h0)). Qed.
Lemma lem1581647 (x : real) (y : real) (h1 : term716 x y) : False.
Proof. exact (or_elim (@lem1581579 x y h1) (fun h0 : term638 x y => @lem1581603 x y h0) (fun h0 : term714 x y => @lem1581646 x y h0)). Qed.
Lemma lem1581648 (x : real) (y : real) (h1 : term718 x y) : False.
Proof. exact (or_elim (@lem1581547 x y h1) (fun h0 : term610 => @lem1581578 h0) (fun h0 : term716 x y => @lem1581647 x y h0)). Qed.
Lemma lem1581649 (z : real) (x : real) (y : real) (h1 : term720 z x y) : False.
Proof. exact (or_elim (@lem1581446 z x y h1) (fun h0 : term578 y x z => @lem1581546 y x z h0) (fun h0 : term718 x y => @lem1581648 x y h0)). Qed.
Lemma lem1581650 (z : real) (x : real) (y : real) (h1 : term722 z x y) : False.
Proof. exact (or_elim (@lem1581345 z x y h1) (fun h0 : term506 x y z => @lem1581445 x y z h0) (fun h0 : term720 z x y => @lem1581649 z x y h0)). Qed.
Lemma lem1581651 (z : real) (x : real) (y : real) (h1 : term724 z x y) : False.
Proof. exact (or_elim (@lem1581294 z x y h1) (fun h0 : term273 x y => @lem1581344 x y h0) (fun h0 : term722 z x y => @lem1581650 z x y h0)). Qed.
Lemma lem1581652 (z : real) (x : real) (y : real) (h1 : term170 z x y) : term170 z x y.
Proof. exact (h1). Qed.
Lemma lem1581653 (z : real) (x : real) (y : real) (h1 : term170 z x y) : term724 z x y.
Proof. exact (EQ_MP (@lem1581293 z x y) (@lem1581652 z x y h1)). Qed.
Lemma lem1581654 (z : real) (x : real) (y : real) (h1 : term170 z x y) : (term724 z x y) = False.
Proof. exact (prop_ext (fun h2 : term724 z x y => @lem1581651 z x y h2) (fun h2 : False => @lem1581653 z x y h1)). Qed.
Lemma lem1581655 (z : real) (x : real) (y : real) (h1 : term170 z x y) : False.
Proof. exact (EQ_MP (@lem1581654 z x y h1) (@lem1581653 z x y h1)). Qed.
Lemma lem1581656 (z : real) (x : real) (y : real) (h1 : term18 z x y) : term18 z x y.
Proof. exact (h1). Qed.
Lemma lem1581657 (z : real) (x : real) (y : real) (h1 : term18 z x y) : term170 z x y.
Proof. exact (EQ_MP (@lem1578719 z x y) (@lem1581656 z x y h1)). Qed.
Lemma lem1581658 (z : real) (x : real) (y : real) (h1 : term18 z x y) : (term170 z x y) = False.
Proof. exact (prop_ext (fun h2 : term170 z x y => @lem1581655 z x y h2) (fun h2 : False => @lem1581657 z x y h1)). Qed.
Lemma lem1581659 (z : real) (x : real) (y : real) (h1 : term18 z x y) : False.
Proof. exact (EQ_MP (@lem1581658 z x y h1) (@lem1581657 z x y h1)). Qed.
Lemma lem1581660 (z : real) (x : real) (y : real) : term727 z x y.
Proof. exact (fun h0 : term18 z x y => @lem1581659 z x y h0). Qed.
Lemma lem1581661 (z : real) (x : real) (y : real) : term728 z x y.
Proof. exact (@lem1386578 (term729 z x y)). Qed.
Lemma lem1581662 (z : real) (x : real) (y : real) : term729 z x y.
Proof. exact (@lem1581661 z x y (@lem1581660 z x y)). Qed.
