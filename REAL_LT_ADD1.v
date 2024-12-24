Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADD1_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483486_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483578_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1504341 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17362 (real_le x y) (term2 x y)). Qed.
Lemma lem1504342 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504343 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1504342 (term7 x)). Qed.
Lemma lem1504344 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1504345 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504346 (x : real) (y : real) : (term10 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1504345) (@lem1504344 x y)). Qed.
Lemma lem1504347 (x : real) (y : real) : (term10 x y) = (term1 x y).
Proof. exact (TRANS (@lem1504346 x y) (@lem1504341 x y)). Qed.
Lemma lem1504348 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1504347 x y)). Qed.
Lemma lem1504349 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504350 (x : real) : (term6 x) = (term13 x).
Proof. exact (MK_COMB (@lem1504349) (@lem1504348 x)). Qed.
Lemma lem1504351 (x : real) : (term5 x) = (term13 x).
Proof. exact (TRANS (@lem1504343 x) (@lem1504350 x)). Qed.
Lemma lem1504352 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504353 : term14 = term15.
Proof. exact (@lem1504352 term16). Qed.
Lemma lem1504354 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1504355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504356 (x : real) : (term19 x) = (term5 x).
Proof. exact (MK_COMB (@lem1504355) (@lem1504354 x)). Qed.
Lemma lem1504357 (x : real) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem1504356 x) (@lem1504351 x)). Qed.
Lemma lem1504358 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1504357 x)). Qed.
Lemma lem1504359 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504360 : term15 = term22.
Proof. exact (MK_COMB (@lem1504359) (@lem1504358)). Qed.
Lemma lem1504362 : term14 = term22.
Proof. exact (TRANS (@lem1504353) (@lem1504360)). Qed.
Lemma lem1504369 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1504370 (x : real) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1504369 x y)). Qed.
Lemma lem1504371 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504372 (x : real) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem1504371) (@lem1504370 x)). Qed.
Lemma lem1504373 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1504372 x)). Qed.
Lemma lem1504374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504375 : term22 = term22.
Proof. exact (MK_COMB (@lem1504374) (@lem1504373)). Qed.
Lemma lem1504376 : term14 = term22.
Proof. exact (TRANS (@lem1504362) (@lem1504375)). Qed.
Lemma lem1504377 (y : real) (x : real) : (real_le x y) = (term23 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1504383 (y : real) (x : real) : (real_sub y x) = (term24 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1504388 (x : real) (y : real) : (term24 y x) = (term25 x y).
Proof. exact (@lem1483488 (term26 x) y). Qed.
Lemma lem1504390 (x : real) (y : real) : (real_sub y x) = (term25 x y).
Proof. exact (TRANS (@lem1504383 y x) (@lem1504388 x y)). Qed.
Lemma lem1504391 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504392 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (MK_COMB (@lem1504391) (@lem1504390 x y)). Qed.
Lemma lem1504393 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1504394 (x : real) (y : real) : (term23 y x) = (term30 x y).
Proof. exact (MK_COMB (@lem1504392 x y) (@lem1504393)). Qed.
Lemma lem1504395 (x : real) (y : real) : (real_le x y) = (term30 x y).
Proof. exact (TRANS (@lem1504377 y x) (@lem1504394 x y)). Qed.
Lemma lem1504396 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (@lem1483531 x (term33 y)). Qed.
Lemma lem1504408 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483519 x (term33 y)). Qed.
Lemma lem1504409 (y : real) : (term36 y) = (term37 y).
Proof. exact (@lem1483508 y term38 term39). Qed.
Lemma lem1504411 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1504412 : term42 = term43.
Proof. exact (@lem1504411 term44 term44). Qed.
Lemma lem1504413 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1504414 : term46 = term44.
Proof. exact (EQ_MP (@lem1504413) (@lem940073)). Qed.
Lemma lem1504415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1504416 : term47 = term39.
Proof. exact (MK_COMB (@lem1504415) (@lem1504414)). Qed.
Lemma lem1504417 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1504418 : term43 = term38.
Proof. exact (MK_COMB (@lem1504417) (@lem1504416)). Qed.
Lemma lem1504419 : term42 = term38.
Proof. exact (TRANS (@lem1504412) (@lem1504418)). Qed.
Lemma lem1504422 (y : real) : (term48 y) = (term48 y).
Proof. exact (eq_refl (term48 y)). Qed.
Lemma lem1504423 (y : real) : (term37 y) = (term49 y).
Proof. exact (MK_COMB (@lem1504422 y) (@lem1504419)). Qed.
Lemma lem1504424 (y : real) : (term36 y) = (term49 y).
Proof. exact (TRANS (@lem1504409 y) (@lem1504423 y)). Qed.
Lemma lem1504425 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1504428 (x : real) (y : real) : (term35 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1504425 x) (@lem1504424 y)). Qed.
Lemma lem1504430 (x : real) (y : real) : (term34 x y) = (term50 x y).
Proof. exact (TRANS (@lem1504408 x y) (@lem1504428 x y)). Qed.
Lemma lem1504431 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504432 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1504431) (@lem1504430 x y)). Qed.
Lemma lem1504433 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1504434 (x : real) (y : real) : (term32 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1504432 x y) (@lem1504433)). Qed.
Lemma lem1504435 (x : real) (y : real) : (term31 x y) = (term53 x y).
Proof. exact (TRANS (@lem1504396 x y) (@lem1504434 x y)). Qed.
Lemma lem1504436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1504437 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1504436) (@lem1504395 x y)). Qed.
Lemma lem1504438 (x : real) (y : real) : (term1 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1504437 x y) (@lem1504435 x y)). Qed.
Lemma lem1504439 (x : real) : (term12 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1504438 x y)). Qed.
Lemma lem1504440 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504441 (x : real) : (term13 x) = (term58 x).
Proof. exact (MK_COMB (@lem1504440) (@lem1504439 x)). Qed.
Lemma lem1504442 : term21 = term59.
Proof. exact (fun_ext (fun x : real => @lem1504441 x)). Qed.
Lemma lem1504443 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504444 : term22 = term60.
Proof. exact (MK_COMB (@lem1504443) (@lem1504442)). Qed.
Lemma lem1504503 : term14 = term60.
Proof. exact (TRANS (@lem1504376) (@lem1504444)). Qed.
Lemma lem1504510 (x : real) (y : real) : (term56 x y) = (term56 x y).
Proof. exact (eq_refl (term56 x y)). Qed.
Lemma lem1504511 (x : real) : (term57 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1504510 x y)). Qed.
Lemma lem1504512 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504513 (x : real) : (term58 x) = (term58 x).
Proof. exact (MK_COMB (@lem1504512) (@lem1504511 x)). Qed.
Lemma lem1504514 : term59 = term59.
Proof. exact (fun_ext (fun x : real => @lem1504513 x)). Qed.
Lemma lem1504515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504516 : term60 = term60.
Proof. exact (MK_COMB (@lem1504515) (@lem1504514)). Qed.
Lemma lem1504517 : term14 = term60.
Proof. exact (TRANS (@lem1504503) (@lem1504516)). Qed.
Lemma lem1504521 (x : real) (y : real) (h1 : term56 x y) : term56 x y.
Proof. exact (h1). Qed.
Lemma lem1504522 (x : real) (y : real) (h1 : term56 x y) : term53 x y.
Proof. exact (proj2 (@lem1504521 x y h1)). Qed.
Lemma lem1504523 (x : real) (y : real) (h1 : term56 x y) : term30 x y.
Proof. exact (proj1 (@lem1504521 x y h1)). Qed.
Lemma lem1504525 (n : nat) (m : nat) : (term61 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504526 : term62 = term63.
Proof. exact (@lem1504525 (NUMERAL 0) term44). Qed.
Lemma lem1504527 : term64 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504528 (h1 : term64 = (BIT1 0)) : term63 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504529 : (term64 = (BIT1 0)) = (term63 = True).
Proof. exact (prop_ext (fun h1 : term64 = (BIT1 0) => @lem1504528 h1) (fun h1 : term63 = True => @lem1504527)). Qed.
Lemma lem1504530 : term63 = True.
Proof. exact (EQ_MP (@lem1504529) (@lem1504527)). Qed.
Lemma lem1504531 : term62 = True.
Proof. exact (TRANS (@lem1504526) (@lem1504530)). Qed.
Lemma lem1504532 : True = term62.
Proof. exact (SYM (@lem1504531)). Qed.
Lemma lem1504533 : term62.
Proof. exact (EQ_MP (@lem1504532) (@lem0)). Qed.
Lemma lem1504534 (x : real) (y : real) (h1 : term56 x y) : term65 x y.
Proof. exact (conj (@lem1504533) (@lem1504523 x y h1)). Qed.
Lemma lem1504536 (x : real) (y : real) : term66 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1504537 (x : real) (y : real) : term67 x y.
Proof. exact (@lem1504536 term39 (term25 x y)). Qed.
Lemma lem1504538 (x : real) (y : real) (h1 : term56 x y) : term68 x y.
Proof. exact (@lem1504537 x y (@lem1504534 x y h1)). Qed.
Lemma lem1504539 (x : real) (y : real) : (term69 x y) = (term25 x y).
Proof. exact (@lem1483460 (term25 x y)). Qed.
Lemma lem1504540 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504541 (x : real) (y : real) : (term70 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1504540) (@lem1504539 x y)). Qed.
Lemma lem1504542 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1504543 (x : real) (y : real) : (term68 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1504541 x y) (@lem1504542)). Qed.
Lemma lem1504544 (x : real) (y : real) (h1 : term56 x y) : term30 x y.
Proof. exact (EQ_MP (@lem1504543 x y) (@lem1504538 x y h1)). Qed.
Lemma lem1504546 (n : nat) (m : nat) : (term61 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1504547 : term62 = term63.
Proof. exact (@lem1504546 (NUMERAL 0) term44). Qed.
Lemma lem1504548 : term64 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504549 (h1 : term64 = (BIT1 0)) : term63 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1504550 : (term64 = (BIT1 0)) = (term63 = True).
Proof. exact (prop_ext (fun h1 : term64 = (BIT1 0) => @lem1504549 h1) (fun h1 : term63 = True => @lem1504548)). Qed.
Lemma lem1504551 : term63 = True.
Proof. exact (EQ_MP (@lem1504550) (@lem1504548)). Qed.
Lemma lem1504552 : term62 = True.
Proof. exact (TRANS (@lem1504547) (@lem1504551)). Qed.
Lemma lem1504553 : True = term62.
Proof. exact (SYM (@lem1504552)). Qed.
Lemma lem1504554 : term62.
Proof. exact (EQ_MP (@lem1504553) (@lem0)). Qed.
Lemma lem1504555 (x : real) (y : real) (h1 : term56 x y) : term71 x y.
Proof. exact (conj (@lem1504554) (@lem1504522 x y h1)). Qed.
Lemma lem1504557 (x : real) (y : real) : term66 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1504558 (x : real) (y : real) : term72 x y.
Proof. exact (@lem1504557 term39 (term50 x y)). Qed.
Lemma lem1504559 (x : real) (y : real) (h1 : term56 x y) : term73 x y.
Proof. exact (@lem1504558 x y (@lem1504555 x y h1)). Qed.
Lemma lem1504560 (x : real) (y : real) : (term74 x y) = (term50 x y).
Proof. exact (@lem1483460 (term50 x y)). Qed.
Lemma lem1504561 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504562 (x : real) (y : real) : (term75 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1504561) (@lem1504560 x y)). Qed.
Lemma lem1504563 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1504564 (x : real) (y : real) : (term73 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1504562 x y) (@lem1504563)). Qed.
Lemma lem1504565 (x : real) (y : real) (h1 : term56 x y) : term53 x y.
Proof. exact (EQ_MP (@lem1504564 x y) (@lem1504559 x y h1)). Qed.
Lemma lem1504566 (x : real) (y : real) (h1 : term56 x y) : term76 x y.
Proof. exact (conj (@lem1504565 x y h1) (@lem1504544 x y h1)). Qed.
Lemma lem1504568 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483578 x y)). Qed.
Lemma lem1504569 (x : real) (y : real) : term78 x y.
Proof. exact (@lem1504568 (term50 x y) (term25 x y)). Qed.
Lemma lem1504570 (x : real) (y : real) (h1 : term56 x y) : term79 x y.
Proof. exact (@lem1504569 x y (@lem1504566 x y h1)). Qed.
Lemma lem1504571 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483480 x (term26 x) (term49 y) y). Qed.
Lemma lem1504572 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem1483442 term38 x). Qed.
Lemma lem1504574 (m : nat) : (term84 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504575 : term85 = term29.
Proof. exact (@lem1504574 term44). Qed.
Lemma lem1504576 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504577 : term86 = term87.
Proof. exact (MK_COMB (@lem1504576) (@lem1504575)). Qed.
Lemma lem1504578 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504579 (x : real) : (term83 x) = (term88 x).
Proof. exact (MK_COMB (@lem1504577) (@lem1504578 x)). Qed.
Lemma lem1504580 (x : real) : (term82 x) = (term88 x).
Proof. exact (TRANS (@lem1504572 x) (@lem1504579 x)). Qed.
Lemma lem1504581 (x : real) : (term88 x) = term29.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1504582 (x : real) : (term82 x) = term29.
Proof. exact (TRANS (@lem1504580 x) (@lem1504581 x)). Qed.
Lemma lem1504583 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504584 (x : real) : (term89 x) = term90.
Proof. exact (MK_COMB (@lem1504583) (@lem1504582 x)). Qed.
Lemma lem1504585 (y : real) : (term91 y) = (term92 y).
Proof. exact (@lem1483486 (term26 y) y term38). Qed.
Lemma lem1504586 (y : real) : (term93 y) = (term83 y).
Proof. exact (@lem1483440 term38 y). Qed.
Lemma lem1504588 (m : nat) : (term84 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504589 : term85 = term29.
Proof. exact (@lem1504588 term44). Qed.
Lemma lem1504590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504591 : term86 = term87.
Proof. exact (MK_COMB (@lem1504590) (@lem1504589)). Qed.
Lemma lem1504592 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504593 (y : real) : (term83 y) = (term88 y).
Proof. exact (MK_COMB (@lem1504591) (@lem1504592 y)). Qed.
Lemma lem1504594 (y : real) : (term93 y) = (term88 y).
Proof. exact (TRANS (@lem1504586 y) (@lem1504593 y)). Qed.
Lemma lem1504595 (y : real) : (term88 y) = term29.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1504596 (y : real) : (term93 y) = term29.
Proof. exact (TRANS (@lem1504594 y) (@lem1504595 y)). Qed.
Lemma lem1504597 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1504598 (y : real) : (term94 y) = term90.
Proof. exact (MK_COMB (@lem1504597) (@lem1504596 y)). Qed.
Lemma lem1504599 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1504600 (y : real) : (term92 y) = term95.
Proof. exact (MK_COMB (@lem1504598 y) (@lem1504599)). Qed.
Lemma lem1504601 (y : real) : (term91 y) = term95.
Proof. exact (TRANS (@lem1504585 y) (@lem1504600 y)). Qed.
Lemma lem1504602 : term95 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1504603 (y : real) : (term91 y) = term38.
Proof. exact (TRANS (@lem1504601 y) (@lem1504602)). Qed.
Lemma lem1504604 (x : real) (y : real) : (term81 x y) = term95.
Proof. exact (MK_COMB (@lem1504584 x) (@lem1504603 y)). Qed.
Lemma lem1504605 (x : real) (y : real) : (term80 x y) = term95.
Proof. exact (TRANS (@lem1504571 x y) (@lem1504604 x y)). Qed.
Lemma lem1504606 : term95 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1504607 (x : real) (y : real) : (term80 x y) = term38.
Proof. exact (TRANS (@lem1504605 x y) (@lem1504606)). Qed.
Lemma lem1504608 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1504609 (x : real) (y : real) : (term96 x y) = term97.
Proof. exact (MK_COMB (@lem1504608) (@lem1504607 x y)). Qed.
Lemma lem1504610 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1504611 (x : real) (y : real) : (term79 x y) = term98.
Proof. exact (MK_COMB (@lem1504609 x y) (@lem1504610)). Qed.
Lemma lem1504612 (x : real) (y : real) (h1 : term56 x y) : term98.
Proof. exact (EQ_MP (@lem1504611 x y) (@lem1504570 x y h1)). Qed.
Lemma lem1504614 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1504615 : term98 = term101.
Proof. exact (@lem1504614 term44 (NUMERAL 0)). Qed.
Lemma lem1504616 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1504617 : term64 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1504618 (h1 : term64 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1504619 : (term64 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term64 = (BIT1 0) => @lem1504618 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem1504617)). Qed.
Lemma lem1504620 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1504619) (@lem1504617)). Qed.
Lemma lem1504621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1504622 : term102 = (and False).
Proof. exact (MK_COMB (@lem1504621) (@lem1504620)). Qed.
Lemma lem1504623 : term101 = (False /\ True).
Proof. exact (MK_COMB (@lem1504622) (@lem1504616)). Qed.
Lemma lem1504625 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1504626 : term101 = False.
Proof. exact (TRANS (@lem1504623) (@lem1504625)). Qed.
Lemma lem1504627 : term98 = False.
Proof. exact (TRANS (@lem1504615) (@lem1504626)). Qed.
Lemma lem1504628 (x : real) (y : real) (h1 : term56 x y) : False.
Proof. exact (EQ_MP (@lem1504627) (@lem1504612 x y h1)). Qed.
Lemma lem1504630 (x : real) (y : real) (h1 : term56 x y) : term56 x y.
Proof. exact (h1). Qed.
Lemma lem1504631 (x : real) (y : real) (h1 : term56 x y) : (term56 x y) = False.
Proof. exact (prop_ext (fun h2 : term56 x y => @lem1504628 x y h1) (fun h2 : False => @lem1504630 x y h1)). Qed.
Lemma lem1504632 (x : real) (y : real) (h1 : term56 x y) : False.
Proof. exact (EQ_MP (@lem1504631 x y h1) (@lem1504630 x y h1)). Qed.
Lemma lem1504633 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1504634 (x : real) (h1 : term58 x) : False.
Proof. exact (ex_elim (@lem1504633 x h1) (fun y : real => fun h0 : term57 x y => @lem1504632 x y h0)). Qed.
Lemma lem1504635 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem1504636 (h1 : term60) : False.
Proof. exact (ex_elim (@lem1504635 h1) (fun x : real => fun h0 : term59 x => @lem1504634 x h0)). Qed.
Lemma lem1504637 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1504638 (h1 : term14) : term60.
Proof. exact (EQ_MP (@lem1504517) (@lem1504637 h1)). Qed.
Lemma lem1504639 (h1 : term14) : term60 = False.
Proof. exact (prop_ext (fun h2 : term60 => @lem1504636 h2) (fun h2 : False => @lem1504638 h1)). Qed.
Lemma lem1504640 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1504639 h1) (@lem1504638 h1)). Qed.
Lemma lem1504641 : term103.
Proof. exact (fun h0 : term14 => @lem1504640 h0). Qed.
Lemma lem1504642 : term104.
Proof. exact (@lem1386578 term105). Qed.
Lemma lem1504643 : term105.
Proof. exact (@lem1504642 (@lem1504641)). Qed.
