Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_RMUL_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1491431 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491432 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1491431 (term4 x)). Qed.
Lemma lem1491433 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1491434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491436 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1491434) (@lem1491433 x y)). Qed.
Lemma lem1491437 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1491436 x y)). Qed.
Lemma lem1491438 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491439 (x : real) : (term3 x) = (term12 x).
Proof. exact (MK_COMB (@lem1491438) (@lem1491437 x)). Qed.
Lemma lem1491440 (x : real) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem1491432 x) (@lem1491439 x)). Qed.
Lemma lem1491441 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491442 : term13 = term14.
Proof. exact (@lem1491441 term15). Qed.
Lemma lem1491443 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1491444 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491445 (x : real) : (term18 x) = (term2 x).
Proof. exact (MK_COMB (@lem1491444) (@lem1491443 x)). Qed.
Lemma lem1491446 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1491445 x) (@lem1491440 x)). Qed.
Lemma lem1491447 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1491446 x)). Qed.
Lemma lem1491448 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491449 : term14 = term21.
Proof. exact (MK_COMB (@lem1491448) (@lem1491447)). Qed.
Lemma lem1491451 : term13 = term21.
Proof. exact (TRANS (@lem1491442) (@lem1491449)). Qed.
Lemma lem1491454 (x : real) (y : real) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1491455 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1491454 x y)). Qed.
Lemma lem1491456 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491457 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1491456) (@lem1491455 x)). Qed.
Lemma lem1491458 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1491457 x)). Qed.
Lemma lem1491459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491460 : term21 = term21.
Proof. exact (MK_COMB (@lem1491459) (@lem1491458)). Qed.
Lemma lem1491461 : term13 = term21.
Proof. exact (TRANS (@lem1491451) (@lem1491460)). Qed.
Lemma lem1491462 (x : real) (y : real) : (term9 x y) = (term22 x y).
Proof. exact (@lem1483554 (term6 x y) (term7 x y)). Qed.
Lemma lem1491469 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1491472 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1491473 (x : real) (y : real) : (term7 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1491472 x) (@lem1491469 y)). Qed.
Lemma lem1491478 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483478 term26 x y). Qed.
Lemma lem1491479 (x : real) (y : real) : (term7 x y) = (term25 x y).
Proof. exact (TRANS (@lem1491473 x y) (@lem1491478 x y)). Qed.
Lemma lem1491492 (x : real) (y : real) : (term6 x y) = (term25 x y).
Proof. exact (@lem1483512 (real_mul x y)). Qed.
Lemma lem1491493 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1491494 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1491493) (@lem1491492 x y)). Qed.
Lemma lem1491495 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1491494 x y) (@lem1491479 x y)). Qed.
Lemma lem1491496 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483519 (term25 x y) (term25 x y)). Qed.
Lemma lem1491497 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1483476 term26 term26 (real_mul x y)). Qed.
Lemma lem1491499 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1491500 : term36 = term37.
Proof. exact (@lem1491499 term38 term38). Qed.
Lemma lem1491501 : (term39 = (BIT1 0)) = (term40 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1491502 : term40 = term38.
Proof. exact (EQ_MP (@lem1491501) (@lem940073)). Qed.
Lemma lem1491503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1491504 : term37 = term41.
Proof. exact (MK_COMB (@lem1491503) (@lem1491502)). Qed.
Lemma lem1491505 : term36 = term41.
Proof. exact (TRANS (@lem1491500) (@lem1491504)). Qed.
Lemma lem1491506 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491507 : term42 = term43.
Proof. exact (MK_COMB (@lem1491506) (@lem1491505)). Qed.
Lemma lem1491508 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491509 (x : real) (y : real) : (term33 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1491507) (@lem1491508 x y)). Qed.
Lemma lem1491510 (x : real) (y : real) : (term32 x y) = (term44 x y).
Proof. exact (TRANS (@lem1491497 x y) (@lem1491509 x y)). Qed.
Lemma lem1491511 (x : real) (y : real) : (term44 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1491512 (x : real) (y : real) : (term32 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1491510 x y) (@lem1491511 x y)). Qed.
Lemma lem1491513 (x : real) (y : real) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1491514 (x : real) (y : real) : (term31 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1491513 x y) (@lem1491512 x y)). Qed.
Lemma lem1491515 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem1483440 term26 (real_mul x y)). Qed.
Lemma lem1491517 (m : nat) : (term48 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491518 : term50 = term49.
Proof. exact (@lem1491517 term38). Qed.
Lemma lem1491519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491520 : term51 = term52.
Proof. exact (MK_COMB (@lem1491519) (@lem1491518)). Qed.
Lemma lem1491521 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491522 (x : real) (y : real) : (term47 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1491520) (@lem1491521 x y)). Qed.
Lemma lem1491523 (x : real) (y : real) : (term46 x y) = (term53 x y).
Proof. exact (TRANS (@lem1491515 x y) (@lem1491522 x y)). Qed.
Lemma lem1491524 (x : real) (y : real) : (term53 x y) = term49.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1491525 (x : real) (y : real) : (term46 x y) = term49.
Proof. exact (TRANS (@lem1491523 x y) (@lem1491524 x y)). Qed.
Lemma lem1491526 (x : real) (y : real) : (term31 x y) = term49.
Proof. exact (TRANS (@lem1491514 x y) (@lem1491525 x y)). Qed.
Lemma lem1491527 (x : real) (y : real) : (term30 x y) = term49.
Proof. exact (TRANS (@lem1491496 x y) (@lem1491526 x y)). Qed.
Lemma lem1491528 (x : real) (y : real) : (term29 x y) = term49.
Proof. exact (TRANS (@lem1491495 x y) (@lem1491527 x y)). Qed.
Lemma lem1491529 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1491530 (x : real) (y : real) : (term54 x y) = term55.
Proof. exact (MK_COMB (@lem1491529) (@lem1491528 x y)). Qed.
Lemma lem1491531 : term55 = term56.
Proof. exact (@lem1483512 term49). Qed.
Lemma lem1491533 (x : nat) : (term57 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1491534 : term56 = term49.
Proof. exact (@lem1491533 term38). Qed.
Lemma lem1491535 : term55 = term49.
Proof. exact (TRANS (@lem1491531) (@lem1491534)). Qed.
Lemma lem1491536 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1491537 (x : real) (y : real) : ((term54 x y) = term55) = ((term54 x y) = term49).
Proof. exact (MK_COMB (@lem1491536 x y) (@lem1491535)). Qed.
Lemma lem1491538 (x : real) (y : real) : (term54 x y) = term49.
Proof. exact (EQ_MP (@lem1491537 x y) (@lem1491530 x y)). Qed.
Lemma lem1491539 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491540 (x : real) (y : real) : (term59 x y) = term60.
Proof. exact (MK_COMB (@lem1491539) (@lem1491538 x y)). Qed.
Lemma lem1491541 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1491542 (x : real) (y : real) : (term61 x y) = term62.
Proof. exact (MK_COMB (@lem1491540 x y) (@lem1491541)). Qed.
Lemma lem1491543 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491544 (x : real) (y : real) : (term63 x y) = term60.
Proof. exact (MK_COMB (@lem1491543) (@lem1491528 x y)). Qed.
Lemma lem1491545 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1491546 (x : real) (y : real) : (term64 x y) = term62.
Proof. exact (MK_COMB (@lem1491544 x y) (@lem1491545)). Qed.
Lemma lem1491547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491548 (x : real) (y : real) : (term65 x y) = term66.
Proof. exact (MK_COMB (@lem1491547) (@lem1491546 x y)). Qed.
Lemma lem1491549 (x : real) (y : real) : (term22 x y) = term67.
Proof. exact (MK_COMB (@lem1491548 x y) (@lem1491542 x y)). Qed.
Lemma lem1491550 (x : real) (y : real) : (term9 x y) = term67.
Proof. exact (TRANS (@lem1491462 x y) (@lem1491549 x y)). Qed.
Lemma lem1491551 (x : real) : (term11 x) = term68.
Proof. exact (fun_ext (fun y : real => @lem1491550 x y)). Qed.
Lemma lem1491552 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491553 (x : real) : (term12 x) = term69.
Proof. exact (MK_COMB (@lem1491552) (@lem1491551 x)). Qed.
Lemma lem1491554 : term20 = term70.
Proof. exact (fun_ext (fun x : real => @lem1491553 x)). Qed.
Lemma lem1491555 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491556 : term21 = term71.
Proof. exact (MK_COMB (@lem1491555) (@lem1491554)). Qed.
Lemma lem1491557 : term13 = term71.
Proof. exact (TRANS (@lem1491461) (@lem1491556)). Qed.
Lemma lem1491559 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491560 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1491559 real t). Qed.
Lemma lem1491561 : term71 = term69.
Proof. exact (@lem1491560 term69). Qed.
Lemma lem1491563 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1491564 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1491563 real P Q). Qed.
Lemma lem1491565 : term78 = term79.
Proof. exact (@lem1491564 term80 term80). Qed.
Lemma lem1491566 (y : real) : (term81 y) = term62.
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1491567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491568 (y : real) : (term82 y) = term66.
Proof. exact (MK_COMB (@lem1491567) (@lem1491566 y)). Qed.
Lemma lem1491569 (y : real) : (term81 y) = term62.
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1491570 (y : real) : (term83 y) = term67.
Proof. exact (MK_COMB (@lem1491568 y) (@lem1491569 y)). Qed.
Lemma lem1491571 : term84 = term68.
Proof. exact (fun_ext (fun y : real => @lem1491570 y)). Qed.
Lemma lem1491572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491573 : term78 = term69.
Proof. exact (MK_COMB (@lem1491572) (@lem1491571)). Qed.
Lemma lem1491574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1491575 : term85 = term86.
Proof. exact (MK_COMB (@lem1491574) (@lem1491573)). Qed.
Lemma lem1491576 (y : real) : (term81 y) = term62.
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1491577 : term87 = term80.
Proof. exact (fun_ext (fun y : real => @lem1491576 y)). Qed.
Lemma lem1491578 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491579 : term88 = term89.
Proof. exact (MK_COMB (@lem1491578) (@lem1491577)). Qed.
Lemma lem1491580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491581 : term90 = term91.
Proof. exact (MK_COMB (@lem1491580) (@lem1491579)). Qed.
Lemma lem1491582 (y : real) : (term81 y) = term62.
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1491583 : term87 = term80.
Proof. exact (fun_ext (fun y : real => @lem1491582 y)). Qed.
Lemma lem1491584 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491585 : term88 = term89.
Proof. exact (MK_COMB (@lem1491584) (@lem1491583)). Qed.
Lemma lem1491586 : term79 = term92.
Proof. exact (MK_COMB (@lem1491581) (@lem1491585)). Qed.
Lemma lem1491587 : (term78 = term79) = (term69 = term92).
Proof. exact (MK_COMB (@lem1491575) (@lem1491586)). Qed.
Lemma lem1491588 : term69 = term92.
Proof. exact (EQ_MP (@lem1491587) (@lem1491565)). Qed.
Lemma lem1491589 : term71 = term92.
Proof. exact (TRANS (@lem1491561) (@lem1491588)). Qed.
Lemma lem1491591 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491592 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1491591 real t). Qed.
Lemma lem1491593 : term89 = term62.
Proof. exact (@lem1491592 term62). Qed.
Lemma lem1491594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491595 : term91 = term66.
Proof. exact (MK_COMB (@lem1491594) (@lem1491593)). Qed.
Lemma lem1491597 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491598 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1491597 real t). Qed.
Lemma lem1491599 : term89 = term62.
Proof. exact (@lem1491598 term62). Qed.
Lemma lem1491600 : term92 = term67.
Proof. exact (MK_COMB (@lem1491595) (@lem1491599)). Qed.
Lemma lem1491603 : term71 = term67.
Proof. exact (TRANS (@lem1491589) (@lem1491600)). Qed.
Lemma lem1491612 : term13 = term67.
Proof. exact (TRANS (@lem1491557) (@lem1491603)). Qed.
Lemma lem1491622 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1491623 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1491625 (n : nat) (m : nat) : (term93 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491626 : term62 = term94.
Proof. exact (@lem1491625 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491627 : term94 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491628 : term62 = False.
Proof. exact (TRANS (@lem1491626) (@lem1491627)). Qed.
Lemma lem1491629 (h1 : term62) : False.
Proof. exact (EQ_MP (@lem1491628) (@lem1491623 h1)). Qed.
Lemma lem1491630 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1491632 (n : nat) (m : nat) : (term93 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491633 : term62 = term94.
Proof. exact (@lem1491632 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491634 : term94 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491635 : term62 = False.
Proof. exact (TRANS (@lem1491633) (@lem1491634)). Qed.
Lemma lem1491636 (h1 : term62) : False.
Proof. exact (EQ_MP (@lem1491635) (@lem1491630 h1)). Qed.
Lemma lem1491637 (h1 : term67) : False.
Proof. exact (or_elim (@lem1491622 h1) (fun h0 : term62 => @lem1491629 h0) (fun h0 : term62 => @lem1491636 h0)). Qed.
Lemma lem1491639 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1491640 (h1 : term67) : term67 = False.
Proof. exact (prop_ext (fun h2 : term67 => @lem1491637 h1) (fun h2 : False => @lem1491639 h1)). Qed.
Lemma lem1491641 (h1 : term67) : False.
Proof. exact (EQ_MP (@lem1491640 h1) (@lem1491639 h1)). Qed.
Lemma lem1491642 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1491643 (h1 : term13) : term67.
Proof. exact (EQ_MP (@lem1491612) (@lem1491642 h1)). Qed.
Lemma lem1491644 (h1 : term13) : term67 = False.
Proof. exact (prop_ext (fun h2 : term67 => @lem1491641 h2) (fun h2 : False => @lem1491643 h1)). Qed.
Lemma lem1491645 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1491644 h1) (@lem1491643 h1)). Qed.
Lemma lem1491646 : term95.
Proof. exact (fun h0 : term13 => @lem1491645 h0). Qed.
Lemma lem1491647 : term96.
Proof. exact (@lem1386578 term97). Qed.
Lemma lem1491648 : term97.
Proof. exact (@lem1491647 (@lem1491646)). Qed.
