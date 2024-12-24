Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LET_TRANS_term_abbrevs.
Require Import LE_SUC_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem94410 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem94411 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem94412 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem94411 n) (@lem94410 n)). Qed.
Lemma lem94413 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem94416 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem94417 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem94416 n h1)). Qed.
Lemma lem94418 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem94419 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem94418 n h1)). Qed.
Lemma lem94420 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem94417 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem94419 n h1)). Qed.
Lemma lem94421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem94422 (n : nat) : (term1 n) = (term3 n).
Proof. exact (MK_COMB (@lem94421) (@lem94420 n)). Qed.
Lemma lem94423 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem94422 n) (@lem94412 n)). Qed.
Lemma lem94424 (n : nat) : term4 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem94426 : term5.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem94427 (m : nat) : term6 m.
Proof. exact (@lem94426 m). Qed.
Lemma lem94428 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem94429 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem94428 m) (@lem94427 m)). Qed.
Lemma lem94430 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem94429 m n). Qed.
Lemma lem94431 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem94433 : term11.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem94434 (m : nat) : term12 m.
Proof. exact (@lem94433 m). Qed.
Lemma lem94435 (m : nat) : (term12 m) = ((term13 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem94444 : term14.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem94445 (m : nat) : term15 m.
Proof. exact (@lem94444 m). Qed.
Lemma lem94446 (m : nat) : (term15 m) = ((term16 m) = False).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem94449 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94450 : term18.
Proof. exact (@lem94449 term19). Qed.
Lemma lem94451 : term20 = term21.
Proof. exact (eq_refl term20). Qed.
Lemma lem94452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94453 : term22 = term23.
Proof. exact (MK_COMB (@lem94452) (@lem94451)). Qed.
Lemma lem94454 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem94455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94456 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem94455) (@lem94454 m)). Qed.
Lemma lem94457 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem94458 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem94456 m) (@lem94457 m)). Qed.
Lemma lem94459 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem94458 m)). Qed.
Lemma lem94460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94461 : term34 = term35.
Proof. exact (MK_COMB (@lem94460) (@lem94459)). Qed.
Lemma lem94462 : term36 = term37.
Proof. exact (MK_COMB (@lem94453) (@lem94461)). Qed.
Lemma lem94463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94464 : term38 = term39.
Proof. exact (MK_COMB (@lem94463) (@lem94462)). Qed.
Lemma lem94465 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem94466 : term40 = term19.
Proof. exact (fun_ext (fun m : nat => @lem94465 m)). Qed.
Lemma lem94467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94468 : term41 = term42.
Proof. exact (MK_COMB (@lem94467) (@lem94466)). Qed.
Lemma lem94469 : term18 = term43.
Proof. exact (MK_COMB (@lem94464) (@lem94468)). Qed.
Lemma lem94470 : term43.
Proof. exact (EQ_MP (@lem94469) (@lem94450)). Qed.
Lemma lem94471 (m : nat) (h1 : term25 m) : term25 m.
Proof. exact (h1). Qed.
Lemma lem94473 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94474 : term44.
Proof. exact (@lem94473 term45). Qed.
Lemma lem94475 : term46 = term47.
Proof. exact (eq_refl term46). Qed.
Lemma lem94476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94477 : term48 = term49.
Proof. exact (MK_COMB (@lem94476) (@lem94475)). Qed.
Lemma lem94478 (n : nat) : (term50 n) = (term51 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem94479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94480 (n : nat) : (term52 n) = (term53 n).
Proof. exact (MK_COMB (@lem94479) (@lem94478 n)). Qed.
Lemma lem94481 (n : nat) : (term54 n) = (term55 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem94482 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem94480 n) (@lem94481 n)). Qed.
Lemma lem94483 : term58 = term59.
Proof. exact (fun_ext (fun n : nat => @lem94482 n)). Qed.
Lemma lem94484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94485 : term60 = term61.
Proof. exact (MK_COMB (@lem94484) (@lem94483)). Qed.
Lemma lem94486 : term62 = term63.
Proof. exact (MK_COMB (@lem94477) (@lem94485)). Qed.
Lemma lem94487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94488 : term64 = term65.
Proof. exact (MK_COMB (@lem94487) (@lem94486)). Qed.
Lemma lem94489 (n : nat) : (term50 n) = (term51 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem94490 : term66 = term45.
Proof. exact (fun_ext (fun n : nat => @lem94489 n)). Qed.
Lemma lem94491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94492 : term67 = term21.
Proof. exact (MK_COMB (@lem94491) (@lem94490)). Qed.
Lemma lem94493 : term44 = term68.
Proof. exact (MK_COMB (@lem94488) (@lem94492)). Qed.
Lemma lem94494 : term68.
Proof. exact (EQ_MP (@lem94493) (@lem94474)). Qed.
Lemma lem94497 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94498 : term69.
Proof. exact (@lem94497 term70). Qed.
Lemma lem94499 : term71 = term72.
Proof. exact (eq_refl term71). Qed.
Lemma lem94500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94501 : term73 = term74.
Proof. exact (MK_COMB (@lem94500) (@lem94499)). Qed.
Lemma lem94502 (p : nat) : (term75 p) = (term76 p).
Proof. exact (eq_refl (term75 p)). Qed.
Lemma lem94503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94504 (p : nat) : (term77 p) = (term78 p).
Proof. exact (MK_COMB (@lem94503) (@lem94502 p)). Qed.
Lemma lem94505 (p : nat) : (term79 p) = (term80 p).
Proof. exact (eq_refl (term79 p)). Qed.
Lemma lem94506 (p : nat) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem94504 p) (@lem94505 p)). Qed.
Lemma lem94507 : term83 = term84.
Proof. exact (fun_ext (fun p : nat => @lem94506 p)). Qed.
Lemma lem94508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94509 : term85 = term86.
Proof. exact (MK_COMB (@lem94508) (@lem94507)). Qed.
Lemma lem94510 : term87 = term88.
Proof. exact (MK_COMB (@lem94501) (@lem94509)). Qed.
Lemma lem94511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94512 : term89 = term90.
Proof. exact (MK_COMB (@lem94511) (@lem94510)). Qed.
Lemma lem94513 (p : nat) : (term75 p) = (term76 p).
Proof. exact (eq_refl (term75 p)). Qed.
Lemma lem94514 : term91 = term70.
Proof. exact (fun_ext (fun p : nat => @lem94513 p)). Qed.
Lemma lem94515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94516 : term92 = term47.
Proof. exact (MK_COMB (@lem94515) (@lem94514)). Qed.
Lemma lem94517 : term69 = term93.
Proof. exact (MK_COMB (@lem94512) (@lem94516)). Qed.
Lemma lem94518 : term93.
Proof. exact (EQ_MP (@lem94517) (@lem94498)). Qed.
Lemma lem94525 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94526 (n : nat) : term94 n.
Proof. exact (@lem94525 (term95 n)). Qed.
Lemma lem94527 (n : nat) : (term96 n) = (term97 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem94528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94529 (n : nat) : (term98 n) = (term99 n).
Proof. exact (MK_COMB (@lem94528) (@lem94527 n)). Qed.
Lemma lem94530 (n : nat) (p : nat) : (term100 n p) = (term101 n p).
Proof. exact (eq_refl (term100 n p)). Qed.
Lemma lem94531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94532 (n : nat) (p : nat) : (term102 n p) = (term103 n p).
Proof. exact (MK_COMB (@lem94531) (@lem94530 n p)). Qed.
Lemma lem94533 (n : nat) (p : nat) : (term104 n p) = (term105 n p).
Proof. exact (eq_refl (term104 n p)). Qed.
Lemma lem94534 (n : nat) (p : nat) : (term106 n p) = (term107 n p).
Proof. exact (MK_COMB (@lem94532 n p) (@lem94533 n p)). Qed.
Lemma lem94535 (n : nat) : (term108 n) = (term109 n).
Proof. exact (fun_ext (fun p : nat => @lem94534 n p)). Qed.
Lemma lem94536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94537 (n : nat) : (term110 n) = (term111 n).
Proof. exact (MK_COMB (@lem94536) (@lem94535 n)). Qed.
Lemma lem94538 (n : nat) : (term112 n) = (term113 n).
Proof. exact (MK_COMB (@lem94529 n) (@lem94537 n)). Qed.
Lemma lem94539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94540 (n : nat) : (term114 n) = (term115 n).
Proof. exact (MK_COMB (@lem94539) (@lem94538 n)). Qed.
Lemma lem94541 (n : nat) (p : nat) : (term100 n p) = (term101 n p).
Proof. exact (eq_refl (term100 n p)). Qed.
Lemma lem94542 (n : nat) : (term116 n) = (term95 n).
Proof. exact (fun_ext (fun p : nat => @lem94541 n p)). Qed.
Lemma lem94543 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94544 (n : nat) : (term117 n) = (term55 n).
Proof. exact (MK_COMB (@lem94543) (@lem94542 n)). Qed.
Lemma lem94545 (n : nat) : (term94 n) = (term118 n).
Proof. exact (MK_COMB (@lem94540 n) (@lem94544 n)). Qed.
Lemma lem94546 (n : nat) : term118 n.
Proof. exact (EQ_MP (@lem94545 n) (@lem94526 n)). Qed.
Lemma lem94553 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94554 (m : nat) : term119 m.
Proof. exact (@lem94553 (term120 m)). Qed.
Lemma lem94555 (m : nat) : (term121 m) = (term122 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem94556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94557 (m : nat) : (term123 m) = (term124 m).
Proof. exact (MK_COMB (@lem94556) (@lem94555 m)). Qed.
Lemma lem94558 (n : nat) (m : nat) : (term125 m n) = (term126 n m).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem94559 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94560 (n : nat) (m : nat) : (term127 m n) = (term128 n m).
Proof. exact (MK_COMB (@lem94559) (@lem94558 n m)). Qed.
Lemma lem94561 (n : nat) (m : nat) : (term129 m n) = (term130 n m).
Proof. exact (eq_refl (term129 m n)). Qed.
Lemma lem94562 (n : nat) (m : nat) : (term131 m n) = (term132 n m).
Proof. exact (MK_COMB (@lem94560 n m) (@lem94561 n m)). Qed.
Lemma lem94563 (m : nat) : (term133 m) = (term134 m).
Proof. exact (fun_ext (fun n : nat => @lem94562 n m)). Qed.
Lemma lem94564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94565 (m : nat) : (term135 m) = (term136 m).
Proof. exact (MK_COMB (@lem94564) (@lem94563 m)). Qed.
Lemma lem94566 (m : nat) : (term137 m) = (term138 m).
Proof. exact (MK_COMB (@lem94557 m) (@lem94565 m)). Qed.
Lemma lem94567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94568 (m : nat) : (term139 m) = (term140 m).
Proof. exact (MK_COMB (@lem94567) (@lem94566 m)). Qed.
Lemma lem94569 (n : nat) (m : nat) : (term125 m n) = (term126 n m).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem94570 (m : nat) : (term141 m) = (term120 m).
Proof. exact (fun_ext (fun n : nat => @lem94569 n m)). Qed.
Lemma lem94571 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94572 (m : nat) : (term142 m) = (term29 m).
Proof. exact (MK_COMB (@lem94571) (@lem94570 m)). Qed.
Lemma lem94573 (m : nat) : (term119 m) = (term143 m).
Proof. exact (MK_COMB (@lem94568 m) (@lem94572 m)). Qed.
Lemma lem94574 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem94573 m) (@lem94554 m)). Qed.
Lemma lem94577 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94578 (m : nat) : term144 m.
Proof. exact (@lem94577 (term145 m)). Qed.
Lemma lem94579 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem94580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94581 (m : nat) : (term148 m) = (term149 m).
Proof. exact (MK_COMB (@lem94580) (@lem94579 m)). Qed.
Lemma lem94582 (m : nat) (p : nat) : (term150 m p) = (term151 m p).
Proof. exact (eq_refl (term150 m p)). Qed.
Lemma lem94583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94584 (m : nat) (p : nat) : (term152 m p) = (term153 m p).
Proof. exact (MK_COMB (@lem94583) (@lem94582 m p)). Qed.
Lemma lem94585 (m : nat) (p : nat) : (term154 m p) = (term155 m p).
Proof. exact (eq_refl (term154 m p)). Qed.
Lemma lem94586 (m : nat) (p : nat) : (term156 m p) = (term157 m p).
Proof. exact (MK_COMB (@lem94584 m p) (@lem94585 m p)). Qed.
Lemma lem94587 (m : nat) : (term158 m) = (term159 m).
Proof. exact (fun_ext (fun p : nat => @lem94586 m p)). Qed.
Lemma lem94588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94589 (m : nat) : (term160 m) = (term161 m).
Proof. exact (MK_COMB (@lem94588) (@lem94587 m)). Qed.
Lemma lem94590 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem94581 m) (@lem94589 m)). Qed.
Lemma lem94591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94592 (m : nat) : (term164 m) = (term165 m).
Proof. exact (MK_COMB (@lem94591) (@lem94590 m)). Qed.
Lemma lem94593 (m : nat) (p : nat) : (term150 m p) = (term151 m p).
Proof. exact (eq_refl (term150 m p)). Qed.
Lemma lem94594 (m : nat) : (term166 m) = (term145 m).
Proof. exact (fun_ext (fun p : nat => @lem94593 m p)). Qed.
Lemma lem94595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94596 (m : nat) : (term167 m) = (term122 m).
Proof. exact (MK_COMB (@lem94595) (@lem94594 m)). Qed.
Lemma lem94597 (m : nat) : (term144 m) = (term168 m).
Proof. exact (MK_COMB (@lem94592 m) (@lem94596 m)). Qed.
Lemma lem94598 (m : nat) : term168 m.
Proof. exact (EQ_MP (@lem94597 m) (@lem94578 m)). Qed.
Lemma lem94605 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem94606 (n : nat) (m : nat) : term169 n m.
Proof. exact (@lem94605 (term170 n m)). Qed.
Lemma lem94607 (n : nat) (m : nat) : (term171 n m) = (term172 n m).
Proof. exact (eq_refl (term171 n m)). Qed.
Lemma lem94608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94609 (n : nat) (m : nat) : (term173 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem94608) (@lem94607 n m)). Qed.
Lemma lem94610 (n : nat) (m : nat) (p : nat) : (term175 n m p) = (term176 n m p).
Proof. exact (eq_refl (term175 n m p)). Qed.
Lemma lem94611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94612 (n : nat) (m : nat) (p : nat) : (term177 n m p) = (term178 n m p).
Proof. exact (MK_COMB (@lem94611) (@lem94610 n m p)). Qed.
Lemma lem94613 (n : nat) (m : nat) (p : nat) : (term179 n m p) = (term180 n m p).
Proof. exact (eq_refl (term179 n m p)). Qed.
Lemma lem94614 (n : nat) (m : nat) (p : nat) : (term181 n m p) = (term182 n m p).
Proof. exact (MK_COMB (@lem94612 n m p) (@lem94613 n m p)). Qed.
Lemma lem94615 (n : nat) (m : nat) : (term183 n m) = (term184 n m).
Proof. exact (fun_ext (fun p : nat => @lem94614 n m p)). Qed.
Lemma lem94616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94617 (n : nat) (m : nat) : (term185 n m) = (term186 n m).
Proof. exact (MK_COMB (@lem94616) (@lem94615 n m)). Qed.
Lemma lem94618 (n : nat) (m : nat) : (term187 n m) = (term188 n m).
Proof. exact (MK_COMB (@lem94609 n m) (@lem94617 n m)). Qed.
Lemma lem94619 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94620 (n : nat) (m : nat) : (term189 n m) = (term190 n m).
Proof. exact (MK_COMB (@lem94619) (@lem94618 n m)). Qed.
Lemma lem94621 (n : nat) (m : nat) (p : nat) : (term175 n m p) = (term176 n m p).
Proof. exact (eq_refl (term175 n m p)). Qed.
Lemma lem94622 (n : nat) (m : nat) : (term191 n m) = (term170 n m).
Proof. exact (fun_ext (fun p : nat => @lem94621 n m p)). Qed.
Lemma lem94623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem94624 (n : nat) (m : nat) : (term192 n m) = (term130 n m).
Proof. exact (MK_COMB (@lem94623) (@lem94622 n m)). Qed.
Lemma lem94625 (n : nat) (m : nat) : (term169 n m) = (term193 n m).
Proof. exact (MK_COMB (@lem94620 n m) (@lem94624 n m)). Qed.
Lemma lem94626 (n : nat) (m : nat) : term193 n m.
Proof. exact (EQ_MP (@lem94625 n m) (@lem94606 n m)). Qed.
Lemma lem94655 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94656 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem94657 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem94656 n) (@lem94655 n)). Qed.
Lemma lem94658 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem94679 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem94658 n) (@lem94657 n)). Qed.
Lemma lem94680 (p : nat) : (term195 p) = True.
Proof. exact (@lem94679 p). Qed.
Lemma lem94681 : term196 = term196.
Proof. exact (eq_refl term196). Qed.
Lemma lem94682 (p : nat) : (term197 p) = term198.
Proof. exact (MK_COMB (@lem94681) (@lem94680 p)). Qed.
Lemma lem94684 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem94685 : term198 = term199.
Proof. exact (@lem94684 term199). Qed.
Lemma lem94686 (p : nat) : (term197 p) = term199.
Proof. exact (TRANS (@lem94682 p) (@lem94685)). Qed.
Lemma lem94687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94688 (p : nat) : (term200 p) = term201.
Proof. exact (MK_COMB (@lem94687) (@lem94686 p)). Qed.
Lemma lem94690 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem94658 n) (@lem94657 n)). Qed.
Lemma lem94691 (p : nat) : (term195 p) = True.
Proof. exact (@lem94690 p). Qed.
Lemma lem94692 (p : nat) : (term80 p) = term202.
Proof. exact (MK_COMB (@lem94688 p) (@lem94691 p)). Qed.
Lemma lem94694 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem94695 : term202 = True.
Proof. exact (@lem94694 term199). Qed.
Lemma lem94696 (p : nat) : (term80 p) = True.
Proof. exact (TRANS (@lem94692 p) (@lem94695)). Qed.
Lemma lem94697 (p : nat) : True = (term80 p).
Proof. exact (SYM (@lem94696 p)). Qed.
Lemma lem94698 (p : nat) : term80 p.
Proof. exact (EQ_MP (@lem94697 p) (@lem0)). Qed.
Lemma lem94727 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94728 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem94729 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem94728 n) (@lem94727 n)). Qed.
Lemma lem94730 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem94732 (m : nat) : term203 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94733 (m : nat) : (term203 m) = (term204 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem94734 (m : nat) : term204 m.
Proof. exact (EQ_MP (@lem94733 m) (@lem94732 m)). Qed.
Lemma lem94735 (m : nat) (n : nat) : term205 m n.
Proof. exact (@lem94734 m n). Qed.
Lemma lem94736 (m : nat) (n : nat) : (term205 m n) = ((term206 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term205 m n)). Qed.
Lemma lem94756 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94736 m n) (@lem94735 m n)). Qed.
Lemma lem94757 (n : nat) (p : nat) : (term206 n p) = (Peano.lt n p).
Proof. exact (@lem94756 n p). Qed.
Lemma lem94758 (n : nat) : (term207 n) = (term207 n).
Proof. exact (eq_refl (term207 n)). Qed.
Lemma lem94759 (n : nat) (p : nat) : (term208 n p) = (term209 n p).
Proof. exact (MK_COMB (@lem94758 n) (@lem94757 n p)). Qed.
Lemma lem94762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94763 (n : nat) (p : nat) : (term210 n p) = (term211 n p).
Proof. exact (MK_COMB (@lem94762) (@lem94759 n p)). Qed.
Lemma lem94765 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem94730 n) (@lem94729 n)). Qed.
Lemma lem94766 (p : nat) : (term195 p) = True.
Proof. exact (@lem94765 p). Qed.
Lemma lem94767 (n : nat) (p : nat) : (term105 n p) = (term212 n p).
Proof. exact (MK_COMB (@lem94763 n p) (@lem94766 p)). Qed.
Lemma lem94769 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem94770 (n : nat) (p : nat) : (term212 n p) = True.
Proof. exact (@lem94769 (term209 n p)). Qed.
Lemma lem94771 (n : nat) (p : nat) : (term105 n p) = True.
Proof. exact (TRANS (@lem94767 n p) (@lem94770 n p)). Qed.
Lemma lem94772 (n : nat) (p : nat) : True = (term105 n p).
Proof. exact (SYM (@lem94771 n p)). Qed.
Lemma lem94773 (n : nat) (p : nat) : term105 n p.
Proof. exact (EQ_MP (@lem94772 n p) (@lem0)). Qed.
Lemma lem94805 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94806 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem94807 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem94806 n) (@lem94805 n)). Qed.
Lemma lem94808 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem94810 (m : nat) : term203 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94811 (m : nat) : (term203 m) = (term204 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem94812 (m : nat) : term204 m.
Proof. exact (EQ_MP (@lem94811 m) (@lem94810 m)). Qed.
Lemma lem94813 (m : nat) (n : nat) : term205 m n.
Proof. exact (@lem94812 m n). Qed.
Lemma lem94814 (m : nat) (n : nat) : (term205 m n) = ((term206 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term205 m n)). Qed.
Lemma lem94837 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem94808 n) (@lem94807 n)). Qed.
Lemma lem94838 (p : nat) : (term195 p) = True.
Proof. exact (@lem94837 p). Qed.
Lemma lem94839 (m : nat) : (term213 m) = (term213 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem94840 (p : nat) (m : nat) : (term214 m p) = (term215 m).
Proof. exact (MK_COMB (@lem94839 m) (@lem94838 p)). Qed.
Lemma lem94842 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem94843 (m : nat) : (term215 m) = (term216 m).
Proof. exact (@lem94842 (term216 m)). Qed.
Lemma lem94844 (p : nat) (m : nat) : (term214 m p) = (term216 m).
Proof. exact (TRANS (@lem94840 p m) (@lem94843 m)). Qed.
Lemma lem94845 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94846 (p : nat) (m : nat) : (term217 m p) = (term218 m).
Proof. exact (MK_COMB (@lem94845) (@lem94844 p m)). Qed.
Lemma lem94848 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94814 m n) (@lem94813 m n)). Qed.
Lemma lem94849 (m : nat) (p : nat) : (term206 m p) = (Peano.lt m p).
Proof. exact (@lem94848 m p). Qed.
Lemma lem94850 (m : nat) (p : nat) : (term155 m p) = (term219 m p).
Proof. exact (MK_COMB (@lem94846 p m) (@lem94849 m p)). Qed.
Lemma lem94853 (m : nat) (p : nat) : (term219 m p) = (term155 m p).
Proof. exact (SYM (@lem94850 m p)). Qed.
Lemma lem94865 (m : nat) : term220 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem94866 (m : nat) : (term220 m) = (term221 m).
Proof. exact (eq_refl (term220 m)). Qed.
Lemma lem94867 (m : nat) : term221 m.
Proof. exact (EQ_MP (@lem94866 m) (@lem94865 m)). Qed.
Lemma lem94868 (m : nat) (n : nat) : term222 m n.
Proof. exact (@lem94867 m n). Qed.
Lemma lem94869 (m : nat) (n : nat) : (term222 m n) = ((term223 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term222 m n)). Qed.
Lemma lem94889 (m : nat) (n : nat) : (term223 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem94869 m n) (@lem94868 m n)). Qed.
Lemma lem94890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94891 (m : nat) (n : nat) : (term224 m n) = (term225 m n).
Proof. exact (MK_COMB (@lem94890) (@lem94889 m n)). Qed.
Lemma lem94892 (n : nat) : (term226 n) = (term226 n).
Proof. exact (eq_refl (term226 n)). Qed.
Lemma lem94893 (m : nat) (n : nat) : (term227 m n) = (term228 m n).
Proof. exact (MK_COMB (@lem94891 m n) (@lem94892 n)). Qed.
Lemma lem94896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94897 (m : nat) (n : nat) : (term229 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem94896) (@lem94893 m n)). Qed.
Lemma lem94898 (m : nat) : (term226 m) = (term226 m).
Proof. exact (eq_refl (term226 m)). Qed.
Lemma lem94899 (n : nat) (m : nat) : (term172 n m) = (term231 n m).
Proof. exact (MK_COMB (@lem94897 m n) (@lem94898 m)). Qed.
Lemma lem94902 (n : nat) (m : nat) : (term231 n m) = (term172 n m).
Proof. exact (SYM (@lem94899 n m)). Qed.
Lemma lem94908 (m : nat) : term203 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94909 (m : nat) : (term203 m) = (term204 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem94910 (m : nat) : term204 m.
Proof. exact (EQ_MP (@lem94909 m) (@lem94908 m)). Qed.
Lemma lem94911 (m : nat) (n : nat) : term205 m n.
Proof. exact (@lem94910 m n). Qed.
Lemma lem94912 (m : nat) (n : nat) : (term205 m n) = ((term206 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term205 m n)). Qed.
Lemma lem94914 (m : nat) : term220 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem94915 (m : nat) : (term220 m) = (term221 m).
Proof. exact (eq_refl (term220 m)). Qed.
Lemma lem94916 (m : nat) : term221 m.
Proof. exact (EQ_MP (@lem94915 m) (@lem94914 m)). Qed.
Lemma lem94917 (m : nat) (n : nat) : term222 m n.
Proof. exact (@lem94916 m n). Qed.
Lemma lem94918 (m : nat) (n : nat) : (term222 m n) = ((term223 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term222 m n)). Qed.
Lemma lem94920 (n : nat) (m : nat) (h1 : term25 m) : term232 m n.
Proof. exact (@lem94471 m h1 n). Qed.
Lemma lem94921 (n : nat) (m : nat) : (term232 m n) = (term233 n m).
Proof. exact (eq_refl (term232 m n)). Qed.
Lemma lem94922 (n : nat) (m : nat) (h1 : term25 m) : term233 n m.
Proof. exact (EQ_MP (@lem94921 n m) (@lem94920 n m h1)). Qed.
Lemma lem94923 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term234 n m p.
Proof. exact (@lem94922 n m h1 p). Qed.
Lemma lem94924 (n : nat) (m : nat) (p : nat) : (term234 n m p) = (term235 n m p).
Proof. exact (eq_refl (term234 n m p)). Qed.
Lemma lem94925 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term235 n m p.
Proof. exact (EQ_MP (@lem94924 n m p) (@lem94923 n p m h1)). Qed.
Lemma lem94926 (n : nat) (m : nat) (p : nat) : (term235 n m p) = ((term235 n m p) = True).
Proof. exact (@lem7 (term235 n m p)). Qed.
Lemma lem94940 (m : nat) (n : nat) : (term223 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem94918 m n) (@lem94917 m n)). Qed.
Lemma lem94941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94942 (m : nat) (n : nat) : (term224 m n) = (term225 m n).
Proof. exact (MK_COMB (@lem94941) (@lem94940 m n)). Qed.
Lemma lem94944 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94912 m n) (@lem94911 m n)). Qed.
Lemma lem94945 (n : nat) (p : nat) : (term206 n p) = (Peano.lt n p).
Proof. exact (@lem94944 n p). Qed.
Lemma lem94946 (m : nat) (n : nat) (p : nat) : (term236 m n p) = (term237 m n p).
Proof. exact (MK_COMB (@lem94942 m n) (@lem94945 n p)). Qed.
Lemma lem94949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94950 (m : nat) (n : nat) (p : nat) : (term238 m n p) = (term239 m n p).
Proof. exact (MK_COMB (@lem94949) (@lem94946 m n p)). Qed.
Lemma lem94952 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94912 m n) (@lem94911 m n)). Qed.
Lemma lem94953 (m : nat) (p : nat) : (term206 m p) = (Peano.lt m p).
Proof. exact (@lem94952 m p). Qed.
Lemma lem94954 (n : nat) (m : nat) (p : nat) : (term180 n m p) = (term235 n m p).
Proof. exact (MK_COMB (@lem94950 m n p) (@lem94953 m p)). Qed.
Lemma lem94956 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : (term235 n m p) = True.
Proof. exact (EQ_MP (@lem94926 n m p) (@lem94925 n p m h1)). Qed.
Lemma lem94957 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : (term180 n m p) = True.
Proof. exact (TRANS (@lem94954 n m p) (@lem94956 n p m h1)). Qed.
Lemma lem94958 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : True = (term180 n m p).
Proof. exact (SYM (@lem94957 n p m h1)). Qed.
Lemma lem94959 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term180 n m p.
Proof. exact (EQ_MP (@lem94958 n p m h1) (@lem0)). Qed.
Lemma lem94965 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem94435 m) (@lem94434 m)). Qed.
Lemma lem94966 : term199 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem94965 (NUMERAL 0)). Qed.
Lemma lem94968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem94969 (x : nat) : (x = x) = True.
Proof. exact (@lem94968 nat x). Qed.
Lemma lem94970 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem94969 (NUMERAL 0)). Qed.
Lemma lem94971 : term199 = True.
Proof. exact (TRANS (@lem94966) (@lem94970)). Qed.
Lemma lem94972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94973 : term196 = (and True).
Proof. exact (MK_COMB (@lem94972) (@lem94971)). Qed.
Lemma lem94975 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem94976 : term240 = False.
Proof. exact (@lem94975 (NUMERAL 0)). Qed.
Lemma lem94977 : term241 = (True /\ False).
Proof. exact (MK_COMB (@lem94973) (@lem94976)). Qed.
Lemma lem94979 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem94980 : (True /\ False) = False.
Proof. exact (@lem94979 False). Qed.
Lemma lem94981 : term241 = False.
Proof. exact (TRANS (@lem94977) (@lem94980)). Qed.
Lemma lem94982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94983 : term242 = (imp False).
Proof. exact (MK_COMB (@lem94982) (@lem94981)). Qed.
Lemma lem94985 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem94986 : term240 = False.
Proof. exact (@lem94985 (NUMERAL 0)). Qed.
Lemma lem94987 : term72 = (False -> False).
Proof. exact (MK_COMB (@lem94983) (@lem94986)). Qed.
Lemma lem94989 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem94990 : (False -> False) = True.
Proof. exact (@lem94989 False). Qed.
Lemma lem94991 : term72 = True.
Proof. exact (TRANS (@lem94987) (@lem94990)). Qed.
Lemma lem94992 : True = term72.
Proof. exact (SYM (@lem94991)). Qed.
Lemma lem94999 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem94431 m n) (@lem94430 m n)). Qed.
Lemma lem95000 (n : nat) : (term243 n) = (term244 n).
Proof. exact (@lem94999 (NUMERAL 0) n). Qed.
Lemma lem95004 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem94424 n (@lem94423 n)). Qed.
Lemma lem95005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem95006 (n : nat) : (term245 n) = (or False).
Proof. exact (MK_COMB (@lem95005) (@lem95004 n)). Qed.
Lemma lem95007 (n : nat) : (term246 n) = (term246 n).
Proof. exact (eq_refl (term246 n)). Qed.
Lemma lem95008 (n : nat) : (term244 n) = (term247 n).
Proof. exact (MK_COMB (@lem95006 n) (@lem95007 n)). Qed.
Lemma lem95010 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem95011 (n : nat) : (term247 n) = (term246 n).
Proof. exact (@lem95010 (term246 n)). Qed.
Lemma lem95012 (n : nat) : (term244 n) = (term246 n).
Proof. exact (TRANS (@lem95008 n) (@lem95011 n)). Qed.
Lemma lem95013 (n : nat) : (term243 n) = (term246 n).
Proof. exact (TRANS (@lem95000 n) (@lem95012 n)). Qed.
Lemma lem95014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95015 (n : nat) : (term207 n) = (term248 n).
Proof. exact (MK_COMB (@lem95014) (@lem95013 n)). Qed.
Lemma lem95017 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95018 (n : nat) : (term226 n) = False.
Proof. exact (@lem95017 (S n)). Qed.
Lemma lem95019 (n : nat) : (term249 n) = (term250 n).
Proof. exact (MK_COMB (@lem95015 n) (@lem95018 n)). Qed.
Lemma lem95021 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem95022 (n : nat) : (term250 n) = False.
Proof. exact (@lem95021 (term246 n)). Qed.
Lemma lem95023 (n : nat) : (term249 n) = False.
Proof. exact (TRANS (@lem95019 n) (@lem95022 n)). Qed.
Lemma lem95024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95025 (n : nat) : (term251 n) = (imp False).
Proof. exact (MK_COMB (@lem95024) (@lem95023 n)). Qed.
Lemma lem95027 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95028 : term240 = False.
Proof. exact (@lem95027 (NUMERAL 0)). Qed.
Lemma lem95029 (n : nat) : (term97 n) = (False -> False).
Proof. exact (MK_COMB (@lem95025 n) (@lem95028)). Qed.
Lemma lem95031 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95032 : (False -> False) = True.
Proof. exact (@lem95031 False). Qed.
Lemma lem95033 (n : nat) : (term97 n) = True.
Proof. exact (TRANS (@lem95029 n) (@lem95032)). Qed.
Lemma lem95034 (n : nat) : True = (term97 n).
Proof. exact (SYM (@lem95033 n)). Qed.
Lemma lem95041 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem94435 m) (@lem94434 m)). Qed.
Lemma lem95042 (m : nat) : (term216 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem95041 (S m)). Qed.
Lemma lem95044 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem94413 n (@lem94412 n)). Qed.
Lemma lem95045 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem95044 m). Qed.
Lemma lem95046 (m : nat) : (term216 m) = False.
Proof. exact (TRANS (@lem95042 m) (@lem95045 m)). Qed.
Lemma lem95047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95048 (m : nat) : (term213 m) = (and False).
Proof. exact (MK_COMB (@lem95047) (@lem95046 m)). Qed.
Lemma lem95050 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95051 : term240 = False.
Proof. exact (@lem95050 (NUMERAL 0)). Qed.
Lemma lem95052 (m : nat) : (term252 m) = (False /\ False).
Proof. exact (MK_COMB (@lem95048 m) (@lem95051)). Qed.
Lemma lem95054 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem95055 : (False /\ False) = False.
Proof. exact (@lem95054 False). Qed.
Lemma lem95056 (m : nat) : (term252 m) = False.
Proof. exact (TRANS (@lem95052 m) (@lem95055)). Qed.
Lemma lem95057 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95058 (m : nat) : (term253 m) = (imp False).
Proof. exact (MK_COMB (@lem95057) (@lem95056 m)). Qed.
Lemma lem95060 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95061 (m : nat) : (term226 m) = False.
Proof. exact (@lem95060 (S m)). Qed.
Lemma lem95062 (m : nat) : (term147 m) = (False -> False).
Proof. exact (MK_COMB (@lem95058 m) (@lem95061 m)). Qed.
Lemma lem95064 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95065 : (False -> False) = True.
Proof. exact (@lem95064 False). Qed.
Lemma lem95066 (m : nat) : (term147 m) = True.
Proof. exact (TRANS (@lem95062 m) (@lem95065)). Qed.
Lemma lem95067 (m : nat) : True = (term147 m).
Proof. exact (SYM (@lem95066 m)). Qed.
Lemma lem95072 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem94435 m) (@lem94434 m)). Qed.
Lemma lem95073 (m : nat) : (term216 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem95072 (S m)). Qed.
Lemma lem95075 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem94413 n (@lem94412 n)). Qed.
Lemma lem95076 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem95075 m). Qed.
Lemma lem95077 (m : nat) : (term216 m) = False.
Proof. exact (TRANS (@lem95073 m) (@lem95076 m)). Qed.
Lemma lem95078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95079 (m : nat) : (term218 m) = (imp False).
Proof. exact (MK_COMB (@lem95078) (@lem95077 m)). Qed.
Lemma lem95080 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem95081 (m : nat) (p : nat) : (term219 m p) = (term254 m p).
Proof. exact (MK_COMB (@lem95079 m) (@lem95080 m p)). Qed.
Lemma lem95083 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95084 (m : nat) (p : nat) : (term254 m p) = True.
Proof. exact (@lem95083 (Peano.lt m p)). Qed.
Lemma lem95085 (m : nat) (p : nat) : (term219 m p) = True.
Proof. exact (TRANS (@lem95081 m p) (@lem95084 m p)). Qed.
Lemma lem95086 (m : nat) (p : nat) : True = (term219 m p).
Proof. exact (SYM (@lem95085 m p)). Qed.
Lemma lem95087 (m : nat) (p : nat) : term219 m p.
Proof. exact (EQ_MP (@lem95086 m p) (@lem0)). Qed.
Lemma lem95093 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95094 (n : nat) : (term226 n) = False.
Proof. exact (@lem95093 (S n)). Qed.
Lemma lem95095 (m : nat) (n : nat) : (term225 m n) = (term225 m n).
Proof. exact (eq_refl (term225 m n)). Qed.
Lemma lem95096 (m : nat) (n : nat) : (term228 m n) = (term255 m n).
Proof. exact (MK_COMB (@lem95095 m n) (@lem95094 n)). Qed.
Lemma lem95098 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem95099 (m : nat) (n : nat) : (term255 m n) = False.
Proof. exact (@lem95098 (Peano.le m n)). Qed.
Lemma lem95100 (m : nat) (n : nat) : (term228 m n) = False.
Proof. exact (TRANS (@lem95096 m n) (@lem95099 m n)). Qed.
Lemma lem95101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95102 (m : nat) (n : nat) : (term230 m n) = (imp False).
Proof. exact (MK_COMB (@lem95101) (@lem95100 m n)). Qed.
Lemma lem95104 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem94446 m) (@lem94445 m)). Qed.
Lemma lem95105 (m : nat) : (term226 m) = False.
Proof. exact (@lem95104 (S m)). Qed.
Lemma lem95106 (n : nat) (m : nat) : (term231 n m) = (False -> False).
Proof. exact (MK_COMB (@lem95102 m n) (@lem95105 m)). Qed.
Lemma lem95108 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95109 : (False -> False) = True.
Proof. exact (@lem95108 False). Qed.
Lemma lem95110 (n : nat) (m : nat) : (term231 n m) = True.
Proof. exact (TRANS (@lem95106 n m) (@lem95109)). Qed.
Lemma lem95111 (n : nat) (m : nat) : True = (term231 n m).
Proof. exact (SYM (@lem95110 n m)). Qed.
Lemma lem95112 (n : nat) (m : nat) : term231 n m.
Proof. exact (EQ_MP (@lem95111 n m) (@lem0)). Qed.
Lemma lem95113 (n : nat) (m : nat) : term172 n m.
Proof. exact (EQ_MP (@lem94902 n m) (@lem95112 n m)). Qed.
Lemma lem95114 (m : nat) (p : nat) : term155 m p.
Proof. exact (EQ_MP (@lem94853 m p) (@lem95087 m p)). Qed.
Lemma lem95115 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem95067 m) (@lem0)). Qed.
Lemma lem95116 (n : nat) : term97 n.
Proof. exact (EQ_MP (@lem95034 n) (@lem0)). Qed.
Lemma lem95117 : term72.
Proof. exact (EQ_MP (@lem94992) (@lem0)). Qed.
Lemma lem95118 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term182 n m p.
Proof. exact (fun h0 : term176 n m p => @lem94959 n p m h1). Qed.
Lemma lem95123 (n : nat) (m : nat) (h1 : term25 m) : term186 n m.
Proof. exact (fun p : nat => @lem95118 n p m h1). Qed.
Lemma lem95124 (n : nat) (m : nat) (h1 : term25 m) : term188 n m.
Proof. exact (conj (@lem95113 n m) (@lem95123 n m h1)). Qed.
Lemma lem95125 (n : nat) (m : nat) (h1 : term25 m) : term130 n m.
Proof. exact (@lem94626 n m (@lem95124 n m h1)). Qed.
Lemma lem95126 (m : nat) (p : nat) : term157 m p.
Proof. exact (fun h0 : term151 m p => @lem95114 m p). Qed.
Lemma lem95131 (m : nat) : term161 m.
Proof. exact (fun p : nat => @lem95126 m p). Qed.
Lemma lem95132 (m : nat) : term163 m.
Proof. exact (conj (@lem95115 m) (@lem95131 m)). Qed.
Lemma lem95133 (m : nat) : term122 m.
Proof. exact (@lem94598 m (@lem95132 m)). Qed.
Lemma lem95134 (n : nat) (m : nat) (h1 : term25 m) : term132 n m.
Proof. exact (fun h0 : term126 n m => @lem95125 n m h1). Qed.
Lemma lem95139 (m : nat) (h1 : term25 m) : term136 m.
Proof. exact (fun n : nat => @lem95134 n m h1). Qed.
Lemma lem95140 (m : nat) (h1 : term25 m) : term138 m.
Proof. exact (conj (@lem95133 m) (@lem95139 m h1)). Qed.
Lemma lem95141 (m : nat) (h1 : term25 m) : term29 m.
Proof. exact (@lem94574 m (@lem95140 m h1)). Qed.
Lemma lem95142 (n : nat) (p : nat) : term107 n p.
Proof. exact (fun h0 : term101 n p => @lem94773 n p). Qed.
Lemma lem95147 (n : nat) : term111 n.
Proof. exact (fun p : nat => @lem95142 n p). Qed.
Lemma lem95148 (n : nat) : term113 n.
Proof. exact (conj (@lem95116 n) (@lem95147 n)). Qed.
Lemma lem95149 (n : nat) : term55 n.
Proof. exact (@lem94546 n (@lem95148 n)). Qed.
Lemma lem95150 (p : nat) : term82 p.
Proof. exact (fun h0 : term76 p => @lem94698 p). Qed.
Lemma lem95155 : term86.
Proof. exact (fun p : nat => @lem95150 p). Qed.
Lemma lem95156 : term88.
Proof. exact (conj (@lem95117) (@lem95155)). Qed.
Lemma lem95157 : term47.
Proof. exact (@lem94518 (@lem95156)). Qed.
Lemma lem95158 (n : nat) : term57 n.
Proof. exact (fun h0 : term51 n => @lem95149 n). Qed.
Lemma lem95163 : term61.
Proof. exact (fun n : nat => @lem95158 n). Qed.
Lemma lem95164 : term63.
Proof. exact (conj (@lem95157) (@lem95163)). Qed.
Lemma lem95165 : term21.
Proof. exact (@lem94494 (@lem95164)). Qed.
Lemma lem95166 (m : nat) : term31 m.
Proof. exact (fun h0 : term25 m => @lem95141 m h0). Qed.
Lemma lem95171 : term35.
Proof. exact (fun m : nat => @lem95166 m). Qed.
Lemma lem95172 : term37.
Proof. exact (conj (@lem95165) (@lem95171)). Qed.
Lemma lem95173 : term42.
Proof. exact (@lem94470 (@lem95172)). Qed.
