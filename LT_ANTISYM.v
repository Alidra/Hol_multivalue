Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ANTISYM_term_abbrevs.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem92427 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem92428 (m : nat) : term1 m.
Proof. exact (@lem92427 m). Qed.
Lemma lem92429 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem92430 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem92429 m) (@lem92428 m)). Qed.
Lemma lem92431 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem92430 m n). Qed.
Lemma lem92432 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem92434 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem92435 (m : nat) : term7 m.
Proof. exact (@lem92434 m). Qed.
Lemma lem92436 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem92439 (P : nat -> Prop) : term9 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92440 : term10.
Proof. exact (@lem92439 term11). Qed.
Lemma lem92441 : term12 = term13.
Proof. exact (eq_refl term12). Qed.
Lemma lem92442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92443 : term14 = term15.
Proof. exact (MK_COMB (@lem92442) (@lem92441)). Qed.
Lemma lem92444 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem92445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92446 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem92445) (@lem92444 m)). Qed.
Lemma lem92447 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem92448 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem92446 m) (@lem92447 m)). Qed.
Lemma lem92449 : term24 = term25.
Proof. exact (fun_ext (fun m : nat => @lem92448 m)). Qed.
Lemma lem92450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92451 : term26 = term27.
Proof. exact (MK_COMB (@lem92450) (@lem92449)). Qed.
Lemma lem92452 : term28 = term29.
Proof. exact (MK_COMB (@lem92443) (@lem92451)). Qed.
Lemma lem92453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92454 : term30 = term31.
Proof. exact (MK_COMB (@lem92453) (@lem92452)). Qed.
Lemma lem92455 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem92456 : term32 = term11.
Proof. exact (fun_ext (fun m : nat => @lem92455 m)). Qed.
Lemma lem92457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92458 : term33 = term34.
Proof. exact (MK_COMB (@lem92457) (@lem92456)). Qed.
Lemma lem92459 : term10 = term35.
Proof. exact (MK_COMB (@lem92454) (@lem92458)). Qed.
Lemma lem92460 : term35.
Proof. exact (EQ_MP (@lem92459) (@lem92440)). Qed.
Lemma lem92461 (m : nat) (h1 : term17 m) : term17 m.
Proof. exact (h1). Qed.
Lemma lem92463 (P : nat -> Prop) : term9 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92464 : term36.
Proof. exact (@lem92463 term37). Qed.
Lemma lem92465 : term38 = term39.
Proof. exact (eq_refl term38). Qed.
Lemma lem92466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92467 : term40 = term41.
Proof. exact (MK_COMB (@lem92466) (@lem92465)). Qed.
Lemma lem92468 (n : nat) : (term42 n) = (term43 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem92469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92470 (n : nat) : (term44 n) = (term45 n).
Proof. exact (MK_COMB (@lem92469) (@lem92468 n)). Qed.
Lemma lem92471 (n : nat) : (term46 n) = (term47 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem92472 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem92470 n) (@lem92471 n)). Qed.
Lemma lem92473 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem92472 n)). Qed.
Lemma lem92474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92475 : term52 = term53.
Proof. exact (MK_COMB (@lem92474) (@lem92473)). Qed.
Lemma lem92476 : term54 = term55.
Proof. exact (MK_COMB (@lem92467) (@lem92475)). Qed.
Lemma lem92477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92478 : term56 = term57.
Proof. exact (MK_COMB (@lem92477) (@lem92476)). Qed.
Lemma lem92479 (n : nat) : (term42 n) = (term43 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem92480 : term58 = term37.
Proof. exact (fun_ext (fun n : nat => @lem92479 n)). Qed.
Lemma lem92481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92482 : term59 = term13.
Proof. exact (MK_COMB (@lem92481) (@lem92480)). Qed.
Lemma lem92483 : term36 = term60.
Proof. exact (MK_COMB (@lem92478) (@lem92482)). Qed.
Lemma lem92484 : term60.
Proof. exact (EQ_MP (@lem92483) (@lem92464)). Qed.
Lemma lem92491 (P : nat -> Prop) : term9 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92492 (m : nat) : term61 m.
Proof. exact (@lem92491 (term62 m)). Qed.
Lemma lem92493 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem92494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92495 (m : nat) : (term65 m) = (term66 m).
Proof. exact (MK_COMB (@lem92494) (@lem92493 m)). Qed.
Lemma lem92496 (n : nat) (m : nat) : (term67 m n) = (term68 n m).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem92497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92498 (n : nat) (m : nat) : (term69 m n) = (term70 n m).
Proof. exact (MK_COMB (@lem92497) (@lem92496 n m)). Qed.
Lemma lem92499 (n : nat) (m : nat) : (term71 m n) = (term72 n m).
Proof. exact (eq_refl (term71 m n)). Qed.
Lemma lem92500 (n : nat) (m : nat) : (term73 m n) = (term74 n m).
Proof. exact (MK_COMB (@lem92498 n m) (@lem92499 n m)). Qed.
Lemma lem92501 (m : nat) : (term75 m) = (term76 m).
Proof. exact (fun_ext (fun n : nat => @lem92500 n m)). Qed.
Lemma lem92502 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92503 (m : nat) : (term77 m) = (term78 m).
Proof. exact (MK_COMB (@lem92502) (@lem92501 m)). Qed.
Lemma lem92504 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem92495 m) (@lem92503 m)). Qed.
Lemma lem92505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92506 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem92505) (@lem92504 m)). Qed.
Lemma lem92507 (n : nat) (m : nat) : (term67 m n) = (term68 n m).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem92508 (m : nat) : (term83 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem92507 n m)). Qed.
Lemma lem92509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92510 (m : nat) : (term84 m) = (term21 m).
Proof. exact (MK_COMB (@lem92509) (@lem92508 m)). Qed.
Lemma lem92511 (m : nat) : (term61 m) = (term85 m).
Proof. exact (MK_COMB (@lem92506 m) (@lem92510 m)). Qed.
Lemma lem92512 (m : nat) : term85 m.
Proof. exact (EQ_MP (@lem92511 m) (@lem92492 m)). Qed.
Lemma lem92525 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem92526 : term86 = term87.
Proof. exact (@lem92525 term87). Qed.
Lemma lem92527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92528 : term39 = term88.
Proof. exact (MK_COMB (@lem92527) (@lem92526)). Qed.
Lemma lem92529 : term88 = term39.
Proof. exact (SYM (@lem92528)). Qed.
Lemma lem92557 (m : nat) : term89 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem92558 (m : nat) : (term89 m) = (term90 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem92559 (m : nat) : term90 m.
Proof. exact (EQ_MP (@lem92558 m) (@lem92557 m)). Qed.
Lemma lem92560 (m : nat) (n : nat) : term91 m n.
Proof. exact (@lem92559 m n). Qed.
Lemma lem92561 (m : nat) (n : nat) : (term91 m n) = ((term92 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term91 m n)). Qed.
Lemma lem92563 (n : nat) (m : nat) (h1 : term17 m) : term93 m n.
Proof. exact (@lem92461 m h1 n). Qed.
Lemma lem92564 (n : nat) (m : nat) : (term93 m n) = (term94 n m).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem92565 (n : nat) (m : nat) (h1 : term17 m) : term94 n m.
Proof. exact (EQ_MP (@lem92564 n m) (@lem92563 n m h1)). Qed.
Lemma lem92566 (n : nat) (m : nat) : term95 n m.
Proof. exact (@lem82 (term96 n m)). Qed.
Lemma lem92573 (m : nat) (n : nat) : (term92 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem92561 m n) (@lem92560 m n)). Qed.
Lemma lem92574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92575 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (MK_COMB (@lem92574) (@lem92573 m n)). Qed.
Lemma lem92577 (m : nat) (n : nat) : (term92 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem92561 m n) (@lem92560 m n)). Qed.
Lemma lem92578 (n : nat) (m : nat) : (term92 n m) = (Peano.lt n m).
Proof. exact (@lem92577 n m). Qed.
Lemma lem92579 (n : nat) (m : nat) : (term99 n m) = (term96 n m).
Proof. exact (MK_COMB (@lem92575 m n) (@lem92578 n m)). Qed.
Lemma lem92581 (n : nat) (m : nat) (h1 : term17 m) : (term96 n m) = False.
Proof. exact (@lem92566 n m (@lem92565 n m h1)). Qed.
Lemma lem92582 (n : nat) (m : nat) (h1 : term17 m) : (term99 n m) = False.
Proof. exact (TRANS (@lem92579 n m) (@lem92581 n m h1)). Qed.
Lemma lem92583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92584 (n : nat) (m : nat) (h1 : term17 m) : (term72 n m) = (~ False).
Proof. exact (MK_COMB (@lem92583) (@lem92582 n m h1)). Qed.
Lemma lem92586 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92587 (n : nat) (m : nat) (h1 : term17 m) : (term72 n m) = True.
Proof. exact (TRANS (@lem92584 n m h1) (@lem92586)). Qed.
Lemma lem92588 (n : nat) (m : nat) (h1 : term17 m) : True = (term72 n m).
Proof. exact (SYM (@lem92587 n m h1)). Qed.
Lemma lem92589 (n : nat) (m : nat) (h1 : term17 m) : term72 n m.
Proof. exact (EQ_MP (@lem92588 n m h1) (@lem0)). Qed.
Lemma lem92591 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem92436 m) (@lem92435 m)). Qed.
Lemma lem92592 : term87 = False.
Proof. exact (@lem92591 (NUMERAL 0)). Qed.
Lemma lem92593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92594 : term88 = (~ False).
Proof. exact (MK_COMB (@lem92593) (@lem92592)). Qed.
Lemma lem92596 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92597 : term88 = True.
Proof. exact (TRANS (@lem92594) (@lem92596)). Qed.
Lemma lem92598 : True = term88.
Proof. exact (SYM (@lem92597)). Qed.
Lemma lem92599 : term88.
Proof. exact (EQ_MP (@lem92598) (@lem0)). Qed.
Lemma lem92603 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem92432 m n) (@lem92431 m n)). Qed.
Lemma lem92604 (n : nat) : (term100 n) = (term101 n).
Proof. exact (@lem92603 (NUMERAL 0) n). Qed.
Lemma lem92609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92610 (n : nat) : (term102 n) = (term103 n).
Proof. exact (MK_COMB (@lem92609) (@lem92604 n)). Qed.
Lemma lem92612 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem92436 m) (@lem92435 m)). Qed.
Lemma lem92613 (n : nat) : (term104 n) = False.
Proof. exact (@lem92612 (S n)). Qed.
Lemma lem92614 (n : nat) : (term105 n) = (term106 n).
Proof. exact (MK_COMB (@lem92610 n) (@lem92613 n)). Qed.
Lemma lem92616 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem92617 (n : nat) : (term106 n) = False.
Proof. exact (@lem92616 (term101 n)). Qed.
Lemma lem92618 (n : nat) : (term105 n) = False.
Proof. exact (TRANS (@lem92614 n) (@lem92617 n)). Qed.
Lemma lem92619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92620 (n : nat) : (term47 n) = (~ False).
Proof. exact (MK_COMB (@lem92619) (@lem92618 n)). Qed.
Lemma lem92622 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92623 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem92620 n) (@lem92622)). Qed.
Lemma lem92624 (n : nat) : True = (term47 n).
Proof. exact (SYM (@lem92623 n)). Qed.
Lemma lem92629 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem92436 m) (@lem92435 m)). Qed.
Lemma lem92630 (m : nat) : (term104 m) = False.
Proof. exact (@lem92629 (S m)). Qed.
Lemma lem92631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92632 (m : nat) : (term107 m) = (and False).
Proof. exact (MK_COMB (@lem92631) (@lem92630 m)). Qed.
Lemma lem92634 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem92432 m n) (@lem92431 m n)). Qed.
Lemma lem92635 (m : nat) : (term100 m) = (term101 m).
Proof. exact (@lem92634 (NUMERAL 0) m). Qed.
Lemma lem92640 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem92632 m) (@lem92635 m)). Qed.
Lemma lem92642 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem92643 (m : nat) : (term109 m) = False.
Proof. exact (@lem92642 (term101 m)). Qed.
Lemma lem92644 (m : nat) : (term108 m) = False.
Proof. exact (TRANS (@lem92640 m) (@lem92643 m)). Qed.
Lemma lem92645 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92646 (m : nat) : (term64 m) = (~ False).
Proof. exact (MK_COMB (@lem92645) (@lem92644 m)). Qed.
Lemma lem92648 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92649 (m : nat) : (term64 m) = True.
Proof. exact (TRANS (@lem92646 m) (@lem92648)). Qed.
Lemma lem92650 (m : nat) : True = (term64 m).
Proof. exact (SYM (@lem92649 m)). Qed.
Lemma lem92652 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem92650 m) (@lem0)). Qed.
Lemma lem92653 (n : nat) : term47 n.
Proof. exact (EQ_MP (@lem92624 n) (@lem0)). Qed.
Lemma lem92654 : term39.
Proof. exact (EQ_MP (@lem92529) (@lem92599)). Qed.
Lemma lem92655 (n : nat) (m : nat) (h1 : term17 m) : term74 n m.
Proof. exact (fun h0 : term68 n m => @lem92589 n m h1). Qed.
Lemma lem92660 (m : nat) (h1 : term17 m) : term78 m.
Proof. exact (fun n : nat => @lem92655 n m h1). Qed.
Lemma lem92661 (m : nat) (h1 : term17 m) : term80 m.
Proof. exact (conj (@lem92652 m) (@lem92660 m h1)). Qed.
Lemma lem92662 (m : nat) (h1 : term17 m) : term21 m.
Proof. exact (@lem92512 m (@lem92661 m h1)). Qed.
Lemma lem92663 (n : nat) : term49 n.
Proof. exact (fun h0 : term43 n => @lem92653 n). Qed.
Lemma lem92668 : term53.
Proof. exact (fun n : nat => @lem92663 n). Qed.
Lemma lem92669 : term55.
Proof. exact (conj (@lem92654) (@lem92668)). Qed.
Lemma lem92670 : term13.
Proof. exact (@lem92484 (@lem92669)). Qed.
Lemma lem92671 (m : nat) : term23 m.
Proof. exact (fun h0 : term17 m => @lem92662 m h0). Qed.
Lemma lem92676 : term27.
Proof. exact (fun m : nat => @lem92671 m). Qed.
Lemma lem92677 : term29.
Proof. exact (conj (@lem92670) (@lem92676)). Qed.
Lemma lem92678 : term34.
Proof. exact (@lem92460 (@lem92677)). Qed.
