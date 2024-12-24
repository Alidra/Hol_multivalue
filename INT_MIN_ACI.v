Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_ACI_term_abbrevs.
Require Import REAL_MIN_ACI_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305437 (z : real) (x : real) (y : real) : term0 z x y.
Proof. exact (proj2 (@lem1581662 z x y)). Qed.
Lemma lem2305438 (z : real) (x : real) (y : real) : term1 z x y.
Proof. exact (proj2 (@lem2305437 z x y)). Qed.
Lemma lem2305439 (x : real) (y : real) : term2 x y.
Proof. exact (proj2 (@lem2305438 (@el real) x y)). Qed.
Lemma lem2305440 (x : real) (y : real) : (term3 x y) = (real_min x y).
Proof. exact (proj2 (@lem2305439 x y)). Qed.
Lemma lem2305441 (x : real) : term4 x.
Proof. exact (fun y : real => @lem2305440 x y). Qed.
Lemma lem2305442 : term5.
Proof. exact (fun x : real => @lem2305441 x). Qed.
Lemma lem2305443 (x : int) : term6 x.
Proof. exact (@lem2305442 (real_of_int x)). Qed.
Lemma lem2305444 (x : int) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2305445 (x : int) : term7 x.
Proof. exact (EQ_MP (@lem2305444 x) (@lem2305443 x)). Qed.
Lemma lem2305446 (x : int) (y : int) : term8 x y.
Proof. exact (@lem2305445 x (real_of_int y)). Qed.
Lemma lem2305447 (x : int) (y : int) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem2305448 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2305447 x y) (@lem2305446 x y)). Qed.
Lemma lem2305450 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305451 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305452 (x : int) (y : int) : (term9 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2305451 x) (@lem2305450 x y)). Qed.
Lemma lem2305454 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305455 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (@lem2305454 x (int_min x y)). Qed.
Lemma lem2305456 (x : int) (y : int) : (term9 x y) = (term14 x y).
Proof. exact (TRANS (@lem2305452 x y) (@lem2305455 x y)). Qed.
Lemma lem2305457 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305458 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2305457) (@lem2305456 x y)). Qed.
Lemma lem2305460 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305461 (x : int) (y : int) : ((term9 x y) = (term10 x y)) = ((term14 x y) = (term11 x y)).
Proof. exact (MK_COMB (@lem2305458 x y) (@lem2305460 x y)). Qed.
Lemma lem2305463 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305464 (x : int) (y : int) : ((term14 x y) = (term11 x y)) = ((term17 x y) = (int_min x y)).
Proof. exact (@lem2305463 (term17 x y) (int_min x y)). Qed.
Lemma lem2305465 (x : int) (y : int) : ((term9 x y) = (term10 x y)) = ((term17 x y) = (int_min x y)).
Proof. exact (TRANS (@lem2305461 x y) (@lem2305464 x y)). Qed.
Lemma lem2305466 (x : int) (y : int) : (term17 x y) = (int_min x y).
Proof. exact (EQ_MP (@lem2305465 x y) (@lem2305448 x y)). Qed.
Lemma lem2305467 (x : real) : (real_min x x) = x.
Proof. exact (proj1 (@lem2305439 x (@el real))). Qed.
Lemma lem2305468 : term18.
Proof. exact (fun x : real => @lem2305467 x). Qed.
Lemma lem2305469 (x : int) : term19 x.
Proof. exact (@lem2305468 (real_of_int x)). Qed.
Lemma lem2305470 (x : int) : (term19 x) = ((term20 x) = (real_of_int x)).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2305471 (x : int) : (term20 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2305470 x) (@lem2305469 x)). Qed.
Lemma lem2305473 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305474 (x : int) : (term20 x) = (term21 x).
Proof. exact (@lem2305473 x x). Qed.
Lemma lem2305475 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305476 (x : int) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem2305475) (@lem2305474 x)). Qed.
Lemma lem2305477 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305478 (x : int) : ((term20 x) = (real_of_int x)) = ((term21 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2305476 x) (@lem2305477 x)). Qed.
Lemma lem2305480 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305481 (x : int) : ((term21 x) = (real_of_int x)) = ((int_min x x) = x).
Proof. exact (@lem2305480 (int_min x x) x). Qed.
Lemma lem2305482 (x : int) : ((term20 x) = (real_of_int x)) = ((int_min x x) = x).
Proof. exact (TRANS (@lem2305478 x) (@lem2305481 x)). Qed.
Lemma lem2305483 (x : int) : (int_min x x) = x.
Proof. exact (EQ_MP (@lem2305482 x) (@lem2305471 x)). Qed.
Lemma lem2305484 (x : int) (y : int) : term24 x y.
Proof. exact (conj (@lem2305483 x) (@lem2305466 x y)). Qed.
Lemma lem2305485 (y : real) (x : real) (z : real) : (term25 x y z) = (term25 y x z).
Proof. exact (proj1 (@lem2305438 z x y)). Qed.
Lemma lem2305486 (y : real) (x : real) : term26 y x.
Proof. exact (fun z : real => @lem2305485 y x z). Qed.
Lemma lem2305487 (y : real) : term27 y.
Proof. exact (fun x : real => @lem2305486 y x). Qed.
Lemma lem2305488 : term28.
Proof. exact (fun y : real => @lem2305487 y). Qed.
Lemma lem2305489 (y : int) : term29 y.
Proof. exact (@lem2305488 (real_of_int y)). Qed.
Lemma lem2305490 (y : int) : (term29 y) = (term30 y).
Proof. exact (eq_refl (term29 y)). Qed.
Lemma lem2305491 (y : int) : term30 y.
Proof. exact (EQ_MP (@lem2305490 y) (@lem2305489 y)). Qed.
Lemma lem2305492 (y : int) (x : int) : term31 y x.
Proof. exact (@lem2305491 y (real_of_int x)). Qed.
Lemma lem2305493 (y : int) (x : int) : (term31 y x) = (term32 y x).
Proof. exact (eq_refl (term31 y x)). Qed.
Lemma lem2305494 (y : int) (x : int) : term32 y x.
Proof. exact (EQ_MP (@lem2305493 y x) (@lem2305492 y x)). Qed.
Lemma lem2305495 (y : int) (x : int) (z : int) : term33 y x z.
Proof. exact (@lem2305494 y x (real_of_int z)). Qed.
Lemma lem2305496 (y : int) (x : int) (z : int) : (term33 y x z) = ((term34 x y z) = (term34 y x z)).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem2305497 (y : int) (x : int) (z : int) : (term34 x y z) = (term34 y x z).
Proof. exact (EQ_MP (@lem2305496 y x z) (@lem2305495 y x z)). Qed.
Lemma lem2305499 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305500 (y : int) (z : int) : (term10 y z) = (term11 y z).
Proof. exact (@lem2305499 y z). Qed.
Lemma lem2305501 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305502 (x : int) (y : int) (z : int) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem2305501 x) (@lem2305500 y z)). Qed.
Lemma lem2305504 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305505 (x : int) (y : int) (z : int) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem2305504 x (int_min y z)). Qed.
Lemma lem2305506 (x : int) (y : int) (z : int) : (term34 x y z) = (term36 x y z).
Proof. exact (TRANS (@lem2305502 x y z) (@lem2305505 x y z)). Qed.
Lemma lem2305507 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305508 (x : int) (y : int) (z : int) : (term37 x y z) = (term38 x y z).
Proof. exact (MK_COMB (@lem2305507) (@lem2305506 x y z)). Qed.
Lemma lem2305510 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305511 (x : int) (z : int) : (term10 x z) = (term11 x z).
Proof. exact (@lem2305510 x z). Qed.
Lemma lem2305512 (y : int) : (term12 y) = (term12 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem2305513 (y : int) (x : int) (z : int) : (term34 y x z) = (term35 y x z).
Proof. exact (MK_COMB (@lem2305512 y) (@lem2305511 x z)). Qed.
Lemma lem2305515 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305516 (y : int) (x : int) (z : int) : (term35 y x z) = (term36 y x z).
Proof. exact (@lem2305515 y (int_min x z)). Qed.
Lemma lem2305517 (y : int) (x : int) (z : int) : (term34 y x z) = (term36 y x z).
Proof. exact (TRANS (@lem2305513 y x z) (@lem2305516 y x z)). Qed.
Lemma lem2305518 (y : int) (x : int) (z : int) : ((term34 x y z) = (term34 y x z)) = ((term36 x y z) = (term36 y x z)).
Proof. exact (MK_COMB (@lem2305508 x y z) (@lem2305517 y x z)). Qed.
Lemma lem2305520 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305521 (y : int) (x : int) (z : int) : ((term36 x y z) = (term36 y x z)) = ((term39 x y z) = (term39 y x z)).
Proof. exact (@lem2305520 (term39 x y z) (term39 y x z)). Qed.
Lemma lem2305522 (y : int) (x : int) (z : int) : ((term34 x y z) = (term34 y x z)) = ((term39 x y z) = (term39 y x z)).
Proof. exact (TRANS (@lem2305518 y x z) (@lem2305521 y x z)). Qed.
Lemma lem2305523 (y : int) (x : int) (z : int) : (term39 x y z) = (term39 y x z).
Proof. exact (EQ_MP (@lem2305522 y x z) (@lem2305497 y x z)). Qed.
Lemma lem2305524 (z : int) (x : int) (y : int) : term40 z x y.
Proof. exact (conj (@lem2305523 y x z) (@lem2305484 x y)). Qed.
Lemma lem2305525 (x : real) (y : real) (z : real) : (term41 x y z) = (term25 x y z).
Proof. exact (proj1 (@lem2305437 z x y)). Qed.
Lemma lem2305526 (x : real) (y : real) : term42 x y.
Proof. exact (fun z : real => @lem2305525 x y z). Qed.
Lemma lem2305527 (x : real) : term43 x.
Proof. exact (fun y : real => @lem2305526 x y). Qed.
Lemma lem2305528 : term44.
Proof. exact (fun x : real => @lem2305527 x). Qed.
Lemma lem2305529 (x : int) : term45 x.
Proof. exact (@lem2305528 (real_of_int x)). Qed.
Lemma lem2305530 (x : int) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2305531 (x : int) : term46 x.
Proof. exact (EQ_MP (@lem2305530 x) (@lem2305529 x)). Qed.
Lemma lem2305532 (x : int) (y : int) : term47 x y.
Proof. exact (@lem2305531 x (real_of_int y)). Qed.
Lemma lem2305533 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem2305534 (x : int) (y : int) : term48 x y.
Proof. exact (EQ_MP (@lem2305533 x y) (@lem2305532 x y)). Qed.
Lemma lem2305535 (x : int) (y : int) (z : int) : term49 x y z.
Proof. exact (@lem2305534 x y (real_of_int z)). Qed.
Lemma lem2305536 (x : int) (y : int) (z : int) : (term49 x y z) = ((term50 x y z) = (term34 x y z)).
Proof. exact (eq_refl (term49 x y z)). Qed.
Lemma lem2305537 (x : int) (y : int) (z : int) : (term50 x y z) = (term34 x y z).
Proof. exact (EQ_MP (@lem2305536 x y z) (@lem2305535 x y z)). Qed.
Lemma lem2305539 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305540 : real_min = real_min.
Proof. exact (eq_refl real_min). Qed.
Lemma lem2305541 (x : int) (y : int) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem2305540) (@lem2305539 x y)). Qed.
Lemma lem2305542 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305543 (x : int) (y : int) (z : int) : (term50 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem2305541 x y) (@lem2305542 z)). Qed.
Lemma lem2305545 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305546 (x : int) (y : int) (z : int) : (term53 x y z) = (term54 x y z).
Proof. exact (@lem2305545 (int_min x y) z). Qed.
Lemma lem2305547 (x : int) (y : int) (z : int) : (term50 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem2305543 x y z) (@lem2305546 x y z)). Qed.
Lemma lem2305548 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305549 (x : int) (y : int) (z : int) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem2305548) (@lem2305547 x y z)). Qed.
Lemma lem2305551 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305552 (y : int) (z : int) : (term10 y z) = (term11 y z).
Proof. exact (@lem2305551 y z). Qed.
Lemma lem2305553 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305554 (x : int) (y : int) (z : int) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem2305553 x) (@lem2305552 y z)). Qed.
Lemma lem2305556 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305557 (x : int) (y : int) (z : int) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem2305556 x (int_min y z)). Qed.
Lemma lem2305558 (x : int) (y : int) (z : int) : (term34 x y z) = (term36 x y z).
Proof. exact (TRANS (@lem2305554 x y z) (@lem2305557 x y z)). Qed.
Lemma lem2305559 (x : int) (y : int) (z : int) : ((term50 x y z) = (term34 x y z)) = ((term54 x y z) = (term36 x y z)).
Proof. exact (MK_COMB (@lem2305549 x y z) (@lem2305558 x y z)). Qed.
Lemma lem2305561 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305562 (x : int) (y : int) (z : int) : ((term54 x y z) = (term36 x y z)) = ((term57 x y z) = (term39 x y z)).
Proof. exact (@lem2305561 (term57 x y z) (term39 x y z)). Qed.
Lemma lem2305563 (x : int) (y : int) (z : int) : ((term50 x y z) = (term34 x y z)) = ((term57 x y z) = (term39 x y z)).
Proof. exact (TRANS (@lem2305559 x y z) (@lem2305562 x y z)). Qed.
Lemma lem2305564 (x : int) (y : int) (z : int) : (term57 x y z) = (term39 x y z).
Proof. exact (EQ_MP (@lem2305563 x y z) (@lem2305537 x y z)). Qed.
Lemma lem2305565 (z : int) (x : int) (y : int) : term58 z x y.
Proof. exact (conj (@lem2305564 x y z) (@lem2305524 z x y)). Qed.
Lemma lem2305566 (y : real) (x : real) : (real_min x y) = (real_min y x).
Proof. exact (proj1 (@lem1581662 (@el real) x y)). Qed.
Lemma lem2305567 (y : real) : term59 y.
Proof. exact (fun x : real => @lem2305566 y x). Qed.
Lemma lem2305568 : term60.
Proof. exact (fun y : real => @lem2305567 y). Qed.
Lemma lem2305569 (y : int) : term61 y.
Proof. exact (@lem2305568 (real_of_int y)). Qed.
Lemma lem2305570 (y : int) : (term61 y) = (term62 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem2305571 (y : int) : term62 y.
Proof. exact (EQ_MP (@lem2305570 y) (@lem2305569 y)). Qed.
Lemma lem2305572 (y : int) (x : int) : term63 y x.
Proof. exact (@lem2305571 y (real_of_int x)). Qed.
Lemma lem2305573 (y : int) (x : int) : (term63 y x) = ((term10 x y) = (term10 y x)).
Proof. exact (eq_refl (term63 y x)). Qed.
Lemma lem2305574 (y : int) (x : int) : (term10 x y) = (term10 y x).
Proof. exact (EQ_MP (@lem2305573 y x) (@lem2305572 y x)). Qed.
Lemma lem2305576 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305577 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305578 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem2305577) (@lem2305576 x y)). Qed.
Lemma lem2305580 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305581 (y : int) (x : int) : (term10 y x) = (term11 y x).
Proof. exact (@lem2305580 y x). Qed.
Lemma lem2305582 (y : int) (x : int) : ((term10 x y) = (term10 y x)) = ((term11 x y) = (term11 y x)).
Proof. exact (MK_COMB (@lem2305578 x y) (@lem2305581 y x)). Qed.
Lemma lem2305584 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305585 (y : int) (x : int) : ((term11 x y) = (term11 y x)) = ((int_min x y) = (int_min y x)).
Proof. exact (@lem2305584 (int_min x y) (int_min y x)). Qed.
Lemma lem2305586 (y : int) (x : int) : ((term10 x y) = (term10 y x)) = ((int_min x y) = (int_min y x)).
Proof. exact (TRANS (@lem2305582 y x) (@lem2305585 y x)). Qed.
Lemma lem2305587 (y : int) (x : int) : (int_min x y) = (int_min y x).
Proof. exact (EQ_MP (@lem2305586 y x) (@lem2305574 y x)). Qed.
Lemma lem2305588 (z : int) (x : int) (y : int) : term66 z x y.
Proof. exact (conj (@lem2305587 y x) (@lem2305565 z x y)). Qed.
