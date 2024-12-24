Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LT_term_abbrevs.
Require Import REAL_LT_01_spec.
Require Import REAL_LT_MUL_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1582435 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1582436 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1582435 h1 x). Qed.
Lemma lem1582437 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1582438 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1582437 x) (@lem1582436 x h1)). Qed.
Lemma lem1582439 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1582438 x h1 y). Qed.
Lemma lem1582440 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1582441 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1582440 x y) (@lem1582439 x y h1)). Qed.
Lemma lem1582442 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1582443 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1582441 x y h1 (@lem1582442 x y h2)). Qed.
Lemma lem1582444 (x : real) (y : real) (h1 : term5 x y) : term7 x y.
Proof. exact (fun h0 : term0 => @lem1582443 x y h0 h1). Qed.
Lemma lem1582445 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1582446 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1582444 x y h2 (@lem1582445 h1)). Qed.
Lemma lem1582447 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : term5 x y => @lem1582446 x y h1 h0). Qed.
Lemma lem1582448 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1582447 x y h1). Qed.
Lemma lem1582449 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1582448 x h1). Qed.
Lemma lem1582450 : term8.
Proof. exact (fun h0 : term0 => @lem1582449 h0). Qed.
Lemma lem1582451 : term0.
Proof. exact (@lem1582450 (@lem1487565)). Qed.
Lemma lem1582452 (x : real) : term1 x.
Proof. exact (@lem1582451 x). Qed.
Lemma lem1582453 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1582454 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1582453 x) (@lem1582452 x)). Qed.
Lemma lem1582455 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1582454 x y). Qed.
Lemma lem1582456 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1582458 : term9 = (term9 = True).
Proof. exact (@lem7 term9). Qed.
Lemma lem1582460 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1582461 (x : real) (n : nat) : term11 x n.
Proof. exact (@lem1582460 x n). Qed.
Lemma lem1582462 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1582465 (x : real) (h1 : term14 x) : term14 x.
Proof. exact (h1). Qed.
Lemma lem1582467 (P : nat -> Prop) : term15 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1582468 (x : real) : term16 x.
Proof. exact (@lem1582467 (term17 x)). Qed.
Lemma lem1582469 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1582470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582471 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1582470) (@lem1582469 x)). Qed.
Lemma lem1582472 (x : real) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (eq_refl (term22 x n)). Qed.
Lemma lem1582473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582474 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1582473) (@lem1582472 x n)). Qed.
Lemma lem1582475 (x : real) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1582476 (x : real) (n : nat) : (term28 x n) = (term29 x n).
Proof. exact (MK_COMB (@lem1582474 x n) (@lem1582475 x n)). Qed.
Lemma lem1582477 (x : real) : (term30 x) = (term31 x).
Proof. exact (fun_ext (fun n : nat => @lem1582476 x n)). Qed.
Lemma lem1582478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582479 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1582478) (@lem1582477 x)). Qed.
Lemma lem1582480 (x : real) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1582471 x) (@lem1582479 x)). Qed.
Lemma lem1582481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582482 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1582481) (@lem1582480 x)). Qed.
Lemma lem1582483 (x : real) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (eq_refl (term22 x n)). Qed.
Lemma lem1582484 (x : real) : (term38 x) = (term17 x).
Proof. exact (fun_ext (fun n : nat => @lem1582483 x n)). Qed.
Lemma lem1582485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582486 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1582485) (@lem1582484 x)). Qed.
Lemma lem1582487 (x : real) : (term16 x) = (term41 x).
Proof. exact (MK_COMB (@lem1582482 x) (@lem1582486 x)). Qed.
Lemma lem1582488 (x : real) : term41 x.
Proof. exact (EQ_MP (@lem1582487 x) (@lem1582468 x)). Qed.
Lemma lem1582489 (x : real) (n : nat) (h1 : term23 x n) : term23 x n.
Proof. exact (h1). Qed.
Lemma lem1582491 (x : real) : (term42 x) = term43.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1582492 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1582493 (x : real) : (term19 x) = term9.
Proof. exact (MK_COMB (@lem1582492) (@lem1582491 x)). Qed.
Lemma lem1582495 : term9 = True.
Proof. exact (EQ_MP (@lem1582458) (@lem1499399)). Qed.
Lemma lem1582496 (x : real) : (term19 x) = True.
Proof. exact (TRANS (@lem1582493 x) (@lem1582495)). Qed.
Lemma lem1582497 (x : real) : True = (term19 x).
Proof. exact (SYM (@lem1582496 x)). Qed.
Lemma lem1582498 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1582497 x) (@lem0)). Qed.
Lemma lem1582500 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem1582462 x n) (@lem1582461 x n)). Qed.
Lemma lem1582501 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1582502 (x : real) (n : nat) : (term27 x n) = (term45 x n).
Proof. exact (MK_COMB (@lem1582501) (@lem1582500 x n)). Qed.
Lemma lem1582503 (x : real) (n : nat) : (term45 x n) = (term27 x n).
Proof. exact (SYM (@lem1582502 x n)). Qed.
Lemma lem1582505 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1582456 x y) (@lem1582455 x y)). Qed.
Lemma lem1582506 (x : real) (n : nat) : term46 x n.
Proof. exact (@lem1582505 x (real_pow x n)). Qed.
Lemma lem1582507 (x : real) : (term14 x) = ((term14 x) = True).
Proof. exact (@lem7 (term14 x)). Qed.
Lemma lem1582509 (x : real) (n : nat) : (term23 x n) = ((term23 x n) = True).
Proof. exact (@lem7 (term23 x n)). Qed.
Lemma lem1582514 (x : real) (h1 : term14 x) : (term14 x) = True.
Proof. exact (EQ_MP (@lem1582507 x) (@lem1582465 x h1)). Qed.
Lemma lem1582515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582516 (x : real) (h1 : term14 x) : (term47 x) = (and True).
Proof. exact (MK_COMB (@lem1582515) (@lem1582514 x h1)). Qed.
Lemma lem1582518 (x : real) (n : nat) (h1 : term23 x n) : (term23 x n) = True.
Proof. exact (EQ_MP (@lem1582509 x n) (@lem1582489 x n h1)). Qed.
Lemma lem1582519 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : (term48 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1582516 x h1) (@lem1582518 x n h2)). Qed.
Lemma lem1582521 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1582522 : (True /\ True) = True.
Proof. exact (@lem1582521 True). Qed.
Lemma lem1582523 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : (term48 x n) = True.
Proof. exact (TRANS (@lem1582519 x n h1 h2) (@lem1582522)). Qed.
Lemma lem1582524 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : True = (term48 x n).
Proof. exact (SYM (@lem1582523 x n h1 h2)). Qed.
Lemma lem1582525 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : term48 x n.
Proof. exact (EQ_MP (@lem1582524 x n h1 h2) (@lem0)). Qed.
Lemma lem1582526 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : term45 x n.
Proof. exact (@lem1582506 x n (@lem1582525 x n h1 h2)). Qed.
Lemma lem1582527 (x : real) (n : nat) (h1 : term14 x) (h2 : term23 x n) : term27 x n.
Proof. exact (EQ_MP (@lem1582503 x n) (@lem1582526 x n h1 h2)). Qed.
Lemma lem1582528 (n : nat) (x : real) (h1 : term14 x) : term29 x n.
Proof. exact (fun h0 : term23 x n => @lem1582527 x n h1 h0). Qed.
Lemma lem1582533 (x : real) (h1 : term14 x) : term33 x.
Proof. exact (fun n : nat => @lem1582528 n x h1). Qed.
Lemma lem1582534 (x : real) (h1 : term14 x) : term35 x.
Proof. exact (conj (@lem1582498 x) (@lem1582533 x h1)). Qed.
Lemma lem1582535 (x : real) (h1 : term14 x) : term40 x.
Proof. exact (@lem1582488 x (@lem1582534 x h1)). Qed.
Lemma lem1582536 (n : nat) (x : real) (h1 : term14 x) : term22 x n.
Proof. exact (@lem1582535 x h1 n). Qed.
Lemma lem1582537 (x : real) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (eq_refl (term22 x n)). Qed.
Lemma lem1582538 (n : nat) (x : real) (h1 : term14 x) : term23 x n.
Proof. exact (EQ_MP (@lem1582537 x n) (@lem1582536 n x h1)). Qed.
Lemma lem1582539 (n : nat) (x : real) (h1 : term14 x) : (term14 x) = (term23 x n).
Proof. exact (prop_ext (fun h2 : term14 x => @lem1582538 n x h1) (fun h2 : term23 x n => @lem1582465 x h1)). Qed.
Lemma lem1582540 (n : nat) (x : real) (h1 : term14 x) : term23 x n.
Proof. exact (EQ_MP (@lem1582539 n x h1) (@lem1582465 x h1)). Qed.
Lemma lem1582541 (x : real) (n : nat) : term49 x n.
Proof. exact (fun h0 : term14 x => @lem1582540 n x h0). Qed.
Lemma lem1582546 (x : real) : term50 x.
Proof. exact (fun n : nat => @lem1582541 x n). Qed.
Lemma lem1582551 : term51.
Proof. exact (fun x : real => @lem1582546 x). Qed.
