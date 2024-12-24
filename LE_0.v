Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem91417 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem91418 : term1.
Proof. exact (@lem91417 term2). Qed.
Lemma lem91419 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem91420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem91421 : term5 = term6.
Proof. exact (MK_COMB (@lem91420) (@lem91419)). Qed.
Lemma lem91422 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem91423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91424 (n : nat) : (term9 n) = (term10 n).
Proof. exact (MK_COMB (@lem91423) (@lem91422 n)). Qed.
Lemma lem91425 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem91426 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem91424 n) (@lem91425 n)). Qed.
Lemma lem91427 : term15 = term16.
Proof. exact (fun_ext (fun n : nat => @lem91426 n)). Qed.
Lemma lem91428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91429 : term17 = term18.
Proof. exact (MK_COMB (@lem91428) (@lem91427)). Qed.
Lemma lem91430 : term19 = term20.
Proof. exact (MK_COMB (@lem91421) (@lem91429)). Qed.
Lemma lem91431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91432 : term21 = term22.
Proof. exact (MK_COMB (@lem91431) (@lem91430)). Qed.
Lemma lem91433 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem91434 : term23 = term2.
Proof. exact (fun_ext (fun n : nat => @lem91433 n)). Qed.
Lemma lem91435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91436 : term24 = term25.
Proof. exact (MK_COMB (@lem91435) (@lem91434)). Qed.
Lemma lem91437 : term1 = term26.
Proof. exact (MK_COMB (@lem91432) (@lem91436)). Qed.
Lemma lem91438 : term26.
Proof. exact (EQ_MP (@lem91437) (@lem91418)). Qed.
Lemma lem91439 (n : nat) (h1 : term8 n) : term8 n.
Proof. exact (h1). Qed.
Lemma lem91447 : term27.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem91448 (m : nat) : term28 m.
Proof. exact (@lem91447 m). Qed.
Lemma lem91449 (m : nat) : (term28 m) = ((term29 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem91452 (m : nat) : (term29 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem91449 m) (@lem91448 m)). Qed.
Lemma lem91453 : term4 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem91452 (NUMERAL 0)). Qed.
Lemma lem91455 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91456 (x : nat) : (x = x) = True.
Proof. exact (@lem91455 nat x). Qed.
Lemma lem91457 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem91456 (NUMERAL 0)). Qed.
Lemma lem91458 : term4 = True.
Proof. exact (TRANS (@lem91453) (@lem91457)). Qed.
Lemma lem91459 : True = term4.
Proof. exact (SYM (@lem91458)). Qed.
Lemma lem91460 : term4.
Proof. exact (EQ_MP (@lem91459) (@lem0)). Qed.
Lemma lem91461 : term30.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem91462 (m : nat) : term31 m.
Proof. exact (@lem91461 m). Qed.
Lemma lem91463 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem91464 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem91463 m) (@lem91462 m)). Qed.
Lemma lem91465 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem91464 m n). Qed.
Lemma lem91466 (m : nat) (n : nat) : (term33 m n) = ((term34 m n) = (term35 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem91472 (n : nat) : (term8 n) = ((term8 n) = True).
Proof. exact (@lem7 (term8 n)). Qed.
Lemma lem91475 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (EQ_MP (@lem91466 m n) (@lem91465 m n)). Qed.
Lemma lem91476 (n : nat) : (term12 n) = (term36 n).
Proof. exact (@lem91475 (NUMERAL 0) n). Qed.
Lemma lem91482 (n : nat) (h1 : term8 n) : (term8 n) = True.
Proof. exact (EQ_MP (@lem91472 n) (@lem91439 n h1)). Qed.
Lemma lem91483 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem91484 (n : nat) (h1 : term8 n) : (term36 n) = (term38 n).
Proof. exact (MK_COMB (@lem91483 n) (@lem91482 n h1)). Qed.
Lemma lem91486 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem91487 (n : nat) : (term38 n) = True.
Proof. exact (@lem91486 ((NUMERAL 0) = (S n))). Qed.
Lemma lem91488 (n : nat) (h1 : term8 n) : (term36 n) = True.
Proof. exact (TRANS (@lem91484 n h1) (@lem91487 n)). Qed.
Lemma lem91489 (n : nat) (h1 : term8 n) : (term12 n) = True.
Proof. exact (TRANS (@lem91476 n) (@lem91488 n h1)). Qed.
Lemma lem91490 (n : nat) (h1 : term8 n) : True = (term12 n).
Proof. exact (SYM (@lem91489 n h1)). Qed.
Lemma lem91491 (n : nat) (h1 : term8 n) : term12 n.
Proof. exact (EQ_MP (@lem91490 n h1) (@lem0)). Qed.
Lemma lem91492 (n : nat) : term14 n.
Proof. exact (fun h0 : term8 n => @lem91491 n h0). Qed.
Lemma lem91497 : term18.
Proof. exact (fun n : nat => @lem91492 n). Qed.
Lemma lem91498 : term20.
Proof. exact (conj (@lem91460) (@lem91497)). Qed.
Lemma lem91499 : term25.
Proof. exact (@lem91438 (@lem91498)). Qed.
