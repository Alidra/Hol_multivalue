Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_LE_term_abbrevs.
Require Import LE_LT_spec.
Require Import LT_REFL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem97339 (n : nat) : term0 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem97340 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem97341 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem97340 n) (@lem97339 n)). Qed.
Lemma lem97342 (n : nat) : term2 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem97344 (m : nat) : term3 m.
Proof. exact (@lem97338 m). Qed.
Lemma lem97345 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem97346 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem97345 m) (@lem97344 m)). Qed.
Lemma lem97347 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem97346 m n). Qed.
Lemma lem97348 (m : nat) (n : nat) : (term5 m n) = ((Peano.le m n) = (term6 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem97363 (m : nat) (n : nat) : (Peano.le m n) = (term6 m n).
Proof. exact (EQ_MP (@lem97348 m n) (@lem97347 m n)). Qed.
Lemma lem97368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97369 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem97368) (@lem97363 m n)). Qed.
Lemma lem97372 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem97373 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem97369 m n) (@lem97372 m n)). Qed.
Lemma lem97376 (m : nat) (n : nat) : (term12 m n) = (term12 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem97377 (m : nat) (n : nat) : ((Peano.lt m n) = (term10 m n)) = ((Peano.lt m n) = (term11 m n)).
Proof. exact (MK_COMB (@lem97376 m n) (@lem97373 m n)). Qed.
Lemma lem97380 (m : nat) : (term13 m) = (term14 m).
Proof. exact (fun_ext (fun n : nat => @lem97377 m n)). Qed.
Lemma lem97381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97382 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem97381) (@lem97380 m)). Qed.
Lemma lem97387 : term17 = term18.
Proof. exact (fun_ext (fun m : nat => @lem97382 m)). Qed.
Lemma lem97388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97389 : term19 = term20.
Proof. exact (MK_COMB (@lem97388) (@lem97387)). Qed.
Lemma lem97394 : term20 = term19.
Proof. exact (SYM (@lem97389)). Qed.
Lemma lem97395 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem97396 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem97403 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem97396 m n) (@lem97395 m n h1)). Qed.
Lemma lem97404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem97405 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term21 m n) = (or True).
Proof. exact (MK_COMB (@lem97404) (@lem97403 m n h1)). Qed.
Lemma lem97408 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem97409 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term6 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem97405 m n h1) (@lem97408 m n)). Qed.
Lemma lem97411 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem97412 (m : nat) (n : nat) : (term22 m n) = True.
Proof. exact (@lem97411 (m = n)). Qed.
Lemma lem97413 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term6 m n) = True.
Proof. exact (TRANS (@lem97409 m n h1) (@lem97412 m n)). Qed.
Lemma lem97414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97415 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term8 m n) = (and True).
Proof. exact (MK_COMB (@lem97414) (@lem97413 m n h1)). Qed.
Lemma lem97418 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem97419 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term11 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem97415 m n h1) (@lem97418 m n)). Qed.
Lemma lem97421 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem97422 (m : nat) (n : nat) : (term23 m n) = (term9 m n).
Proof. exact (@lem97421 (term9 m n)). Qed.
Lemma lem97425 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term11 m n) = (term9 m n).
Proof. exact (TRANS (@lem97419 m n h1) (@lem97422 m n)). Qed.
Lemma lem97426 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term9 m n) = (term11 m n).
Proof. exact (SYM (@lem97425 m n h1)). Qed.
Lemma lem97427 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem97442 (n : nat) : (term24 n) = (term24 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem97443 (m : nat) (n : nat) (h1 : m = n) : (term25 n m) = (term26 n).
Proof. exact (MK_COMB (@lem97442 n) (@lem97427 m n h1)). Qed.
Lemma lem97444 (n : nat) : (term26 n) = (Peano.lt n n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem97445 (n : nat) (m : nat) : (term27 n m) = (term27 n m).
Proof. exact (eq_refl (term27 n m)). Qed.
Lemma lem97446 (m : nat) (n : nat) : ((term25 n m) = (term26 n)) = ((term25 n m) = (Peano.lt n n)).
Proof. exact (MK_COMB (@lem97445 n m) (@lem97444 n)). Qed.
Lemma lem97447 (m : nat) (n : nat) : (term25 n m) = (Peano.lt m n).
Proof. exact (eq_refl (term25 n m)). Qed.
Lemma lem97448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97449 (m : nat) (n : nat) : (term27 n m) = (term12 m n).
Proof. exact (MK_COMB (@lem97448) (@lem97447 m n)). Qed.
Lemma lem97450 (n : nat) : (Peano.lt n n) = (Peano.lt n n).
Proof. exact (eq_refl (Peano.lt n n)). Qed.
Lemma lem97451 (m : nat) (n : nat) : ((term25 n m) = (Peano.lt n n)) = ((Peano.lt m n) = (Peano.lt n n)).
Proof. exact (MK_COMB (@lem97449 m n) (@lem97450 n)). Qed.
Lemma lem97452 (m : nat) (n : nat) : ((term25 n m) = (term26 n)) = ((Peano.lt m n) = (Peano.lt n n)).
Proof. exact (TRANS (@lem97446 m n) (@lem97451 m n)). Qed.
Lemma lem97453 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m n) = (Peano.lt n n).
Proof. exact (EQ_MP (@lem97452 m n) (@lem97443 m n h1)). Qed.
Lemma lem97454 (m : nat) (n : nat) (h1 : Peano.lt m n) (h2 : m = n) : Peano.lt n n.
Proof. exact (EQ_MP (@lem97453 m n h2) (@lem97395 m n h1)). Qed.
Lemma lem97456 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem97457 (n : nat) : (term28 n) = (term1 n).
Proof. exact (@lem97456 (Peano.lt n n)). Qed.
Lemma lem97459 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem97342 n (@lem97341 n)). Qed.
Lemma lem97460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97461 (n : nat) : (term1 n) = (~ False).
Proof. exact (MK_COMB (@lem97460) (@lem97459 n)). Qed.
Lemma lem97463 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem97464 (n : nat) : (term1 n) = True.
Proof. exact (TRANS (@lem97461 n) (@lem97463)). Qed.
Lemma lem97465 (n : nat) : (term28 n) = True.
Proof. exact (TRANS (@lem97457 n) (@lem97464 n)). Qed.
Lemma lem97466 (n : nat) : True = (term28 n).
Proof. exact (SYM (@lem97465 n)). Qed.
Lemma lem97467 (n : nat) : term28 n.
Proof. exact (EQ_MP (@lem97466 n) (@lem0)). Qed.
Lemma lem97469 (m : nat) (n : nat) (h1 : Peano.lt m n) (h2 : m = n) : False.
Proof. exact (@lem97467 n (@lem97454 m n h1 h2)). Qed.
Lemma lem97470 (m : nat) (n : nat) (h1 : Peano.lt m n) : term29 m n.
Proof. exact (fun h0 : m = n => @lem97469 m n h1 h0). Qed.
Lemma lem97471 (m : nat) (n : nat) : (term29 m n) = (term9 m n).
Proof. exact (@lem69 (m = n)). Qed.
Lemma lem97472 (m : nat) (n : nat) (h1 : Peano.lt m n) : term9 m n.
Proof. exact (EQ_MP (@lem97471 m n) (@lem97470 m n h1)). Qed.
Lemma lem97473 (m : nat) (n : nat) (h1 : Peano.lt m n) : term11 m n.
Proof. exact (EQ_MP (@lem97426 m n h1) (@lem97472 m n h1)). Qed.
Lemma lem97474 (m : nat) (n : nat) : term30 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem97473 m n h0). Qed.
Lemma lem97475 (m : nat) (n : nat) (h1 : term11 m n) : term11 m n.
Proof. exact (h1). Qed.
Lemma lem97476 (m : nat) (n : nat) (h1 : term9 m n) : term9 m n.
Proof. exact (h1). Qed.
Lemma lem97477 (m : nat) (n : nat) (h1 : term6 m n) : term6 m n.
Proof. exact (h1). Qed.
Lemma lem97478 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem97479 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem97485 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem97486 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem97487 (m : nat) (n : nat) (h1 : m = n) : (@eq nat m) = (@eq nat n).
Proof. exact (MK_COMB (@lem97486) (@lem97485 m n h1)). Qed.
Lemma lem97488 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem97489 (m : nat) (n : nat) (h1 : m = n) : (m = n) = (n = n).
Proof. exact (MK_COMB (@lem97487 m n h1) (@lem97488 n)). Qed.
Lemma lem97491 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97492 (x : nat) : (x = x) = True.
Proof. exact (@lem97491 nat x). Qed.
Lemma lem97493 (n : nat) : (n = n) = True.
Proof. exact (@lem97492 n). Qed.
Lemma lem97494 (m : nat) (n : nat) (h1 : m = n) : (m = n) = True.
Proof. exact (TRANS (@lem97489 m n h1) (@lem97493 n)). Qed.
Lemma lem97495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97496 (m : nat) (n : nat) (h1 : m = n) : (term9 m n) = (~ True).
Proof. exact (MK_COMB (@lem97495) (@lem97494 m n h1)). Qed.
Lemma lem97498 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem97499 (m : nat) (n : nat) (h1 : m = n) : (term9 m n) = False.
Proof. exact (TRANS (@lem97496 m n h1) (@lem97498)). Qed.
Lemma lem97500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97501 (m : nat) (n : nat) (h1 : m = n) : (term31 m n) = (imp False).
Proof. exact (MK_COMB (@lem97500) (@lem97499 m n h1)). Qed.
Lemma lem97503 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem97504 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem97505 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m) = (Peano.lt n).
Proof. exact (MK_COMB (@lem97504) (@lem97503 m n h1)). Qed.
Lemma lem97506 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem97507 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m n) = (Peano.lt n n).
Proof. exact (MK_COMB (@lem97505 m n h1) (@lem97506 n)). Qed.
Lemma lem97508 (m : nat) (n : nat) (h1 : m = n) : (term32 m n) = (term33 n).
Proof. exact (MK_COMB (@lem97501 m n h1) (@lem97507 m n h1)). Qed.
Lemma lem97510 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem97511 (n : nat) : (term33 n) = True.
Proof. exact (@lem97510 (Peano.lt n n)). Qed.
Lemma lem97512 (m : nat) (n : nat) (h1 : m = n) : (term32 m n) = True.
Proof. exact (TRANS (@lem97508 m n h1) (@lem97511 n)). Qed.
Lemma lem97513 (m : nat) (n : nat) (h1 : m = n) : True = (term32 m n).
Proof. exact (SYM (@lem97512 m n h1)). Qed.
Lemma lem97514 (m : nat) (n : nat) (h1 : m = n) : term32 m n.
Proof. exact (EQ_MP (@lem97513 m n h1) (@lem0)). Qed.
Lemma lem97515 (m : nat) (n : nat) (h1 : term11 m n) : term9 m n.
Proof. exact (proj2 (@lem97475 m n h1)). Qed.
Lemma lem97516 (m : nat) (n : nat) (h1 : term11 m n) : term6 m n.
Proof. exact (proj1 (@lem97475 m n h1)). Qed.
Lemma lem97517 (m : nat) (n : nat) (h1 : term9 m n) (h2 : m = n) : Peano.lt m n.
Proof. exact (@lem97514 m n h2 (@lem97476 m n h1)). Qed.
Lemma lem97518 (m : nat) (n : nat) (h1 : term9 m n) (h2 : m = n) : (m = n) = (Peano.lt m n).
Proof. exact (prop_ext (fun h3 : m = n => @lem97517 m n h1 h2) (fun h3 : Peano.lt m n => @lem97479 m n h2)). Qed.
Lemma lem97519 (m : nat) (n : nat) (h1 : term9 m n) (h2 : m = n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem97518 m n h1 h2) (@lem97479 m n h2)). Qed.
Lemma lem97520 (m : nat) (n : nat) (h1 : term9 m n) (h2 : term6 m n) : Peano.lt m n.
Proof. exact (or_elim (@lem97477 m n h2) (fun h0 : Peano.lt m n => @lem97478 m n h0) (fun h0 : m = n => @lem97519 m n h1 h0)). Qed.
Lemma lem97521 (m : nat) (n : nat) (h1 : term11 m n) (h2 : term6 m n) : (term9 m n) = (Peano.lt m n).
Proof. exact (prop_ext (fun h3 : term9 m n => @lem97520 m n h3 h2) (fun h3 : Peano.lt m n => @lem97515 m n h1)). Qed.
Lemma lem97522 (m : nat) (n : nat) (h1 : term11 m n) (h2 : term6 m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem97521 m n h1 h2) (@lem97515 m n h1)). Qed.
Lemma lem97523 (m : nat) (n : nat) (h1 : term11 m n) : (term6 m n) = (Peano.lt m n).
Proof. exact (prop_ext (fun h2 : term6 m n => @lem97522 m n h1 h2) (fun h2 : Peano.lt m n => @lem97516 m n h1)). Qed.
Lemma lem97524 (m : nat) (n : nat) (h1 : term11 m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem97523 m n h1) (@lem97516 m n h1)). Qed.
Lemma lem97525 (m : nat) (n : nat) : term34 m n.
Proof. exact (fun h0 : term11 m n => @lem97524 m n h0). Qed.
Lemma lem97526 (m : nat) (n : nat) : term35 m n.
Proof. exact (conj (@lem97474 m n) (@lem97525 m n)). Qed.
Lemma lem97527 (m : nat) (n : nat) : (term35 m n) = ((Peano.lt m n) = (term11 m n)).
Proof. exact (@lem32 (Peano.lt m n) (term11 m n)). Qed.
Lemma lem97528 (m : nat) (n : nat) : (Peano.lt m n) = (term11 m n).
Proof. exact (EQ_MP (@lem97527 m n) (@lem97526 m n)). Qed.
Lemma lem97533 (m : nat) : term16 m.
Proof. exact (fun n : nat => @lem97528 m n). Qed.
Lemma lem97538 : term20.
Proof. exact (fun m : nat => @lem97533 m). Qed.
Lemma lem97539 : term19.
Proof. exact (EQ_MP (@lem97394) (@lem97538)). Qed.
