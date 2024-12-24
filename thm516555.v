Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516555_term_abbrevs.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import ODD_spec.
Require Import ODD_ADD_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem516375 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516376 : (NUMERAL 0) = 0.
Proof. exact (@lem516375 0). Qed.
Lemma lem516377 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem516378 : term0 = (Coq.Arith.PeanoNat.Nat.Odd 0).
Proof. exact (MK_COMB (@lem516377) (@lem516376)). Qed.
Lemma lem516379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516380 : term1 = term2.
Proof. exact (MK_COMB (@lem516379) (@lem516378)). Qed.
Lemma lem516381 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem516382 : (term0 = False) = ((Coq.Arith.PeanoNat.Nat.Odd 0) = False).
Proof. exact (MK_COMB (@lem516380) (@lem516381)). Qed.
Lemma lem516383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516384 : term3 = term4.
Proof. exact (MK_COMB (@lem516383) (@lem516382)). Qed.
Lemma lem516385 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem516386 : term6 = term7.
Proof. exact (MK_COMB (@lem516384) (@lem516385)). Qed.
Lemma lem516387 : term7.
Proof. exact (EQ_MP (@lem516386) (@lem124619)). Qed.
Lemma lem516388 (m : nat) : term8 m.
Proof. exact (@lem127895 m). Qed.
Lemma lem516389 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem516390 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem516389 m) (@lem516388 m)). Qed.
Lemma lem516391 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem516390 m n). Qed.
Lemma lem516392 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (term12 m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem516394 : term5.
Proof. exact (proj2 (@lem516387)). Qed.
Lemma lem516395 (n : nat) : term13 n.
Proof. exact (@lem516394 n). Qed.
Lemma lem516396 (n : nat) : (term13 n) = ((term14 n) = (term15 n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem516399 (n : nat) : term16 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem516400 (n : nat) : (term16 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem516402 (n : nat) : term17 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem516403 (n : nat) : (term17 n) = ((BIT1 n) = (term18 n)).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem516405 (n : nat) : term19 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem516406 (n : nat) : (term19 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem516417 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516406 n) (@lem516405 n)). Qed.
Lemma lem516418 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem516419 (n : nat) : (term20 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (MK_COMB (@lem516418) (@lem516417 n)). Qed.
Lemma lem516420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516421 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem516420) (@lem516419 n)). Qed.
Lemma lem516422 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem516423 (n : nat) : ((term20 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (MK_COMB (@lem516421 n) (@lem516422 n)). Qed.
Lemma lem516425 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516426 (x : Prop) : (x = x) = True.
Proof. exact (@lem516425 Prop x). Qed.
Lemma lem516427 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = True.
Proof. exact (@lem516426 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem516428 (n : nat) : ((term20 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = True.
Proof. exact (TRANS (@lem516423 n) (@lem516427 n)). Qed.
Lemma lem516429 : term23 = term24.
Proof. exact (fun_ext (fun n : nat => @lem516428 n)). Qed.
Lemma lem516430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516431 : term25 = term26.
Proof. exact (MK_COMB (@lem516430) (@lem516429)). Qed.
Lemma lem516433 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516434 (t : Prop) : (term28 t) = t.
Proof. exact (@lem516433 nat t). Qed.
Lemma lem516435 : term26 = True.
Proof. exact (@lem516434 True). Qed.
Lemma lem516436 : term25 = True.
Proof. exact (TRANS (@lem516431) (@lem516435)). Qed.
Lemma lem516437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516438 : term29 = (and True).
Proof. exact (MK_COMB (@lem516437) (@lem516436)). Qed.
Lemma lem516442 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem516443 : ((Coq.Arith.PeanoNat.Nat.Odd 0) = False) = term30.
Proof. exact (@lem516442 (Coq.Arith.PeanoNat.Nat.Odd 0)). Qed.
Lemma lem516445 : (Coq.Arith.PeanoNat.Nat.Odd 0) = False.
Proof. exact (proj1 (@lem516387)). Qed.
Lemma lem516446 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516447 : term30 = (~ False).
Proof. exact (MK_COMB (@lem516446) (@lem516445)). Qed.
Lemma lem516449 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem516450 : term30 = True.
Proof. exact (TRANS (@lem516447) (@lem516449)). Qed.
Lemma lem516451 : ((Coq.Arith.PeanoNat.Nat.Odd 0) = False) = True.
Proof. exact (TRANS (@lem516443) (@lem516450)). Qed.
Lemma lem516452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516453 : term4 = (and True).
Proof. exact (MK_COMB (@lem516452) (@lem516451)). Qed.
Lemma lem516461 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem516462 (n : nat) : ((term31 n) = False) = (term32 n).
Proof. exact (@lem516461 (term31 n)). Qed.
Lemma lem516464 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516400 n) (@lem516399 n)). Qed.
Lemma lem516465 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem516466 (n : nat) : (term31 n) = (term33 n).
Proof. exact (MK_COMB (@lem516465) (@lem516464 n)). Qed.
Lemma lem516468 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (EQ_MP (@lem516392 m n) (@lem516391 m n)). Qed.
Lemma lem516469 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem516468 n n). Qed.
Lemma lem516471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516472 (x : Prop) : (x = x) = True.
Proof. exact (@lem516471 Prop x). Qed.
Lemma lem516473 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = True.
Proof. exact (@lem516472 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem516474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516475 (n : nat) : (term34 n) = (~ True).
Proof. exact (MK_COMB (@lem516474) (@lem516473 n)). Qed.
Lemma lem516477 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem516478 (n : nat) : (term34 n) = False.
Proof. exact (TRANS (@lem516475 n) (@lem516477)). Qed.
Lemma lem516479 (n : nat) : (term33 n) = False.
Proof. exact (TRANS (@lem516469 n) (@lem516478 n)). Qed.
Lemma lem516480 (n : nat) : (term31 n) = False.
Proof. exact (TRANS (@lem516466 n) (@lem516479 n)). Qed.
Lemma lem516481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516482 (n : nat) : (term32 n) = (~ False).
Proof. exact (MK_COMB (@lem516481) (@lem516480 n)). Qed.
Lemma lem516484 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem516485 (n : nat) : (term32 n) = True.
Proof. exact (TRANS (@lem516482 n) (@lem516484)). Qed.
Lemma lem516486 (n : nat) : ((term31 n) = False) = True.
Proof. exact (TRANS (@lem516462 n) (@lem516485 n)). Qed.
Lemma lem516487 : term35 = term24.
Proof. exact (fun_ext (fun n : nat => @lem516486 n)). Qed.
Lemma lem516488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516489 : term36 = term26.
Proof. exact (MK_COMB (@lem516488) (@lem516487)). Qed.
Lemma lem516491 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516492 (t : Prop) : (term28 t) = t.
Proof. exact (@lem516491 nat t). Qed.
Lemma lem516493 : term26 = True.
Proof. exact (@lem516492 True). Qed.
Lemma lem516494 : term36 = True.
Proof. exact (TRANS (@lem516489) (@lem516493)). Qed.
Lemma lem516495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516496 : term37 = (and True).
Proof. exact (MK_COMB (@lem516495) (@lem516494)). Qed.
Lemma lem516502 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem516503 (n : nat) : ((term38 n) = True) = (term38 n).
Proof. exact (@lem516502 (term38 n)). Qed.
Lemma lem516505 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem516403 n) (@lem516402 n)). Qed.
Lemma lem516506 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem516507 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem516506) (@lem516505 n)). Qed.
Lemma lem516509 (n : nat) : (term14 n) = (term15 n).
Proof. exact (EQ_MP (@lem516396 n) (@lem516395 n)). Qed.
Lemma lem516510 (n : nat) : (term39 n) = (term40 n).
Proof. exact (@lem516509 (Nat.add n n)). Qed.
Lemma lem516512 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (EQ_MP (@lem516392 m n) (@lem516391 m n)). Qed.
Lemma lem516513 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem516512 n n). Qed.
Lemma lem516515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516516 (x : Prop) : (x = x) = True.
Proof. exact (@lem516515 Prop x). Qed.
Lemma lem516517 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = True.
Proof. exact (@lem516516 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem516518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516519 (n : nat) : (term34 n) = (~ True).
Proof. exact (MK_COMB (@lem516518) (@lem516517 n)). Qed.
Lemma lem516521 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem516522 (n : nat) : (term34 n) = False.
Proof. exact (TRANS (@lem516519 n) (@lem516521)). Qed.
Lemma lem516523 (n : nat) : (term33 n) = False.
Proof. exact (TRANS (@lem516513 n) (@lem516522 n)). Qed.
Lemma lem516524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516525 (n : nat) : (term40 n) = (~ False).
Proof. exact (MK_COMB (@lem516524) (@lem516523 n)). Qed.
Lemma lem516527 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem516528 (n : nat) : (term40 n) = True.
Proof. exact (TRANS (@lem516525 n) (@lem516527)). Qed.
Lemma lem516529 (n : nat) : (term39 n) = True.
Proof. exact (TRANS (@lem516510 n) (@lem516528 n)). Qed.
Lemma lem516530 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem516507 n) (@lem516529 n)). Qed.
Lemma lem516531 (n : nat) : ((term38 n) = True) = True.
Proof. exact (TRANS (@lem516503 n) (@lem516530 n)). Qed.
Lemma lem516532 : term41 = term24.
Proof. exact (fun_ext (fun n : nat => @lem516531 n)). Qed.
Lemma lem516533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516534 : term42 = term26.
Proof. exact (MK_COMB (@lem516533) (@lem516532)). Qed.
Lemma lem516536 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516537 (t : Prop) : (term28 t) = t.
Proof. exact (@lem516536 nat t). Qed.
Lemma lem516538 : term26 = True.
Proof. exact (@lem516537 True). Qed.
Lemma lem516539 : term42 = True.
Proof. exact (TRANS (@lem516534) (@lem516538)). Qed.
Lemma lem516540 : term43 = (True /\ True).
Proof. exact (MK_COMB (@lem516496) (@lem516539)). Qed.
Lemma lem516542 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516543 : (True /\ True) = True.
Proof. exact (@lem516542 True). Qed.
Lemma lem516544 : term43 = True.
Proof. exact (TRANS (@lem516540) (@lem516543)). Qed.
Lemma lem516545 : term44 = (True /\ True).
Proof. exact (MK_COMB (@lem516453) (@lem516544)). Qed.
Lemma lem516547 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516548 : (True /\ True) = True.
Proof. exact (@lem516547 True). Qed.
Lemma lem516549 : term44 = True.
Proof. exact (TRANS (@lem516545) (@lem516548)). Qed.
Lemma lem516550 : term45 = (True /\ True).
Proof. exact (MK_COMB (@lem516438) (@lem516549)). Qed.
Lemma lem516552 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516553 : (True /\ True) = True.
Proof. exact (@lem516552 True). Qed.
Lemma lem516554 : term45 = True.
Proof. exact (TRANS (@lem516550) (@lem516553)). Qed.
Lemma lem516555 : True = term45.
Proof. exact (SYM (@lem516554)). Qed.
