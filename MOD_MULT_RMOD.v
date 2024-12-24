Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT_RMOD_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DIVISION_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MOD_EQ_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem205348 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem205349 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem205350 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem205349 m) (@lem205348 m)). Qed.
Lemma lem205351 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem205350 m n). Qed.
Lemma lem205352 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem205354 (m : nat) : term3 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem205355 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem205356 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem205355 m) (@lem205354 m)). Qed.
Lemma lem205357 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem205356 m n). Qed.
Lemma lem205358 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem205359 (m : nat) (n : nat) : term6 m n.
Proof. exact (EQ_MP (@lem205358 m n) (@lem205357 m n)). Qed.
Lemma lem205360 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (@lem205359 m n p). Qed.
Lemma lem205361 (m : nat) (n : nat) (p : nat) : (term7 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term8 m n p)).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem205366 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term9 m n p) = (term10 n m p).
Proof. exact (h1). Qed.
Lemma lem205367 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term10 n m p) = (term9 m n p).
Proof. exact (SYM (@lem205366 n m p h1)). Qed.
Lemma lem205368 (m : nat) (n : nat) (p : nat) (h1 : (term10 n m p) = (term9 m n p)) : (term10 n m p) = (term9 m n p).
Proof. exact (h1). Qed.
Lemma lem205369 (m : nat) (n : nat) (p : nat) (h1 : (term10 n m p) = (term9 m n p)) : (term9 m n p) = (term10 n m p).
Proof. exact (SYM (@lem205368 m n p h1)). Qed.
Lemma lem205370 (m : nat) (n : nat) (p : nat) : ((term9 m n p) = (term10 n m p)) = ((term10 n m p) = (term9 m n p)).
Proof. exact (prop_ext (fun h1 : (term9 m n p) = (term10 n m p) => @lem205367 n m p h1) (fun h1 : (term10 n m p) = (term9 m n p) => @lem205369 m n p h1)). Qed.
Lemma lem205371 (m : nat) (n : nat) : (term11 n m) = (term12 m n).
Proof. exact (fun_ext (fun p : nat => @lem205370 m n p)). Qed.
Lemma lem205372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205373 (m : nat) (n : nat) : (term13 n m) = (term14 m n).
Proof. exact (MK_COMB (@lem205372) (@lem205371 m n)). Qed.
Lemma lem205374 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem205373 m n)). Qed.
Lemma lem205375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205376 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem205375) (@lem205374 m)). Qed.
Lemma lem205377 : term19 = term20.
Proof. exact (fun_ext (fun m : nat => @lem205376 m)). Qed.
Lemma lem205378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205379 : term21 = term22.
Proof. exact (MK_COMB (@lem205378) (@lem205377)). Qed.
Lemma lem205380 : term22.
Proof. exact (EQ_MP (@lem205379) (@lem82055)). Qed.
Lemma lem205384 (m : nat) (n : nat) (p : nat) (h1 : (term23 m n p) = (term24 m n p)) : (term23 m n p) = (term24 m n p).
Proof. exact (h1). Qed.
Lemma lem205385 (m : nat) (n : nat) (p : nat) (h1 : (term23 m n p) = (term24 m n p)) : (term24 m n p) = (term23 m n p).
Proof. exact (SYM (@lem205384 m n p h1)). Qed.
Lemma lem205386 (m : nat) (n : nat) (p : nat) (h1 : (term24 m n p) = (term23 m n p)) : (term24 m n p) = (term23 m n p).
Proof. exact (h1). Qed.
Lemma lem205387 (m : nat) (n : nat) (p : nat) (h1 : (term24 m n p) = (term23 m n p)) : (term23 m n p) = (term24 m n p).
Proof. exact (SYM (@lem205386 m n p h1)). Qed.
Lemma lem205388 (m : nat) (n : nat) (p : nat) : ((term23 m n p) = (term24 m n p)) = ((term24 m n p) = (term23 m n p)).
Proof. exact (prop_ext (fun h1 : (term23 m n p) = (term24 m n p) => @lem205385 m n p h1) (fun h1 : (term24 m n p) = (term23 m n p) => @lem205387 m n p h1)). Qed.
Lemma lem205389 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (fun_ext (fun p : nat => @lem205388 m n p)). Qed.
Lemma lem205390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205391 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem205390) (@lem205389 m n)). Qed.
Lemma lem205392 (m : nat) : (term29 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem205391 m n)). Qed.
Lemma lem205393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205394 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem205393) (@lem205392 m)). Qed.
Lemma lem205395 : term33 = term34.
Proof. exact (fun_ext (fun m : nat => @lem205394 m)). Qed.
Lemma lem205396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205397 : term35 = term36.
Proof. exact (MK_COMB (@lem205396) (@lem205395)). Qed.
Lemma lem205398 : term36.
Proof. exact (EQ_MP (@lem205397) (@lem82357)). Qed.
Lemma lem205399 (m : nat) : term37 m.
Proof. exact (@lem205380 m). Qed.
Lemma lem205400 (m : nat) : (term37 m) = (term18 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem205401 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem205400 m) (@lem205399 m)). Qed.
Lemma lem205402 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem205401 m n). Qed.
Lemma lem205403 (m : nat) (n : nat) : (term38 m n) = (term14 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem205404 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem205403 m n) (@lem205402 m n)). Qed.
Lemma lem205405 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (@lem205404 m n p). Qed.
Lemma lem205406 (m : nat) (n : nat) (p : nat) : (term39 m n p) = ((term10 n m p) = (term9 m n p)).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem205408 (m : nat) : term40 m.
Proof. exact (@lem205398 m). Qed.
Lemma lem205409 (m : nat) : (term40 m) = (term32 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem205410 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem205409 m) (@lem205408 m)). Qed.
Lemma lem205411 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem205410 m n). Qed.
Lemma lem205412 (m : nat) (n : nat) : (term41 m n) = (term28 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem205413 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem205412 m n) (@lem205411 m n)). Qed.
Lemma lem205414 (m : nat) (n : nat) (p : nat) : term42 m n p.
Proof. exact (@lem205413 m n p). Qed.
Lemma lem205415 (m : nat) (n : nat) (p : nat) : (term42 m n p) = ((term24 m n p) = (term23 m n p)).
Proof. exact (eq_refl (term42 m n p)). Qed.
Lemma lem205417 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem205418 (m : nat) (h1 : term43) : term44 m.
Proof. exact (@lem205417 h1 m). Qed.
Lemma lem205419 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem205420 (m : nat) (h1 : term43) : term45 m.
Proof. exact (EQ_MP (@lem205419 m) (@lem205418 m h1)). Qed.
Lemma lem205421 (m : nat) (n : nat) (h1 : term43) : term46 m n.
Proof. exact (@lem205420 m h1 n). Qed.
Lemma lem205422 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem205423 (m : nat) (n : nat) (h1 : term43) : term47 m n.
Proof. exact (EQ_MP (@lem205422 m n) (@lem205421 m n h1)). Qed.
Lemma lem205424 (m : nat) (n : nat) (p : nat) (h1 : term43) : term48 m n p.
Proof. exact (@lem205423 m n h1 p). Qed.
Lemma lem205425 (m : nat) (n : nat) (p : nat) : (term48 m n p) = (term49 m n p).
Proof. exact (eq_refl (term48 m n p)). Qed.
Lemma lem205426 (m : nat) (n : nat) (p : nat) (h1 : term43) : term49 m n p.
Proof. exact (EQ_MP (@lem205425 m n p) (@lem205424 m n p h1)). Qed.
Lemma lem205427 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term43) : term50 m n p q.
Proof. exact (@lem205426 m n p h1 q). Qed.
Lemma lem205428 (q : nat) (m : nat) (n : nat) (p : nat) : (term50 m n p q) = (term51 q m n p).
Proof. exact (eq_refl (term50 m n p q)). Qed.
Lemma lem205429 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : term43) : term51 q m n p.
Proof. exact (EQ_MP (@lem205428 q m n p) (@lem205427 m n p q h1)). Qed.
Lemma lem205430 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term52 n q p)) : m = (term52 n q p).
Proof. exact (h1). Qed.
Lemma lem205431 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : term43) (h2 : m = (term52 n q p)) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem205429 q m n p h1 (@lem205430 m n q p h2)). Qed.
Lemma lem205432 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term52 n q p)) : term53 m n p.
Proof. exact (fun h0 : term43 => @lem205431 m n q p h0 h1). Qed.
Lemma lem205433 (m : nat) (n : nat) (p : nat) (h1 : term54 m n p) : term54 m n p.
Proof. exact (h1). Qed.
Lemma lem205434 (m : nat) (n : nat) (p : nat) (h1 : term54 m n p) : term53 m n p.
Proof. exact (ex_elim (@lem205433 m n p h1) (fun q : nat => fun h0 : term55 m n p q => @lem205432 m n q p h0)). Qed.
Lemma lem205435 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem205436 (m : nat) (n : nat) (p : nat) (h1 : term43) (h2 : term54 m n p) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem205434 m n p h2 (@lem205435 h1)). Qed.
Lemma lem205437 (m : nat) (n : nat) (p : nat) (h1 : term43) : term56 m n p.
Proof. exact (fun h0 : term54 m n p => @lem205436 m n p h1 h0). Qed.
Lemma lem205438 (m : nat) (n : nat) (h1 : term43) : term57 m n.
Proof. exact (fun p : nat => @lem205437 m n p h1). Qed.
Lemma lem205439 (m : nat) (h1 : term43) : term58 m.
Proof. exact (fun n : nat => @lem205438 m n h1). Qed.
Lemma lem205440 (h1 : term43) : term59.
Proof. exact (fun m : nat => @lem205439 m h1). Qed.
Lemma lem205441 : term60.
Proof. exact (fun h0 : term43 => @lem205440 h0). Qed.
Lemma lem205442 : term59.
Proof. exact (@lem205441 (@lem178251)). Qed.
Lemma lem205443 (m : nat) : term61 m.
Proof. exact (@lem205442 m). Qed.
Lemma lem205444 (m : nat) : (term61 m) = (term58 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem205445 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem205444 m) (@lem205443 m)). Qed.
Lemma lem205446 (m : nat) (n : nat) : term62 m n.
Proof. exact (@lem205445 m n). Qed.
Lemma lem205447 (m : nat) (n : nat) : (term62 m n) = (term57 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem205448 (m : nat) (n : nat) : term57 m n.
Proof. exact (EQ_MP (@lem205447 m n) (@lem205446 m n)). Qed.
Lemma lem205449 (m : nat) (n : nat) (p : nat) : term63 m n p.
Proof. exact (@lem205448 m n p). Qed.
Lemma lem205450 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term56 m n p).
Proof. exact (eq_refl (term63 m n p)). Qed.
Lemma lem205452 (n : nat) : term64 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem205453 (n : nat) : (term64 n) = (term65 n).
Proof. exact (eq_refl (term64 n)). Qed.
Lemma lem205454 (n : nat) : term65 n.
Proof. exact (EQ_MP (@lem205453 n) (@lem205452 n)). Qed.
Lemma lem205456 (n : nat) (h1 : term66 n) : term66 n.
Proof. exact (h1). Qed.
Lemma lem205457 (n : nat) : term67 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem205458 (n : nat) : (term67 n) = ((term68 n) = n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem205463 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205464 (p : nat) : (Nat.modulo p) = (Nat.modulo p).
Proof. exact (eq_refl (Nat.modulo p)). Qed.
Lemma lem205465 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo p n) = (term68 p).
Proof. exact (MK_COMB (@lem205464 p) (@lem205463 n h1)). Qed.
Lemma lem205467 (n : nat) : (term68 n) = n.
Proof. exact (EQ_MP (@lem205458 n) (@lem205457 n)). Qed.
Lemma lem205468 (p : nat) : (term68 p) = p.
Proof. exact (@lem205467 p). Qed.
Lemma lem205469 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo p n) = p.
Proof. exact (TRANS (@lem205465 p n h1) (@lem205468 p)). Qed.
Lemma lem205470 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem205471 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term69 m p n) = (Nat.mul m p).
Proof. exact (MK_COMB (@lem205470 m) (@lem205469 p n h1)). Qed.
Lemma lem205472 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205473 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term70 m p n) = (term71 m p).
Proof. exact (MK_COMB (@lem205472) (@lem205471 m p n h1)). Qed.
Lemma lem205475 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205476 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term72 m p n) = (term73 m p).
Proof. exact (MK_COMB (@lem205473 m p n h1) (@lem205475 n h1)). Qed.
Lemma lem205478 (n : nat) : (term68 n) = n.
Proof. exact (EQ_MP (@lem205458 n) (@lem205457 n)). Qed.
Lemma lem205479 (m : nat) (p : nat) : (term73 m p) = (Nat.mul m p).
Proof. exact (@lem205478 (Nat.mul m p)). Qed.
Lemma lem205480 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term72 m p n) = (Nat.mul m p).
Proof. exact (TRANS (@lem205476 m p n h1) (@lem205479 m p)). Qed.
Lemma lem205481 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205482 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term74 m p n) = (term75 m p).
Proof. exact (MK_COMB (@lem205481) (@lem205480 m p n h1)). Qed.
Lemma lem205484 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem205485 (m : nat) (p : nat) : (term71 m p) = (term71 m p).
Proof. exact (eq_refl (term71 m p)). Qed.
Lemma lem205486 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term76 m p n) = (term73 m p).
Proof. exact (MK_COMB (@lem205485 m p) (@lem205484 n h1)). Qed.
Lemma lem205488 (n : nat) : (term68 n) = n.
Proof. exact (EQ_MP (@lem205458 n) (@lem205457 n)). Qed.
Lemma lem205489 (m : nat) (p : nat) : (term73 m p) = (Nat.mul m p).
Proof. exact (@lem205488 (Nat.mul m p)). Qed.
Lemma lem205490 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term76 m p n) = (Nat.mul m p).
Proof. exact (TRANS (@lem205486 m p n h1) (@lem205489 m p)). Qed.
Lemma lem205491 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term72 m p n) = (term76 m p n)) = ((Nat.mul m p) = (Nat.mul m p)).
Proof. exact (MK_COMB (@lem205482 m p n h1) (@lem205490 m p n h1)). Qed.
Lemma lem205493 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem205494 (x : nat) : (x = x) = True.
Proof. exact (@lem205493 nat x). Qed.
Lemma lem205495 (m : nat) (p : nat) : ((Nat.mul m p) = (Nat.mul m p)) = True.
Proof. exact (@lem205494 (Nat.mul m p)). Qed.
Lemma lem205496 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term72 m p n) = (term76 m p n)) = True.
Proof. exact (TRANS (@lem205491 m p n h1) (@lem205495 m p)). Qed.
Lemma lem205497 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term72 m p n) = (term76 m p n)).
Proof. exact (SYM (@lem205496 m p n h1)). Qed.
Lemma lem205498 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term72 m p n) = (term76 m p n).
Proof. exact (EQ_MP (@lem205497 m p n h1) (@lem0)). Qed.
Lemma lem205519 (m : nat) (p : nat) (n : nat) (h1 : (term72 m p n) = (term76 m p n)) : (term72 m p n) = (term76 m p n).
Proof. exact (h1). Qed.
Lemma lem205520 (m : nat) (p : nat) (n : nat) (h1 : (term72 m p n) = (term76 m p n)) : (term76 m p n) = (term72 m p n).
Proof. exact (SYM (@lem205519 m p n h1)). Qed.
Lemma lem205521 (m : nat) (p : nat) (n : nat) (h1 : (term76 m p n) = (term72 m p n)) : (term76 m p n) = (term72 m p n).
Proof. exact (h1). Qed.
Lemma lem205522 (m : nat) (p : nat) (n : nat) (h1 : (term76 m p n) = (term72 m p n)) : (term72 m p n) = (term76 m p n).
Proof. exact (SYM (@lem205521 m p n h1)). Qed.
Lemma lem205523 (m : nat) (p : nat) (n : nat) : ((term72 m p n) = (term76 m p n)) = ((term76 m p n) = (term72 m p n)).
Proof. exact (prop_ext (fun h1 : (term72 m p n) = (term76 m p n) => @lem205520 m p n h1) (fun h1 : (term76 m p n) = (term72 m p n) => @lem205522 m p n h1)). Qed.
Lemma lem205524 (m : nat) (p : nat) (n : nat) : ((term76 m p n) = (term72 m p n)) = ((term72 m p n) = (term76 m p n)).
Proof. exact (SYM (@lem205523 m p n)). Qed.
Lemma lem205526 (m : nat) (n : nat) (p : nat) : term56 m n p.
Proof. exact (EQ_MP (@lem205450 m n p) (@lem205449 m n p)). Qed.
Lemma lem205527 (m : nat) (p : nat) (n : nat) : term77 m p n.
Proof. exact (@lem205526 (Nat.mul m p) (term69 m p n) n). Qed.
Lemma lem205533 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term23 m n p).
Proof. exact (EQ_MP (@lem205415 m n p) (@lem205414 m n p)). Qed.
Lemma lem205534 (m : nat) (p : nat) (n : nat) : (term78 m p n) = (term79 m p n).
Proof. exact (@lem205533 m (Nat.div p n) n). Qed.
Lemma lem205535 (m : nat) (p : nat) (n : nat) : (term80 m p n) = (term80 m p n).
Proof. exact (eq_refl (term80 m p n)). Qed.
Lemma lem205536 (m : nat) (p : nat) (n : nat) : (term81 m p n) = (term82 m p n).
Proof. exact (MK_COMB (@lem205535 m p n) (@lem205534 m p n)). Qed.
Lemma lem205538 (m : nat) (n : nat) (p : nat) : (term10 n m p) = (term9 m n p).
Proof. exact (EQ_MP (@lem205406 m n p) (@lem205405 m n p)). Qed.
Lemma lem205539 (m : nat) (p : nat) (n : nat) : (term82 m p n) = (term83 m p n).
Proof. exact (@lem205538 m (Nat.modulo p n) (term84 p n)). Qed.
Lemma lem205540 (m : nat) (p : nat) (n : nat) : (term81 m p n) = (term83 m p n).
Proof. exact (TRANS (@lem205536 m p n) (@lem205539 m p n)). Qed.
Lemma lem205541 (m : nat) (p : nat) : (term75 m p) = (term75 m p).
Proof. exact (eq_refl (term75 m p)). Qed.
Lemma lem205542 (m : nat) (p : nat) (n : nat) : ((Nat.mul m p) = (term81 m p n)) = ((Nat.mul m p) = (term83 m p n)).
Proof. exact (MK_COMB (@lem205541 m p) (@lem205540 m p n)). Qed.
Lemma lem205545 (m : nat) (p : nat) (n : nat) : ((Nat.mul m p) = (term83 m p n)) = ((Nat.mul m p) = (term81 m p n)).
Proof. exact (SYM (@lem205542 m p n)). Qed.
Lemma lem205547 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term8 m n p).
Proof. exact (EQ_MP (@lem205361 m n p) (@lem205360 m n p)). Qed.
Lemma lem205548 (m : nat) (p : nat) (n : nat) : ((Nat.mul m p) = (term83 m p n)) = (term85 m p n).
Proof. exact (@lem205547 m p (term86 p n)). Qed.
Lemma lem205555 (m : nat) (p : nat) (n : nat) : (term85 m p n) = ((Nat.mul m p) = (term83 m p n)).
Proof. exact (SYM (@lem205548 m p n)). Qed.
Lemma lem205559 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem205352 n m) (@lem205351 m n)). Qed.
Lemma lem205560 (p : nat) (n : nat) : (term86 p n) = (term87 p n).
Proof. exact (@lem205559 (term84 p n) (Nat.modulo p n)). Qed.
Lemma lem205561 (p : nat) : (@eq nat p) = (@eq nat p).
Proof. exact (eq_refl (@eq nat p)). Qed.
Lemma lem205562 (p : nat) (n : nat) : (p = (term86 p n)) = (p = (term87 p n)).
Proof. exact (MK_COMB (@lem205561 p) (@lem205560 p n)). Qed.
Lemma lem205563 (p : nat) (n : nat) : (p = (term87 p n)) = (p = (term86 p n)).
Proof. exact (SYM (@lem205562 p n)). Qed.
Lemma lem205564 (m : nat) : term88 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem205565 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem205566 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem205565 m) (@lem205564 m)). Qed.
Lemma lem205567 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem205566 m n). Qed.
Lemma lem205568 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem205569 (m : nat) (n : nat) : term91 m n.
Proof. exact (EQ_MP (@lem205568 m n) (@lem205567 m n)). Qed.
Lemma lem205570 (n : nat) (h1 : term66 n) : term66 n.
Proof. exact (h1). Qed.
Lemma lem205571 (m : nat) (n : nat) (h1 : term66 n) : term92 m n.
Proof. exact (@lem205569 m n (@lem205570 n h1)). Qed.
Lemma lem205580 (m : nat) (n : nat) (h1 : term66 n) : m = (term87 m n).
Proof. exact (proj1 (@lem205571 m n h1)). Qed.
Lemma lem205585 (m : nat) (n : nat) : term93 m n.
Proof. exact (fun h0 : term66 n => @lem205580 m n h0). Qed.
Lemma lem205586 (n : nat) (h1 : term66 n) : term66 n.
Proof. exact (h1). Qed.
Lemma lem205587 (m : nat) (n : nat) (h1 : term66 n) : m = (term87 m n).
Proof. exact (@lem205585 m n (@lem205586 n h1)). Qed.
Lemma lem205588 (m : nat) (n : nat) : (m = (term87 m n)) = ((m = (term87 m n)) = True).
Proof. exact (@lem7 (m = (term87 m n))). Qed.
Lemma lem205589 (m : nat) (n : nat) (h1 : term66 n) : (m = (term87 m n)) = True.
Proof. exact (EQ_MP (@lem205588 m n) (@lem205587 m n h1)). Qed.
Lemma lem205591 (n : nat) : term94 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem205607 (m : nat) (n : nat) : term95 m n.
Proof. exact (fun h0 : term66 n => @lem205589 m n h0). Qed.
Lemma lem205608 (p : nat) (n : nat) : term95 p n.
Proof. exact (@lem205607 p n). Qed.
Lemma lem205614 (n : nat) (h1 : term66 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem205591 n (@lem205456 n h1)). Qed.
Lemma lem205617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem205618 (n : nat) (h1 : term66 n) : (term66 n) = (~ False).
Proof. exact (MK_COMB (@lem205617) (@lem205614 n h1)). Qed.
Lemma lem205620 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem205623 (n : nat) (h1 : term66 n) : (term66 n) = True.
Proof. exact (TRANS (@lem205618 n h1) (@lem205620)). Qed.
Lemma lem205624 (n : nat) (h1 : term66 n) : True = (term66 n).
Proof. exact (SYM (@lem205623 n h1)). Qed.
Lemma lem205625 (n : nat) (h1 : term66 n) : term66 n.
Proof. exact (EQ_MP (@lem205624 n h1) (@lem0)). Qed.
Lemma lem205626 (p : nat) (n : nat) (h1 : term66 n) : (p = (term87 p n)) = True.
Proof. exact (@lem205608 p n (@lem205625 n h1)). Qed.
Lemma lem205629 (p : nat) (n : nat) (h1 : term66 n) : True = (p = (term87 p n)).
Proof. exact (SYM (@lem205626 p n h1)). Qed.
Lemma lem205630 (p : nat) (n : nat) (h1 : term66 n) : p = (term87 p n).
Proof. exact (EQ_MP (@lem205629 p n h1) (@lem0)). Qed.
Lemma lem205631 (p : nat) (n : nat) (h1 : term66 n) : p = (term86 p n).
Proof. exact (EQ_MP (@lem205563 p n) (@lem205630 p n h1)). Qed.
Lemma lem205632 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : term85 m p n.
Proof. exact (or_intro2 (m = (NUMERAL 0)) (@lem205631 p n h1)). Qed.
Lemma lem205633 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : (Nat.mul m p) = (term83 m p n).
Proof. exact (EQ_MP (@lem205555 m p n) (@lem205632 m p n h1)). Qed.
Lemma lem205634 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : (Nat.mul m p) = (term81 m p n).
Proof. exact (EQ_MP (@lem205545 m p n) (@lem205633 m p n h1)). Qed.
Lemma lem205635 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : term96 m p n.
Proof. exact (ex_intro (term97 m p n) (term98 m p n) (@lem205634 m p n h1)). Qed.
Lemma lem205636 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : (term76 m p n) = (term72 m p n).
Proof. exact (@lem205527 m p n (@lem205635 m p n h1)). Qed.
Lemma lem205638 (m : nat) (p : nat) (n : nat) (h1 : term66 n) : (term72 m p n) = (term76 m p n).
Proof. exact (EQ_MP (@lem205524 m p n) (@lem205636 m p n h1)). Qed.
Lemma lem205639 (m : nat) (p : nat) (n : nat) : (term72 m p n) = (term76 m p n).
Proof. exact (or_elim (@lem205454 n) (fun h0 : n = (NUMERAL 0) => @lem205498 m p n h0) (fun h0 : term66 n => @lem205638 m p n h0)). Qed.
Lemma lem205644 (m : nat) (n : nat) : term99 m n.
Proof. exact (fun p : nat => @lem205639 m p n). Qed.
Lemma lem205649 (m : nat) : term100 m.
Proof. exact (fun n : nat => @lem205644 m n). Qed.
Lemma lem205654 : term101.
Proof. exact (fun m : nat => @lem205649 m). Qed.
