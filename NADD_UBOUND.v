Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_UBOUND_term_abbrevs.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_BOUND_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1299408 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1299410 : term1.
Proof. exact (proj2 (@lem1299408)). Qed.
Lemma lem1299412 : term2.
Proof. exact (proj2 (@lem1299410)). Qed.
Lemma lem1299415 : term3.
Proof. exact (proj1 (@lem1299412)). Qed.
Lemma lem1299419 (m : nat) (h1 : (term4 m) = m) : (term4 m) = m.
Proof. exact (h1). Qed.
Lemma lem1299420 (m : nat) (h1 : (term4 m) = m) : m = (term4 m).
Proof. exact (SYM (@lem1299419 m h1)). Qed.
Lemma lem1299421 (m : nat) (h1 : m = (term4 m)) : m = (term4 m).
Proof. exact (h1). Qed.
Lemma lem1299422 (m : nat) (h1 : m = (term4 m)) : (term4 m) = m.
Proof. exact (SYM (@lem1299421 m h1)). Qed.
Lemma lem1299423 (m : nat) : ((term4 m) = m) = (m = (term4 m)).
Proof. exact (prop_ext (fun h1 : (term4 m) = m => @lem1299420 m h1) (fun h1 : m = (term4 m) => @lem1299422 m h1)). Qed.
Lemma lem1299424 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1299423 m)). Qed.
Lemma lem1299425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299426 : term3 = term7.
Proof. exact (MK_COMB (@lem1299425) (@lem1299424)). Qed.
Lemma lem1299427 : term7.
Proof. exact (EQ_MP (@lem1299426) (@lem1299415)). Qed.
Lemma lem1299428 (m : nat) : term8 m.
Proof. exact (@lem1299427 m). Qed.
Lemma lem1299429 (m : nat) : (term8 m) = (m = (term4 m)).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1299431 (m : nat) : term9 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1299432 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1299433 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1299432 m) (@lem1299431 m)). Qed.
Lemma lem1299434 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1299433 m n). Qed.
Lemma lem1299435 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1299436 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem1299435 m n) (@lem1299434 m n)). Qed.
Lemma lem1299437 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem1299436 m n p). Qed.
Lemma lem1299438 (m : nat) (n : nat) (p : nat) : (term13 m n p) = ((term14 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem1299440 (m : nat) : term15 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1299441 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1299442 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1299441 m) (@lem1299440 m)). Qed.
Lemma lem1299443 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1299442 m n). Qed.
Lemma lem1299444 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1299445 (m : nat) (n : nat) : term18 m n.
Proof. exact (EQ_MP (@lem1299444 m n) (@lem1299443 m n)). Qed.
Lemma lem1299446 (m : nat) (n : nat) (p : nat) : term19 m n p.
Proof. exact (@lem1299445 m n p). Qed.
Lemma lem1299447 (m : nat) (n : nat) (p : nat) : (term19 m n p) = ((term20 m n p) = (term21 m n p)).
Proof. exact (eq_refl (term19 m n p)). Qed.
Lemma lem1299449 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1299450 (m : nat) (h1 : term22) : term23 m.
Proof. exact (@lem1299449 h1 m). Qed.
Lemma lem1299451 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1299452 (m : nat) (h1 : term22) : term24 m.
Proof. exact (EQ_MP (@lem1299451 m) (@lem1299450 m h1)). Qed.
Lemma lem1299453 (m : nat) (n : nat) (h1 : term22) : term25 m n.
Proof. exact (@lem1299452 m h1 n). Qed.
Lemma lem1299454 (n : nat) (m : nat) : (term25 m n) = (term26 n m).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1299455 (n : nat) (m : nat) (h1 : term22) : term26 n m.
Proof. exact (EQ_MP (@lem1299454 n m) (@lem1299453 m n h1)). Qed.
Lemma lem1299456 (n : nat) (m : nat) (p : nat) (h1 : term22) : term27 n m p.
Proof. exact (@lem1299455 n m h1 p). Qed.
Lemma lem1299457 (n : nat) (m : nat) (p : nat) : (term27 n m p) = (term28 n m p).
Proof. exact (eq_refl (term27 n m p)). Qed.
Lemma lem1299458 (n : nat) (m : nat) (p : nat) (h1 : term22) : term28 n m p.
Proof. exact (EQ_MP (@lem1299457 n m p) (@lem1299456 n m p h1)). Qed.
Lemma lem1299459 (m : nat) (n : nat) (p : nat) (h1 : term29 m n p) : term29 m n p.
Proof. exact (h1). Qed.
Lemma lem1299460 (m : nat) (n : nat) (p : nat) (h1 : term22) (h2 : term29 m n p) : Peano.le m p.
Proof. exact (@lem1299458 n m p h1 (@lem1299459 m n p h2)). Qed.
Lemma lem1299461 (m : nat) (n : nat) (p : nat) (h1 : term29 m n p) : term30 m p.
Proof. exact (fun h0 : term22 => @lem1299460 m n p h0 h1). Qed.
Lemma lem1299462 (m : nat) (p : nat) (h1 : term31 m p) : term31 m p.
Proof. exact (h1). Qed.
Lemma lem1299463 (m : nat) (p : nat) (h1 : term31 m p) : term30 m p.
Proof. exact (ex_elim (@lem1299462 m p h1) (fun n : nat => fun h0 : term32 m p n => @lem1299461 m n p h0)). Qed.
Lemma lem1299464 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1299465 (m : nat) (p : nat) (h1 : term22) (h2 : term31 m p) : Peano.le m p.
Proof. exact (@lem1299463 m p h2 (@lem1299464 h1)). Qed.
Lemma lem1299466 (m : nat) (p : nat) (h1 : term22) : term33 m p.
Proof. exact (fun h0 : term31 m p => @lem1299465 m p h1 h0). Qed.
Lemma lem1299467 (m : nat) (h1 : term22) : term34 m.
Proof. exact (fun p : nat => @lem1299466 m p h1). Qed.
Lemma lem1299468 (h1 : term22) : term35.
Proof. exact (fun m : nat => @lem1299467 m h1). Qed.
Lemma lem1299469 : term36.
Proof. exact (fun h0 : term22 => @lem1299468 h0). Qed.
Lemma lem1299470 : term35.
Proof. exact (@lem1299469 (@lem93743)). Qed.
Lemma lem1299471 (m : nat) : term37 m.
Proof. exact (@lem1299470 m). Qed.
Lemma lem1299472 (m : nat) : (term37 m) = (term34 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1299473 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1299472 m) (@lem1299471 m)). Qed.
Lemma lem1299474 (m : nat) (p : nat) : term38 m p.
Proof. exact (@lem1299473 m p). Qed.
Lemma lem1299475 (m : nat) (p : nat) : (term38 m p) = (term33 m p).
Proof. exact (eq_refl (term38 m p)). Qed.
Lemma lem1299477 (x : nadd) : term39 x.
Proof. exact (@lem1263160 x). Qed.
Lemma lem1299478 (x : nadd) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1299479 (x : nadd) : term40 x.
Proof. exact (EQ_MP (@lem1299478 x) (@lem1299477 x)). Qed.
Lemma lem1299480 (x : nadd) (A1 : nat) (h1 : term41 x A1) : term41 x A1.
Proof. exact (h1). Qed.
Lemma lem1299481 (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term42 x A1 A2.
Proof. exact (h1). Qed.
Lemma lem1299482 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (h1). Qed.
Lemma lem1299484 (m : nat) (p : nat) : term33 m p.
Proof. exact (EQ_MP (@lem1299475 m p) (@lem1299474 m p)). Qed.
Lemma lem1299485 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) : term44 x A1 A2 n.
Proof. exact (@lem1299484 (dest_nadd x n) (term20 A1 A2 n)). Qed.
Lemma lem1299486 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term45 x A1 A2 n.
Proof. exact (@lem1299481 x A1 A2 h1 n). Qed.
Lemma lem1299487 (x : nadd) (A1 : nat) (n : nat) (A2 : nat) : (term45 x A1 A2 n) = (term46 x A1 n A2).
Proof. exact (eq_refl (term45 x A1 A2 n)). Qed.
Lemma lem1299488 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term46 x A1 n A2.
Proof. exact (EQ_MP (@lem1299487 x A1 n A2) (@lem1299486 n x A1 A2 h1)). Qed.
Lemma lem1299489 (x : nadd) (A1 : nat) (n : nat) (A2 : nat) : (term46 x A1 n A2) = ((term46 x A1 n A2) = True).
Proof. exact (@lem7 (term46 x A1 n A2)). Qed.
Lemma lem1299496 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : (term46 x A1 n A2) = True.
Proof. exact (EQ_MP (@lem1299489 x A1 n A2) (@lem1299488 n x A1 A2 h1)). Qed.
Lemma lem1299497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1299498 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : (term47 x A1 n A2) = (and True).
Proof. exact (MK_COMB (@lem1299497) (@lem1299496 n x A1 A2 h1)). Qed.
Lemma lem1299499 (A1 : nat) (A2 : nat) (n : nat) : (term48 A1 A2 n) = (term48 A1 A2 n).
Proof. exact (eq_refl (term48 A1 A2 n)). Qed.
Lemma lem1299500 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : (term49 x A1 A2 n) = (term50 A1 A2 n).
Proof. exact (MK_COMB (@lem1299498 n x A1 A2 h1) (@lem1299499 A1 A2 n)). Qed.
Lemma lem1299502 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1299503 (A1 : nat) (A2 : nat) (n : nat) : (term50 A1 A2 n) = (term48 A1 A2 n).
Proof. exact (@lem1299502 (term48 A1 A2 n)). Qed.
Lemma lem1299504 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : (term49 x A1 A2 n) = (term48 A1 A2 n).
Proof. exact (TRANS (@lem1299500 n x A1 A2 h1) (@lem1299503 A1 A2 n)). Qed.
Lemma lem1299505 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : (term48 A1 A2 n) = (term49 x A1 A2 n).
Proof. exact (SYM (@lem1299504 n x A1 A2 h1)). Qed.
Lemma lem1299507 (m : nat) (n : nat) (p : nat) : (term20 m n p) = (term21 m n p).
Proof. exact (EQ_MP (@lem1299447 m n p) (@lem1299446 m n p)). Qed.
Lemma lem1299508 (A1 : nat) (A2 : nat) (n : nat) : (term20 A1 A2 n) = (term21 A1 A2 n).
Proof. exact (@lem1299507 A1 A2 n). Qed.
Lemma lem1299509 (A1 : nat) (n : nat) (A2 : nat) : (term51 A1 n A2) = (term51 A1 n A2).
Proof. exact (eq_refl (term51 A1 n A2)). Qed.
Lemma lem1299510 (A1 : nat) (A2 : nat) (n : nat) : (term48 A1 A2 n) = (term52 A1 A2 n).
Proof. exact (MK_COMB (@lem1299509 A1 n A2) (@lem1299508 A1 A2 n)). Qed.
Lemma lem1299512 (m : nat) (n : nat) (p : nat) : (term14 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1299438 m n p) (@lem1299437 m n p)). Qed.
Lemma lem1299513 (A1 : nat) (A2 : nat) (n : nat) : (term52 A1 A2 n) = (term53 A2 n).
Proof. exact (@lem1299512 (Nat.mul A1 n) A2 (Nat.mul A2 n)). Qed.
Lemma lem1299514 (A1 : nat) (A2 : nat) (n : nat) : (term48 A1 A2 n) = (term53 A2 n).
Proof. exact (TRANS (@lem1299510 A1 A2 n) (@lem1299513 A1 A2 n)). Qed.
Lemma lem1299515 (A1 : nat) (A2 : nat) (n : nat) : (term53 A2 n) = (term48 A1 A2 n).
Proof. exact (SYM (@lem1299514 A1 A2 n)). Qed.
Lemma lem1299517 (m : nat) : m = (term4 m).
Proof. exact (EQ_MP (@lem1299429 m) (@lem1299428 m)). Qed.
Lemma lem1299518 (A2 : nat) : A2 = (term4 A2).
Proof. exact (@lem1299517 A2). Qed.
Lemma lem1299519 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1299520 (A2 : nat) : (Peano.le A2) = (term54 A2).
Proof. exact (MK_COMB (@lem1299519) (@lem1299518 A2)). Qed.
Lemma lem1299521 (A2 : nat) (n : nat) : (Nat.mul A2 n) = (Nat.mul A2 n).
Proof. exact (eq_refl (Nat.mul A2 n)). Qed.
Lemma lem1299522 (A2 : nat) (n : nat) : (term53 A2 n) = (term55 A2 n).
Proof. exact (MK_COMB (@lem1299520 A2) (@lem1299521 A2 n)). Qed.
Lemma lem1299523 (A2 : nat) (n : nat) : (term55 A2 n) = (term53 A2 n).
Proof. exact (SYM (@lem1299522 A2 n)). Qed.
Lemma lem1299524 (m : nat) : term56 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1299525 (m : nat) : (term56 m) = (term57 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem1299526 (m : nat) : term57 m.
Proof. exact (EQ_MP (@lem1299525 m) (@lem1299524 m)). Qed.
Lemma lem1299527 (m : nat) (n : nat) : term58 m n.
Proof. exact (@lem1299526 m n). Qed.
Lemma lem1299528 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem1299529 (m : nat) (n : nat) : term59 m n.
Proof. exact (EQ_MP (@lem1299528 m n) (@lem1299527 m n)). Qed.
Lemma lem1299530 (m : nat) (n : nat) (p : nat) : term60 m n p.
Proof. exact (@lem1299529 m n p). Qed.
Lemma lem1299531 (m : nat) (n : nat) (p : nat) : (term60 m n p) = ((term61 n m p) = (term62 m n p)).
Proof. exact (eq_refl (term60 m n p)). Qed.
Lemma lem1299538 (n : nat) : (term43 n) = ((term43 n) = True).
Proof. exact (@lem7 (term43 n)). Qed.
Lemma lem1299541 (m : nat) (n : nat) (p : nat) : (term61 n m p) = (term62 m n p).
Proof. exact (EQ_MP (@lem1299531 m n p) (@lem1299530 m n p)). Qed.
Lemma lem1299542 (A2 : nat) (n : nat) : (term55 A2 n) = (term63 A2 n).
Proof. exact (@lem1299541 A2 term64 n). Qed.
Lemma lem1299548 (n : nat) (h1 : term43 n) : (term43 n) = True.
Proof. exact (EQ_MP (@lem1299538 n) (@lem1299482 n h1)). Qed.
Lemma lem1299549 (A2 : nat) : (term65 A2) = (term65 A2).
Proof. exact (eq_refl (term65 A2)). Qed.
Lemma lem1299550 (A2 : nat) (n : nat) (h1 : term43 n) : (term63 A2 n) = (term66 A2).
Proof. exact (MK_COMB (@lem1299549 A2) (@lem1299548 n h1)). Qed.
Lemma lem1299552 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1299553 (A2 : nat) : (term66 A2) = True.
Proof. exact (@lem1299552 (A2 = (NUMERAL 0))). Qed.
Lemma lem1299554 (A2 : nat) (n : nat) (h1 : term43 n) : (term63 A2 n) = True.
Proof. exact (TRANS (@lem1299550 A2 n h1) (@lem1299553 A2)). Qed.
Lemma lem1299555 (A2 : nat) (n : nat) (h1 : term43 n) : (term55 A2 n) = True.
Proof. exact (TRANS (@lem1299542 A2 n) (@lem1299554 A2 n h1)). Qed.
Lemma lem1299556 (A2 : nat) (n : nat) (h1 : term43 n) : True = (term55 A2 n).
Proof. exact (SYM (@lem1299555 A2 n h1)). Qed.
Lemma lem1299557 (A2 : nat) (n : nat) (h1 : term43 n) : term55 A2 n.
Proof. exact (EQ_MP (@lem1299556 A2 n h1) (@lem0)). Qed.
Lemma lem1299558 (A2 : nat) (n : nat) (h1 : term43 n) : term53 A2 n.
Proof. exact (EQ_MP (@lem1299523 A2 n) (@lem1299557 A2 n h1)). Qed.
Lemma lem1299559 (A1 : nat) (A2 : nat) (n : nat) (h1 : term43 n) : term48 A1 A2 n.
Proof. exact (EQ_MP (@lem1299515 A1 A2 n) (@lem1299558 A2 n h1)). Qed.
Lemma lem1299560 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (h1 : term42 x A1 A2) (h2 : term43 n) : term49 x A1 A2 n.
Proof. exact (EQ_MP (@lem1299505 n x A1 A2 h1) (@lem1299559 A1 A2 n h2)). Qed.
Lemma lem1299561 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (h1 : term42 x A1 A2) (h2 : term43 n) : term67 x A1 A2 n.
Proof. exact (ex_intro (term68 x A1 A2 n) (term69 A1 n A2) (@lem1299560 x A1 A2 n h1 h2)). Qed.
Lemma lem1299562 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (h1 : term42 x A1 A2) (h2 : term43 n) : term70 x A1 A2 n.
Proof. exact (@lem1299485 x A1 A2 n (@lem1299561 x A1 A2 n h1 h2)). Qed.
Lemma lem1299563 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (h1 : term42 x A1 A2) (h2 : term43 n) : (term43 n) = (term70 x A1 A2 n).
Proof. exact (prop_ext (fun h3 : term43 n => @lem1299562 x A1 A2 n h1 h2) (fun h3 : term70 x A1 A2 n => @lem1299482 n h2)). Qed.
Lemma lem1299564 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (h1 : term42 x A1 A2) (h2 : term43 n) : term70 x A1 A2 n.
Proof. exact (EQ_MP (@lem1299563 x A1 A2 n h1 h2) (@lem1299482 n h2)). Qed.
Lemma lem1299565 (n : nat) (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term71 x A1 A2 n.
Proof. exact (fun h0 : term43 n => @lem1299564 x A1 A2 n h1 h0). Qed.
Lemma lem1299570 (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term72 x A1 A2.
Proof. exact (fun n : nat => @lem1299565 n x A1 A2 h1). Qed.
Lemma lem1299571 (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term73 x A1 A2.
Proof. exact (ex_intro (term74 x A1 A2) term64 (@lem1299570 x A1 A2 h1)). Qed.
Lemma lem1299572 (x : nadd) (A1 : nat) (A2 : nat) (h1 : term42 x A1 A2) : term75 x.
Proof. exact (ex_intro (term76 x) (Nat.add A1 A2) (@lem1299571 x A1 A2 h1)). Qed.
Lemma lem1299573 (x : nadd) (A1 : nat) (h1 : term41 x A1) : term75 x.
Proof. exact (ex_elim (@lem1299480 x A1 h1) (fun A2 : nat => fun h0 : term77 x A1 A2 => @lem1299572 x A1 A2 h0)). Qed.
Lemma lem1299574 (x : nadd) : term75 x.
Proof. exact (ex_elim (@lem1299479 x) (fun A1 : nat => fun h0 : term78 x A1 => @lem1299573 x A1 h0)). Qed.
Lemma lem1299579 : term79.
Proof. exact (fun x : nadd => @lem1299574 x). Qed.
