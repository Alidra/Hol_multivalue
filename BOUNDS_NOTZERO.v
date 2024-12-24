Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOUNDS_NOTZERO_term_abbrevs.
Require Import ADD_EQ_0_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1261318 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1261319 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1261320 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1261319 m) (@lem1261318 m)). Qed.
Lemma lem1261321 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1261320 m n). Qed.
Lemma lem1261322 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1261323 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1261322 m n) (@lem1261321 m n)). Qed.
Lemma lem1261324 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1261326 : term4.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1261327 : term5.
Proof. exact (proj2 (@lem1261326)). Qed.
Lemma lem1261328 : term6.
Proof. exact (proj2 (@lem1261327)). Qed.
Lemma lem1261329 : term7.
Proof. exact (proj2 (@lem1261328)). Qed.
Lemma lem1261330 : term8.
Proof. exact (proj2 (@lem1261329)). Qed.
Lemma lem1261331 (m : nat) : term9 m.
Proof. exact (@lem1261330 m). Qed.
Lemma lem1261332 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1261333 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1261332 m) (@lem1261331 m)). Qed.
Lemma lem1261334 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1261333 m n). Qed.
Lemma lem1261335 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term13 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1261352 : term14.
Proof. exact (proj1 (@lem1261326)). Qed.
Lemma lem1261353 (m : nat) : term15 m.
Proof. exact (@lem1261352 m). Qed.
Lemma lem1261354 (m : nat) : (term15 m) = ((term16 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1261360 (m : nat) : term17 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1261361 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1261362 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1261361 m) (@lem1261360 m)). Qed.
Lemma lem1261363 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1261362 m n). Qed.
Lemma lem1261364 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1261365 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem1261364 m n) (@lem1261363 m n)). Qed.
Lemma lem1261366 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem1261365 m n p). Qed.
Lemma lem1261367 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem1261369 (m : nat) : term23 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1261370 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1261371 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem1261370 m) (@lem1261369 m)). Qed.
Lemma lem1261372 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1261371 m n). Qed.
Lemma lem1261373 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1261374 (m : nat) (n : nat) : term26 m n.
Proof. exact (EQ_MP (@lem1261373 m n) (@lem1261372 m n)). Qed.
Lemma lem1261375 (m : nat) (n : nat) (p : nat) : term27 m n p.
Proof. exact (@lem1261374 m n p). Qed.
Lemma lem1261376 (m : nat) (n : nat) (p : nat) : (term27 m n p) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl (term27 m n p)). Qed.
Lemma lem1261378 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1261379 (m : nat) (h1 : term30) : term31 m.
Proof. exact (@lem1261378 h1 m). Qed.
Lemma lem1261380 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1261381 (m : nat) (h1 : term30) : term32 m.
Proof. exact (EQ_MP (@lem1261380 m) (@lem1261379 m h1)). Qed.
Lemma lem1261382 (m : nat) (n : nat) (h1 : term30) : term33 m n.
Proof. exact (@lem1261381 m h1 n). Qed.
Lemma lem1261383 (n : nat) (m : nat) : (term33 m n) = (term34 n m).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1261384 (n : nat) (m : nat) (h1 : term30) : term34 n m.
Proof. exact (EQ_MP (@lem1261383 n m) (@lem1261382 m n h1)). Qed.
Lemma lem1261385 (n : nat) (m : nat) (p : nat) (h1 : term30) : term35 n m p.
Proof. exact (@lem1261384 n m h1 p). Qed.
Lemma lem1261386 (n : nat) (m : nat) (p : nat) : (term35 n m p) = (term36 n m p).
Proof. exact (eq_refl (term35 n m p)). Qed.
Lemma lem1261387 (n : nat) (m : nat) (p : nat) (h1 : term30) : term36 n m p.
Proof. exact (EQ_MP (@lem1261386 n m p) (@lem1261385 n m p h1)). Qed.
Lemma lem1261388 (m : nat) (n : nat) (p : nat) (h1 : term37 m n p) : term37 m n p.
Proof. exact (h1). Qed.
Lemma lem1261389 (m : nat) (n : nat) (p : nat) (h1 : term30) (h2 : term37 m n p) : Peano.le m p.
Proof. exact (@lem1261387 n m p h1 (@lem1261388 m n p h2)). Qed.
Lemma lem1261390 (m : nat) (n : nat) (p : nat) (h1 : term37 m n p) : term38 m p.
Proof. exact (fun h0 : term30 => @lem1261389 m n p h0 h1). Qed.
Lemma lem1261391 (m : nat) (p : nat) (h1 : term39 m p) : term39 m p.
Proof. exact (h1). Qed.
Lemma lem1261392 (m : nat) (p : nat) (h1 : term39 m p) : term38 m p.
Proof. exact (ex_elim (@lem1261391 m p h1) (fun n : nat => fun h0 : term40 m p n => @lem1261390 m n p h0)). Qed.
Lemma lem1261393 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1261394 (m : nat) (p : nat) (h1 : term30) (h2 : term39 m p) : Peano.le m p.
Proof. exact (@lem1261392 m p h2 (@lem1261393 h1)). Qed.
Lemma lem1261395 (m : nat) (p : nat) (h1 : term30) : term41 m p.
Proof. exact (fun h0 : term39 m p => @lem1261394 m p h1 h0). Qed.
Lemma lem1261396 (m : nat) (h1 : term30) : term42 m.
Proof. exact (fun p : nat => @lem1261395 m p h1). Qed.
Lemma lem1261397 (h1 : term30) : term43.
Proof. exact (fun m : nat => @lem1261396 m h1). Qed.
Lemma lem1261398 : term44.
Proof. exact (fun h0 : term30 => @lem1261397 h0). Qed.
Lemma lem1261399 : term43.
Proof. exact (@lem1261398 (@lem93743)). Qed.
Lemma lem1261400 (m : nat) : term45 m.
Proof. exact (@lem1261399 m). Qed.
Lemma lem1261401 (m : nat) : (term45 m) = (term42 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem1261402 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1261401 m) (@lem1261400 m)). Qed.
Lemma lem1261403 (m : nat) (p : nat) : term46 m p.
Proof. exact (@lem1261402 m p). Qed.
Lemma lem1261404 (m : nat) (p : nat) : (term46 m p) = (term41 m p).
Proof. exact (eq_refl (term46 m p)). Qed.
Lemma lem1261406 (m : nat) : term47 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1261407 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1261408 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1261407 m) (@lem1261406 m)). Qed.
Lemma lem1261409 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1261408 m n). Qed.
Lemma lem1261410 (m : nat) (n : nat) : (term49 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term50 m n)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1261412 (m : nat) (n : nat) : term51 m n.
Proof. exact (@lem9784 ((Nat.add m n) = (NUMERAL 0))). Qed.
Lemma lem1261413 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem1261414 (m : nat) (n : nat) : term52 m n.
Proof. exact (EQ_MP (@lem1261413 m n) (@lem1261412 m n)). Qed.
Lemma lem1261415 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1261416 (m : nat) (n : nat) (h1 : term53 m n) : term53 m n.
Proof. exact (h1). Qed.
Lemma lem1261417 (P : type1606) (A : nat) (B : nat) (h1 : term54 P A B) : term54 P A B.
Proof. exact (h1). Qed.
Lemma lem1261418 (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : term55 P A B.
Proof. exact (h1). Qed.
Lemma lem1261419 (P : type1606) (h1 : (term56 P) = (NUMERAL 0)) : (term56 P) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1261423 (P : type1606) (h1 : (term56 P) = (NUMERAL 0)) : (term56 P) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1261435 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term50 m n).
Proof. exact (EQ_MP (@lem1261410 m n) (@lem1261409 m n)). Qed.
Lemma lem1261442 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : term50 m n.
Proof. exact (EQ_MP (@lem1261435 m n) (@lem1261415 m n h1)). Qed.
Lemma lem1261443 (n : nat) : term57 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1261444 (n : nat) : (term57 n) = (term58 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem1261445 (n : nat) : term58 n.
Proof. exact (EQ_MP (@lem1261444 n) (@lem1261443 n)). Qed.
Lemma lem1261446 (n : nat) : (term58 n) = ((term58 n) = True).
Proof. exact (@lem7 (term58 n)). Qed.
Lemma lem1261459 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (proj1 (@lem1261442 m n h1)). Qed.
Lemma lem1261460 (P : type1606) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1261461 (P : type1606) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (P m) = (term59 P).
Proof. exact (MK_COMB (@lem1261460 P) (@lem1261459 m n h1)). Qed.
Lemma lem1261463 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (proj2 (@lem1261442 m n h1)). Qed.
Lemma lem1261464 (P : type1606) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (P m n) = (term56 P).
Proof. exact (MK_COMB (@lem1261461 P m n h1) (@lem1261463 m n h1)). Qed.
Lemma lem1261466 (P : type1606) (h1 : (term56 P) = (NUMERAL 0)) : (term56 P) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1261467 (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : (P m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1261464 P m n h1) (@lem1261466 P h2)). Qed.
Lemma lem1261468 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1261469 (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : (term60 P m n) = term61.
Proof. exact (MK_COMB (@lem1261468) (@lem1261467 m n P h1 h2)). Qed.
Lemma lem1261471 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (proj1 (@lem1261442 m n h1)). Qed.
Lemma lem1261472 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1261473 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m) = term62.
Proof. exact (MK_COMB (@lem1261472) (@lem1261471 m n h1)). Qed.
Lemma lem1261475 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (proj2 (@lem1261442 m n h1)). Qed.
Lemma lem1261476 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = term63.
Proof. exact (MK_COMB (@lem1261473 m n h1) (@lem1261475 m n h1)). Qed.
Lemma lem1261477 (A : nat) (B : nat) : (term64 A B) = (term64 A B).
Proof. exact (eq_refl (term64 A B)). Qed.
Lemma lem1261478 (A : nat) (B : nat) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term65 A B m n) = (term66 A B).
Proof. exact (MK_COMB (@lem1261477 A B) (@lem1261476 m n h1)). Qed.
Lemma lem1261479 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : (term67 P A B m n) = (term68 A B).
Proof. exact (MK_COMB (@lem1261469 m n P h1 h2) (@lem1261478 A B m n h1)). Qed.
Lemma lem1261481 (n : nat) : (term58 n) = True.
Proof. exact (EQ_MP (@lem1261446 n) (@lem1261445 n)). Qed.
Lemma lem1261482 (A : nat) (B : nat) : (term68 A B) = True.
Proof. exact (@lem1261481 (term66 A B)). Qed.
Lemma lem1261483 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : (term67 P A B m n) = True.
Proof. exact (TRANS (@lem1261479 A B m n P h1 h2) (@lem1261482 A B)). Qed.
Lemma lem1261484 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : True = (term67 P A B m n).
Proof. exact (SYM (@lem1261483 A B m n P h1 h2)). Qed.
Lemma lem1261485 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : term67 P A B m n.
Proof. exact (EQ_MP (@lem1261484 A B m n P h1 h2) (@lem0)). Qed.
Lemma lem1261486 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : ((term56 P) = (NUMERAL 0)) = (term67 P A B m n).
Proof. exact (prop_ext (fun h3 : (term56 P) = (NUMERAL 0) => @lem1261485 A B m n P h1 h2) (fun h3 : term67 P A B m n => @lem1261423 P h2)). Qed.
Lemma lem1261487 (A : nat) (B : nat) (m : nat) (n : nat) (P : type1606) (h1 : (Nat.add m n) = (NUMERAL 0)) (h2 : (term56 P) = (NUMERAL 0)) : term67 P A B m n.
Proof. exact (EQ_MP (@lem1261486 A B m n P h1 h2) (@lem1261423 P h2)). Qed.
Lemma lem1261489 (m : nat) (p : nat) : term41 m p.
Proof. exact (EQ_MP (@lem1261404 m p) (@lem1261403 m p)). Qed.
Lemma lem1261490 (P : type1606) (A : nat) (B : nat) (m : nat) (n : nat) : term69 P A B m n.
Proof. exact (@lem1261489 (P m n) (term65 A B m n)). Qed.
Lemma lem1261491 (m : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : term70 P A B m.
Proof. exact (@lem1261418 P A B h1 m). Qed.
Lemma lem1261492 (P : type1606) (A : nat) (m : nat) (B : nat) : (term70 P A B m) = (term71 P A m B).
Proof. exact (eq_refl (term70 P A B m)). Qed.
Lemma lem1261493 (m : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : term71 P A m B.
Proof. exact (EQ_MP (@lem1261492 P A m B) (@lem1261491 m P A B h1)). Qed.
Lemma lem1261494 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : term72 P A m B n.
Proof. exact (@lem1261493 m P A B h1 n). Qed.
Lemma lem1261495 (P : type1606) (A : nat) (m : nat) (n : nat) (B : nat) : (term72 P A m B n) = (term73 P A m n B).
Proof. exact (eq_refl (term72 P A m B n)). Qed.
Lemma lem1261496 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : term73 P A m n B.
Proof. exact (EQ_MP (@lem1261495 P A m n B) (@lem1261494 m n P A B h1)). Qed.
Lemma lem1261497 (P : type1606) (A : nat) (m : nat) (n : nat) (B : nat) : (term73 P A m n B) = ((term73 P A m n B) = True).
Proof. exact (@lem7 (term73 P A m n B)). Qed.
Lemma lem1261515 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : (term73 P A m n B) = True.
Proof. exact (EQ_MP (@lem1261497 P A m n B) (@lem1261496 m n P A B h1)). Qed.
Lemma lem1261516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1261517 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : (term74 P A m n B) = (and True).
Proof. exact (MK_COMB (@lem1261516) (@lem1261515 m n P A B h1)). Qed.
Lemma lem1261518 (A : nat) (B : nat) (m : nat) (n : nat) : (term75 A B m n) = (term75 A B m n).
Proof. exact (eq_refl (term75 A B m n)). Qed.
Lemma lem1261519 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : (term76 P A B m n) = (term77 A B m n).
Proof. exact (MK_COMB (@lem1261517 m n P A B h1) (@lem1261518 A B m n)). Qed.
Lemma lem1261521 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1261522 (A : nat) (B : nat) (m : nat) (n : nat) : (term77 A B m n) = (term75 A B m n).
Proof. exact (@lem1261521 (term75 A B m n)). Qed.
Lemma lem1261523 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : (term76 P A B m n) = (term75 A B m n).
Proof. exact (TRANS (@lem1261519 m n P A B h1) (@lem1261522 A B m n)). Qed.
Lemma lem1261524 (m : nat) (n : nat) (P : type1606) (A : nat) (B : nat) (h1 : term55 P A B) : (term75 A B m n) = (term76 P A B m n).
Proof. exact (SYM (@lem1261523 m n P A B h1)). Qed.
Lemma lem1261526 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term29 m n p).
Proof. exact (EQ_MP (@lem1261376 m n p) (@lem1261375 m n p)). Qed.
Lemma lem1261527 (A : nat) (B : nat) (m : nat) (n : nat) : (term65 A B m n) = (term78 A B m n).
Proof. exact (@lem1261526 A B (Nat.add m n)). Qed.
Lemma lem1261528 (A : nat) (m : nat) (n : nat) (B : nat) : (term79 A m n B) = (term79 A m n B).
Proof. exact (eq_refl (term79 A m n B)). Qed.
Lemma lem1261529 (A : nat) (B : nat) (m : nat) (n : nat) : (term75 A B m n) = (term80 A B m n).
Proof. exact (MK_COMB (@lem1261528 A m n B) (@lem1261527 A B m n)). Qed.
Lemma lem1261531 (m : nat) (n : nat) (p : nat) : (term22 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1261367 m n p) (@lem1261366 m n p)). Qed.
Lemma lem1261532 (A : nat) (B : nat) (m : nat) (n : nat) : (term80 A B m n) = (term81 B m n).
Proof. exact (@lem1261531 (term82 A m n) B (term82 B m n)). Qed.
Lemma lem1261533 (A : nat) (B : nat) (m : nat) (n : nat) : (term75 A B m n) = (term81 B m n).
Proof. exact (TRANS (@lem1261529 A B m n) (@lem1261532 A B m n)). Qed.
Lemma lem1261534 (A : nat) (B : nat) (m : nat) (n : nat) : (term81 B m n) = (term75 A B m n).
Proof. exact (SYM (@lem1261533 A B m n)). Qed.
Lemma lem1261536 (P : nat -> Prop) : term83 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1261537 (B : nat) : term84 B.
Proof. exact (@lem1261536 (term85 B)). Qed.
Lemma lem1261538 (B : nat) : (term86 B) = (term87 B).
Proof. exact (eq_refl (term86 B)). Qed.
Lemma lem1261539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1261540 (B : nat) : (term88 B) = (term89 B).
Proof. exact (MK_COMB (@lem1261539) (@lem1261538 B)). Qed.
Lemma lem1261541 (B : nat) (p : nat) : (term90 B p) = (term91 B p).
Proof. exact (eq_refl (term90 B p)). Qed.
Lemma lem1261542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261543 (B : nat) (p : nat) : (term92 B p) = (term93 B p).
Proof. exact (MK_COMB (@lem1261542) (@lem1261541 B p)). Qed.
Lemma lem1261544 (B : nat) (p : nat) : (term94 B p) = (term95 B p).
Proof. exact (eq_refl (term94 B p)). Qed.
Lemma lem1261545 (B : nat) (p : nat) : (term96 B p) = (term97 B p).
Proof. exact (MK_COMB (@lem1261543 B p) (@lem1261544 B p)). Qed.
Lemma lem1261546 (B : nat) : (term98 B) = (term99 B).
Proof. exact (fun_ext (fun p : nat => @lem1261545 B p)). Qed.
Lemma lem1261547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261548 (B : nat) : (term100 B) = (term101 B).
Proof. exact (MK_COMB (@lem1261547) (@lem1261546 B)). Qed.
Lemma lem1261549 (B : nat) : (term102 B) = (term103 B).
Proof. exact (MK_COMB (@lem1261540 B) (@lem1261548 B)). Qed.
Lemma lem1261550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261551 (B : nat) : (term104 B) = (term105 B).
Proof. exact (MK_COMB (@lem1261550) (@lem1261549 B)). Qed.
Lemma lem1261552 (B : nat) (p : nat) : (term90 B p) = (term91 B p).
Proof. exact (eq_refl (term90 B p)). Qed.
Lemma lem1261553 (B : nat) : (term106 B) = (term85 B).
Proof. exact (fun_ext (fun p : nat => @lem1261552 B p)). Qed.
Lemma lem1261554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261555 (B : nat) : (term107 B) = (term108 B).
Proof. exact (MK_COMB (@lem1261554) (@lem1261553 B)). Qed.
Lemma lem1261556 (B : nat) : (term84 B) = (term109 B).
Proof. exact (MK_COMB (@lem1261551 B) (@lem1261555 B)). Qed.
Lemma lem1261557 (B : nat) : term109 B.
Proof. exact (EQ_MP (@lem1261556 B) (@lem1261537 B)). Qed.
Lemma lem1261562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1261563 (x : nat) : (x = x) = True.
Proof. exact (@lem1261562 nat x). Qed.
Lemma lem1261564 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1261563 (NUMERAL 0)). Qed.
Lemma lem1261565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1261566 : term110 = (~ True).
Proof. exact (MK_COMB (@lem1261565) (@lem1261564)). Qed.
Lemma lem1261568 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1261569 : term110 = False.
Proof. exact (TRANS (@lem1261566) (@lem1261568)). Qed.
Lemma lem1261570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261571 : term111 = (imp False).
Proof. exact (MK_COMB (@lem1261570) (@lem1261569)). Qed.
Lemma lem1261573 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1261354 m) (@lem1261353 m)). Qed.
Lemma lem1261574 (B : nat) : (term16 B) = (NUMERAL 0).
Proof. exact (@lem1261573 B). Qed.
Lemma lem1261575 (B : nat) : (Peano.le B) = (Peano.le B).
Proof. exact (eq_refl (Peano.le B)). Qed.
Lemma lem1261576 (B : nat) : (term112 B) = (term113 B).
Proof. exact (MK_COMB (@lem1261575 B) (@lem1261574 B)). Qed.
Lemma lem1261577 (B : nat) : (term87 B) = (term114 B).
Proof. exact (MK_COMB (@lem1261571) (@lem1261576 B)). Qed.
Lemma lem1261579 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1261580 (B : nat) : (term114 B) = True.
Proof. exact (@lem1261579 (term113 B)). Qed.
Lemma lem1261581 (B : nat) : (term87 B) = True.
Proof. exact (TRANS (@lem1261577 B) (@lem1261580 B)). Qed.
Lemma lem1261582 (B : nat) : True = (term87 B).
Proof. exact (SYM (@lem1261581 B)). Qed.
Lemma lem1261583 (B : nat) : term87 B.
Proof. exact (EQ_MP (@lem1261582 B) (@lem0)). Qed.
Lemma lem1261589 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem1261335 m n) (@lem1261334 m n)). Qed.
Lemma lem1261590 (B : nat) (p : nat) : (term12 B p) = (term13 B p).
Proof. exact (@lem1261589 B p). Qed.
Lemma lem1261591 (B : nat) : (Peano.le B) = (Peano.le B).
Proof. exact (eq_refl (Peano.le B)). Qed.
Lemma lem1261592 (B : nat) (p : nat) : (term115 B p) = (term116 B p).
Proof. exact (MK_COMB (@lem1261591 B) (@lem1261590 B p)). Qed.
Lemma lem1261594 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1261324 m n) (@lem1261323 m n)). Qed.
Lemma lem1261595 (B : nat) (p : nat) : (term116 B p) = True.
Proof. exact (@lem1261594 B (Nat.mul B p)). Qed.
Lemma lem1261596 (B : nat) (p : nat) : (term115 B p) = True.
Proof. exact (TRANS (@lem1261592 B p) (@lem1261595 B p)). Qed.
Lemma lem1261597 (p : nat) : (term117 p) = (term117 p).
Proof. exact (eq_refl (term117 p)). Qed.
Lemma lem1261598 (B : nat) (p : nat) : (term95 B p) = (term118 p).
Proof. exact (MK_COMB (@lem1261597 p) (@lem1261596 B p)). Qed.
Lemma lem1261600 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1261601 (p : nat) : (term118 p) = True.
Proof. exact (@lem1261600 (term119 p)). Qed.
Lemma lem1261602 (B : nat) (p : nat) : (term95 B p) = True.
Proof. exact (TRANS (@lem1261598 B p) (@lem1261601 p)). Qed.
Lemma lem1261603 (B : nat) (p : nat) : True = (term95 B p).
Proof. exact (SYM (@lem1261602 B p)). Qed.
Lemma lem1261604 (B : nat) (p : nat) : term95 B p.
Proof. exact (EQ_MP (@lem1261603 B p) (@lem0)). Qed.
Lemma lem1261605 (B : nat) (p : nat) : term97 B p.
Proof. exact (fun h0 : term91 B p => @lem1261604 B p). Qed.
Lemma lem1261610 (B : nat) : term101 B.
Proof. exact (fun p : nat => @lem1261605 B p). Qed.
Lemma lem1261611 (B : nat) : term103 B.
Proof. exact (conj (@lem1261583 B) (@lem1261610 B)). Qed.
Lemma lem1261612 (B : nat) : term108 B.
Proof. exact (@lem1261557 B (@lem1261611 B)). Qed.
Lemma lem1261613 (B : nat) (m : nat) (n : nat) : term120 B m n.
Proof. exact (@lem1261612 B (Nat.add m n)). Qed.
Lemma lem1261614 (B : nat) (m : nat) (n : nat) : (term120 B m n) = (term121 B m n).
Proof. exact (eq_refl (term120 B m n)). Qed.
Lemma lem1261615 (B : nat) (m : nat) (n : nat) : term121 B m n.
Proof. exact (EQ_MP (@lem1261614 B m n) (@lem1261613 B m n)). Qed.
Lemma lem1261616 (B : nat) (m : nat) (n : nat) (h1 : term53 m n) : term81 B m n.
Proof. exact (@lem1261615 B m n (@lem1261416 m n h1)). Qed.
Lemma lem1261617 (A : nat) (B : nat) (m : nat) (n : nat) (h1 : term53 m n) : term75 A B m n.
Proof. exact (EQ_MP (@lem1261534 A B m n) (@lem1261616 B m n h1)). Qed.
Lemma lem1261618 (P : type1606) (A : nat) (B : nat) (m : nat) (n : nat) (h1 : term55 P A B) (h2 : term53 m n) : term76 P A B m n.
Proof. exact (EQ_MP (@lem1261524 m n P A B h1) (@lem1261617 A B m n h2)). Qed.
Lemma lem1261619 (P : type1606) (A : nat) (B : nat) (m : nat) (n : nat) (h1 : term55 P A B) (h2 : term53 m n) : term122 P A B m n.
Proof. exact (ex_intro (term123 P A B m n) (term124 A m n B) (@lem1261618 P A B m n h1 h2)). Qed.
Lemma lem1261620 (P : type1606) (A : nat) (B : nat) (m : nat) (n : nat) (h1 : term55 P A B) (h2 : term53 m n) : term67 P A B m n.
Proof. exact (@lem1261490 P A B m n (@lem1261619 P A B m n h1 h2)). Qed.
Lemma lem1261621 (m : nat) (n : nat) (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term67 P A B m n.
Proof. exact (or_elim (@lem1261414 m n) (fun h0 : (Nat.add m n) = (NUMERAL 0) => @lem1261487 A B m n P h0 h2) (fun h0 : term53 m n => @lem1261620 P A B m n h1 h0)). Qed.
Lemma lem1261626 (m : nat) (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term125 P A B m.
Proof. exact (fun n : nat => @lem1261621 m n A B P h1 h2). Qed.
Lemma lem1261631 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term126 P A B.
Proof. exact (fun m : nat => @lem1261626 m A B P h1 h2). Qed.
Lemma lem1261632 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term127 P.
Proof. exact (ex_intro (term128 P) (Nat.add A B) (@lem1261631 A B P h1 h2)). Qed.
Lemma lem1261633 (P : type1606) (A : nat) (B : nat) (h1 : term54 P A B) : term55 P A B.
Proof. exact (proj2 (@lem1261417 P A B h1)). Qed.
Lemma lem1261634 (P : type1606) (A : nat) (B : nat) (h1 : term54 P A B) : (term56 P) = (NUMERAL 0).
Proof. exact (proj1 (@lem1261417 P A B h1)). Qed.
Lemma lem1261635 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : (term55 P A B) = (term127 P).
Proof. exact (prop_ext (fun h3 : term55 P A B => @lem1261632 A B P h1 h2) (fun h3 : term127 P => @lem1261418 P A B h1)). Qed.
Lemma lem1261636 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term127 P.
Proof. exact (EQ_MP (@lem1261635 A B P h1 h2) (@lem1261418 P A B h1)). Qed.
Lemma lem1261637 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : ((term56 P) = (NUMERAL 0)) = (term127 P).
Proof. exact (prop_ext (fun h3 : (term56 P) = (NUMERAL 0) => @lem1261636 A B P h1 h2) (fun h3 : term127 P => @lem1261419 P h2)). Qed.
Lemma lem1261638 (A : nat) (B : nat) (P : type1606) (h1 : term55 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term127 P.
Proof. exact (EQ_MP (@lem1261637 A B P h1 h2) (@lem1261419 P h2)). Qed.
Lemma lem1261639 (A : nat) (B : nat) (P : type1606) (h1 : term54 P A B) (h2 : (term56 P) = (NUMERAL 0)) : (term55 P A B) = (term127 P).
Proof. exact (prop_ext (fun h3 : term55 P A B => @lem1261638 A B P h3 h2) (fun h3 : term127 P => @lem1261633 P A B h1)). Qed.
Lemma lem1261640 (A : nat) (B : nat) (P : type1606) (h1 : term54 P A B) (h2 : (term56 P) = (NUMERAL 0)) : term127 P.
Proof. exact (EQ_MP (@lem1261639 A B P h1 h2) (@lem1261633 P A B h1)). Qed.
Lemma lem1261641 (P : type1606) (A : nat) (B : nat) (h1 : term54 P A B) : ((term56 P) = (NUMERAL 0)) = (term127 P).
Proof. exact (prop_ext (fun h2 : (term56 P) = (NUMERAL 0) => @lem1261640 A B P h1 h2) (fun h2 : term127 P => @lem1261634 P A B h1)). Qed.
Lemma lem1261642 (P : type1606) (A : nat) (B : nat) (h1 : term54 P A B) : term127 P.
Proof. exact (EQ_MP (@lem1261641 P A B h1) (@lem1261634 P A B h1)). Qed.
Lemma lem1261643 (A : nat) (B : nat) (P : type1606) : term129 A B P.
Proof. exact (fun h0 : term54 P A B => @lem1261642 P A B h0). Qed.
Lemma lem1261648 (A : nat) (P : type1606) : term130 A P.
Proof. exact (fun B : nat => @lem1261643 A B P). Qed.
Lemma lem1261653 (P : type1606) : term131 P.
Proof. exact (fun A : nat => @lem1261648 A P). Qed.
Lemma lem1261658 : term132.
Proof. exact (fun P : type1606 => @lem1261653 P). Qed.
