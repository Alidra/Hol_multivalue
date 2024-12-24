Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_LMULT_term_abbrevs.
Require Import EQ_MULT_LCANCEL_spec.
Require Import LE_MULT2_spec.
Require Import LE_REFL_spec.
Require Import LT_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem102388 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem102389 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem102388 h1 m). Qed.
Lemma lem102390 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem102391 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem102390 m) (@lem102389 m h1)). Qed.
Lemma lem102392 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem102391 m h1 n). Qed.
Lemma lem102393 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem102394 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem102393 m n) (@lem102392 m n h1)). Qed.
Lemma lem102395 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem102394 m n h1 p). Qed.
Lemma lem102396 (m : nat) (p : nat) (n : nat) : (term5 m n p) = (term6 m p n).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem102397 (m : nat) (p : nat) (n : nat) (h1 : term0) : term6 m p n.
Proof. exact (EQ_MP (@lem102396 m p n) (@lem102395 m n p h1)). Qed.
Lemma lem102398 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) : term7 m p n q.
Proof. exact (@lem102397 m p n h1 q). Qed.
Lemma lem102399 (m : nat) (p : nat) (n : nat) (q : nat) : (term7 m p n q) = (term8 m p n q).
Proof. exact (eq_refl (term7 m p n q)). Qed.
Lemma lem102400 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) : term8 m p n q.
Proof. exact (EQ_MP (@lem102399 m p n q) (@lem102398 m p n q h1)). Qed.
Lemma lem102401 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term9 m n p q) : term9 m n p q.
Proof. exact (h1). Qed.
Lemma lem102402 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) (h2 : term9 m n p q) : term10 m p n q.
Proof. exact (@lem102400 m p n q h1 (@lem102401 m n p q h2)). Qed.
Lemma lem102403 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term9 m n p q) : term11 m p n q.
Proof. exact (fun h0 : term0 => @lem102402 m n p q h0 h1). Qed.
Lemma lem102404 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem102405 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) (h2 : term9 m n p q) : term10 m p n q.
Proof. exact (@lem102403 m n p q h2 (@lem102404 h1)). Qed.
Lemma lem102406 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) : term8 m p n q.
Proof. exact (fun h0 : term9 m n p q => @lem102405 m n p q h1 h0). Qed.
Lemma lem102407 (m : nat) (p : nat) (n : nat) (h1 : term0) : term6 m p n.
Proof. exact (fun q : nat => @lem102406 m p n q h1). Qed.
Lemma lem102408 (m : nat) (p : nat) (h1 : term0) : term12 m p.
Proof. exact (fun n : nat => @lem102407 m p n h1). Qed.
Lemma lem102409 (m : nat) (h1 : term0) : term13 m.
Proof. exact (fun p : nat => @lem102408 m p h1). Qed.
Lemma lem102410 (h1 : term0) : term14.
Proof. exact (fun m : nat => @lem102409 m h1). Qed.
Lemma lem102411 : term15.
Proof. exact (fun h0 : term0 => @lem102410 h0). Qed.
Lemma lem102412 : term14.
Proof. exact (@lem102411 (@lem102387)). Qed.
Lemma lem102413 (m : nat) : term16 m.
Proof. exact (@lem102412 m). Qed.
Lemma lem102414 (m : nat) : (term16 m) = (term13 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem102415 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem102414 m) (@lem102413 m)). Qed.
Lemma lem102416 (m : nat) (p : nat) : term17 m p.
Proof. exact (@lem102415 m p). Qed.
Lemma lem102417 (m : nat) (p : nat) : (term17 m p) = (term12 m p).
Proof. exact (eq_refl (term17 m p)). Qed.
Lemma lem102418 (m : nat) (p : nat) : term12 m p.
Proof. exact (EQ_MP (@lem102417 m p) (@lem102416 m p)). Qed.
Lemma lem102419 (m : nat) (p : nat) (n : nat) : term18 m p n.
Proof. exact (@lem102418 m p n). Qed.
Lemma lem102420 (m : nat) (p : nat) (n : nat) : (term18 m p n) = (term6 m p n).
Proof. exact (eq_refl (term18 m p n)). Qed.
Lemma lem102421 (m : nat) (p : nat) (n : nat) : term6 m p n.
Proof. exact (EQ_MP (@lem102420 m p n) (@lem102419 m p n)). Qed.
Lemma lem102422 (m : nat) (p : nat) (n : nat) (q : nat) : term7 m p n q.
Proof. exact (@lem102421 m p n q). Qed.
Lemma lem102423 (m : nat) (p : nat) (n : nat) (q : nat) : (term7 m p n q) = (term8 m p n q).
Proof. exact (eq_refl (term7 m p n q)). Qed.
Lemma lem102425 (m : nat) : term19 m.
Proof. exact (@lem97539 m). Qed.
Lemma lem102426 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem102427 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem102426 m) (@lem102425 m)). Qed.
Lemma lem102428 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem102427 m n). Qed.
Lemma lem102429 (m : nat) (n : nat) : (term21 m n) = ((Peano.lt m n) = (term22 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem102438 (m : nat) (n : nat) : (Peano.lt m n) = (term22 m n).
Proof. exact (EQ_MP (@lem102429 m n) (@lem102428 m n)). Qed.
Lemma lem102439 (n : nat) (p : nat) : (Peano.lt n p) = (term22 n p).
Proof. exact (@lem102438 n p). Qed.
Lemma lem102444 (m : nat) : (term23 m) = (term23 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem102445 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term25 m n p).
Proof. exact (MK_COMB (@lem102444 m) (@lem102439 n p)). Qed.
Lemma lem102448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102449 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (MK_COMB (@lem102448) (@lem102445 m n p)). Qed.
Lemma lem102451 (m : nat) (n : nat) : (Peano.lt m n) = (term22 m n).
Proof. exact (EQ_MP (@lem102429 m n) (@lem102428 m n)). Qed.
Lemma lem102452 (n : nat) (m : nat) (p : nat) : (term28 n m p) = (term29 n m p).
Proof. exact (@lem102451 (Nat.mul m n) (Nat.mul m p)). Qed.
Lemma lem102457 (n : nat) (m : nat) (p : nat) : (term30 n m p) = (term31 n m p).
Proof. exact (MK_COMB (@lem102449 m n p) (@lem102452 n m p)). Qed.
Lemma lem102460 (n : nat) (m : nat) (p : nat) : (term31 n m p) = (term30 n m p).
Proof. exact (SYM (@lem102457 n m p)). Qed.
Lemma lem102461 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem102462 (n : nat) (p : nat) (h1 : term22 n p) : term22 n p.
Proof. exact (h1). Qed.
Lemma lem102463 (m : nat) (h1 : term32 m) : term32 m.
Proof. exact (h1). Qed.
Lemma lem102464 (n : nat) (p : nat) (h1 : term33 n p) : term33 n p.
Proof. exact (h1). Qed.
Lemma lem102465 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem102467 (m : nat) (p : nat) (n : nat) (q : nat) : term8 m p n q.
Proof. exact (EQ_MP (@lem102423 m p n q) (@lem102422 m p n q)). Qed.
Lemma lem102468 (n : nat) (m : nat) (p : nat) : term34 n m p.
Proof. exact (@lem102467 m n m p). Qed.
Lemma lem102469 (n : nat) : term35 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem102470 (n : nat) : (term35 n) = (Peano.le n n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem102471 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem102470 n) (@lem102469 n)). Qed.
Lemma lem102472 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem102487 (n : nat) (p : nat) : (Peano.le n p) = ((Peano.le n p) = True).
Proof. exact (@lem7 (Peano.le n p)). Qed.
Lemma lem102505 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem102472 n) (@lem102471 n)). Qed.
Lemma lem102506 (m : nat) : (Peano.le m m) = True.
Proof. exact (@lem102505 m). Qed.
Lemma lem102507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102508 (m : nat) : (term36 m) = (and True).
Proof. exact (MK_COMB (@lem102507) (@lem102506 m)). Qed.
Lemma lem102510 (n : nat) (p : nat) (h1 : Peano.le n p) : (Peano.le n p) = True.
Proof. exact (EQ_MP (@lem102487 n p) (@lem102465 n p h1)). Qed.
Lemma lem102511 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term37 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem102508 m) (@lem102510 n p h1)). Qed.
Lemma lem102513 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem102514 : (True /\ True) = True.
Proof. exact (@lem102513 True). Qed.
Lemma lem102515 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term37 m n p) = True.
Proof. exact (TRANS (@lem102511 m n p h1) (@lem102514)). Qed.
Lemma lem102516 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : True = (term37 m n p).
Proof. exact (SYM (@lem102515 m n p h1)). Qed.
Lemma lem102517 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : term37 m n p.
Proof. exact (EQ_MP (@lem102516 m n p h1) (@lem0)). Qed.
Lemma lem102518 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : term38 n m p.
Proof. exact (@lem102468 n m p (@lem102517 m n p h1)). Qed.
Lemma lem102519 (m : nat) : term39 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem102520 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem102521 (m : nat) : term40 m.
Proof. exact (EQ_MP (@lem102520 m) (@lem102519 m)). Qed.
Lemma lem102522 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem102521 m n). Qed.
Lemma lem102523 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem102524 (m : nat) (n : nat) : term42 m n.
Proof. exact (EQ_MP (@lem102523 m n) (@lem102522 m n)). Qed.
Lemma lem102525 (m : nat) (n : nat) (p : nat) : term43 m n p.
Proof. exact (@lem102524 m n p). Qed.
Lemma lem102526 (m : nat) (n : nat) (p : nat) : (term43 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term44 m n p)).
Proof. exact (eq_refl (term43 m n p)). Qed.
Lemma lem102528 (m : nat) : term45 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem102543 (n : nat) (p : nat) : term46 n p.
Proof. exact (@lem82 (n = p)). Qed.
Lemma lem102557 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term44 m n p).
Proof. exact (EQ_MP (@lem102526 m n p) (@lem102525 m n p)). Qed.
Lemma lem102561 (m : nat) (h1 : term32 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem102528 m (@lem102463 m h1)). Qed.
Lemma lem102562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem102563 (m : nat) (h1 : term32 m) : (term47 m) = (or False).
Proof. exact (MK_COMB (@lem102562) (@lem102561 m h1)). Qed.
Lemma lem102565 (n : nat) (p : nat) (h1 : term33 n p) : (n = p) = False.
Proof. exact (@lem102543 n p (@lem102464 n p h1)). Qed.
Lemma lem102566 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : (term44 m n p) = (False \/ False).
Proof. exact (MK_COMB (@lem102563 m h1) (@lem102565 n p h2)). Qed.
Lemma lem102568 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem102569 : (False \/ False) = False.
Proof. exact (@lem102568 False). Qed.
Lemma lem102570 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : (term44 m n p) = False.
Proof. exact (TRANS (@lem102566 m n p h1 h2) (@lem102569)). Qed.
Lemma lem102571 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : ((Nat.mul m n) = (Nat.mul m p)) = False.
Proof. exact (TRANS (@lem102557 m n p) (@lem102570 m n p h1 h2)). Qed.
Lemma lem102572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem102573 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : (term48 n m p) = (~ False).
Proof. exact (MK_COMB (@lem102572) (@lem102571 m n p h1 h2)). Qed.
Lemma lem102575 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem102576 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : (term48 n m p) = True.
Proof. exact (TRANS (@lem102573 m n p h1 h2) (@lem102575)). Qed.
Lemma lem102577 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : True = (term48 n m p).
Proof. exact (SYM (@lem102576 m n p h1 h2)). Qed.
Lemma lem102578 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) : term48 n m p.
Proof. exact (EQ_MP (@lem102577 m n p h1 h2) (@lem0)). Qed.
Lemma lem102579 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) (h3 : Peano.le n p) : term29 n m p.
Proof. exact (conj (@lem102518 m n p h3) (@lem102578 m n p h1 h2)). Qed.
Lemma lem102580 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term22 n p.
Proof. exact (proj2 (@lem102461 m n p h1)). Qed.
Lemma lem102581 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term32 m.
Proof. exact (proj1 (@lem102461 m n p h1)). Qed.
Lemma lem102582 (n : nat) (p : nat) (h1 : term22 n p) : term33 n p.
Proof. exact (proj2 (@lem102462 n p h1)). Qed.
Lemma lem102583 (n : nat) (p : nat) (h1 : term22 n p) : Peano.le n p.
Proof. exact (proj1 (@lem102462 n p h1)). Qed.
Lemma lem102584 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) (h3 : Peano.le n p) : (term33 n p) = (term29 n m p).
Proof. exact (prop_ext (fun h4 : term33 n p => @lem102579 m n p h1 h2 h3) (fun h4 : term29 n m p => @lem102464 n p h2)). Qed.
Lemma lem102585 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) (h3 : Peano.le n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102584 m n p h1 h2 h3) (@lem102464 n p h2)). Qed.
Lemma lem102586 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) (h3 : Peano.le n p) : (Peano.le n p) = (term29 n m p).
Proof. exact (prop_ext (fun h4 : Peano.le n p => @lem102585 m n p h1 h2 h3) (fun h4 : term29 n m p => @lem102465 n p h3)). Qed.
Lemma lem102587 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term33 n p) (h3 : Peano.le n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102586 m n p h1 h2 h3) (@lem102465 n p h3)). Qed.
Lemma lem102588 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) (h3 : Peano.le n p) : (term33 n p) = (term29 n m p).
Proof. exact (prop_ext (fun h4 : term33 n p => @lem102587 m n p h1 h4 h3) (fun h4 : term29 n m p => @lem102582 n p h2)). Qed.
Lemma lem102589 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) (h3 : Peano.le n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102588 m n p h1 h2 h3) (@lem102582 n p h2)). Qed.
Lemma lem102590 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) : (Peano.le n p) = (term29 n m p).
Proof. exact (prop_ext (fun h3 : Peano.le n p => @lem102589 m n p h1 h2 h3) (fun h3 : term29 n m p => @lem102583 n p h2)). Qed.
Lemma lem102591 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102590 m n p h1 h2) (@lem102583 n p h2)). Qed.
Lemma lem102592 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) : (term32 m) = (term29 n m p).
Proof. exact (prop_ext (fun h3 : term32 m => @lem102591 m n p h1 h2) (fun h3 : term29 n m p => @lem102463 m h1)). Qed.
Lemma lem102593 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term22 n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102592 m n p h1 h2) (@lem102463 m h1)). Qed.
Lemma lem102594 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term25 m n p) : (term22 n p) = (term29 n m p).
Proof. exact (prop_ext (fun h3 : term22 n p => @lem102593 m n p h1 h3) (fun h3 : term29 n m p => @lem102580 m n p h2)). Qed.
Lemma lem102595 (m : nat) (n : nat) (p : nat) (h1 : term32 m) (h2 : term25 m n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102594 m n p h1 h2) (@lem102580 m n p h2)). Qed.
Lemma lem102596 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : (term32 m) = (term29 n m p).
Proof. exact (prop_ext (fun h2 : term32 m => @lem102595 m n p h2 h1) (fun h2 : term29 n m p => @lem102581 m n p h1)). Qed.
Lemma lem102597 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term29 n m p.
Proof. exact (EQ_MP (@lem102596 m n p h1) (@lem102581 m n p h1)). Qed.
Lemma lem102598 (n : nat) (m : nat) (p : nat) : term31 n m p.
Proof. exact (fun h0 : term25 m n p => @lem102597 m n p h0). Qed.
Lemma lem102599 (n : nat) (m : nat) (p : nat) : term30 n m p.
Proof. exact (EQ_MP (@lem102460 n m p) (@lem102598 n m p)). Qed.
Lemma lem102604 (n : nat) (m : nat) : term49 n m.
Proof. exact (fun p : nat => @lem102599 n m p). Qed.
Lemma lem102609 (m : nat) : term50 m.
Proof. exact (fun n : nat => @lem102604 n m). Qed.
Lemma lem102614 : term51.
Proof. exact (fun m : nat => @lem102609 m). Qed.
