Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_DIV_LE_term_abbrevs.
Require Import DIVISION_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_REFL_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem218368 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem218369 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem218370 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem218369 m) (@lem218368 m)). Qed.
Lemma lem218371 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem218370 m n). Qed.
Lemma lem218372 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem218373 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem218372 m n) (@lem218371 m n)). Qed.
Lemma lem218374 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem218376 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem218380 (m : nat) : term5 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem218381 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem218382 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem218381 m) (@lem218380 m)). Qed.
Lemma lem218383 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem218382 m n). Qed.
Lemma lem218384 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem218385 (n : nat) (m : nat) : term8 n m.
Proof. exact (EQ_MP (@lem218384 n m) (@lem218383 m n)). Qed.
Lemma lem218386 (n : nat) (m : nat) (p : nat) : term9 n m p.
Proof. exact (@lem218385 n m p). Qed.
Lemma lem218387 (n : nat) (m : nat) (p : nat) : (term9 n m p) = ((term10 m n p) = (term11 n m p)).
Proof. exact (eq_refl (term9 n m p)). Qed.
Lemma lem218389 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem218390 (m : nat) (h1 : term12) : term13 m.
Proof. exact (@lem218389 h1 m). Qed.
Lemma lem218391 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem218392 (m : nat) (h1 : term12) : term14 m.
Proof. exact (EQ_MP (@lem218391 m) (@lem218390 m h1)). Qed.
Lemma lem218393 (m : nat) (n : nat) (h1 : term12) : term15 m n.
Proof. exact (@lem218392 m h1 n). Qed.
Lemma lem218394 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem218395 (m : nat) (n : nat) (h1 : term12) : term16 m n.
Proof. exact (EQ_MP (@lem218394 m n) (@lem218393 m n h1)). Qed.
Lemma lem218396 (n : nat) (h1 : term17 n) : term17 n.
Proof. exact (h1). Qed.
Lemma lem218397 (m : nat) (n : nat) (h1 : term12) (h2 : term17 n) : term18 m n.
Proof. exact (@lem218395 m n h1 (@lem218396 n h2)). Qed.
Lemma lem218398 (n : nat) (h1 : term12) (h2 : term17 n) : term19 n.
Proof. exact (fun m : nat => @lem218397 m n h1 h2). Qed.
Lemma lem218399 (n : nat) (h1 : term12) : term20 n.
Proof. exact (fun h0 : term17 n => @lem218398 n h1 h0). Qed.
Lemma lem218400 (h1 : term12) : term21.
Proof. exact (fun n : nat => @lem218399 n h1). Qed.
Lemma lem218401 : term22.
Proof. exact (fun h0 : term12 => @lem218400 h0). Qed.
Lemma lem218402 : term21.
Proof. exact (@lem218401 (@lem157261)). Qed.
Lemma lem218403 (n : nat) : term23 n.
Proof. exact (@lem218402 n). Qed.
Lemma lem218404 (n : nat) : (term23 n) = (term20 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem218406 (p : nat) : term24 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem218407 (p : nat) : (term24 p) = (term25 p).
Proof. exact (eq_refl (term24 p)). Qed.
Lemma lem218408 (p : nat) : term25 p.
Proof. exact (EQ_MP (@lem218407 p) (@lem218406 p)). Qed.
Lemma lem218410 (p : nat) (h1 : term17 p) : term17 p.
Proof. exact (h1). Qed.
Lemma lem218411 : term26.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem218437 : term27.
Proof. exact (proj1 (@lem218411)). Qed.
Lemma lem218438 (m : nat) : term28 m.
Proof. exact (@lem218437 m). Qed.
Lemma lem218439 (m : nat) : (term28 m) = ((term29 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem218445 (n : nat) : term30 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem218446 (n : nat) : (term30 n) = ((term31 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem218448 (n : nat) : term32 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem218449 (n : nat) : (term32 n) = (Peano.le n n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem218450 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem218449 n) (@lem218448 n)). Qed.
Lemma lem218451 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem218456 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem218457 (n : nat) : (Nat.div n) = (Nat.div n).
Proof. exact (eq_refl (Nat.div n)). Qed.
Lemma lem218458 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (term31 n).
Proof. exact (MK_COMB (@lem218457 n) (@lem218456 p h1)). Qed.
Lemma lem218460 (n : nat) : (term31 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem218446 n) (@lem218445 n)). Qed.
Lemma lem218461 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem218458 n p h1) (@lem218460 n)). Qed.
Lemma lem218462 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem218463 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term33 m n p) = (term29 m).
Proof. exact (MK_COMB (@lem218462 m) (@lem218461 n p h1)). Qed.
Lemma lem218465 (m : nat) : (term29 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem218439 m) (@lem218438 m)). Qed.
Lemma lem218466 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term33 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem218463 n m p h1) (@lem218465 m)). Qed.
Lemma lem218467 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem218468 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term34 m n p) = term35.
Proof. exact (MK_COMB (@lem218467) (@lem218466 m n p h1)). Qed.
Lemma lem218470 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem218471 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem218472 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term37 m n p) = (term38 m n).
Proof. exact (MK_COMB (@lem218471 m n) (@lem218470 p h1)). Qed.
Lemma lem218474 (n : nat) : (term31 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem218446 n) (@lem218445 n)). Qed.
Lemma lem218475 (m : nat) (n : nat) : (term38 m n) = (NUMERAL 0).
Proof. exact (@lem218474 (Nat.mul m n)). Qed.
Lemma lem218476 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term37 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem218472 m n p h1) (@lem218475 m n)). Qed.
Lemma lem218477 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term39 m n p) = term40.
Proof. exact (MK_COMB (@lem218468 m n p h1) (@lem218476 m n p h1)). Qed.
Lemma lem218479 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem218451 n) (@lem218450 n)). Qed.
Lemma lem218480 : term40 = True.
Proof. exact (@lem218479 (NUMERAL 0)). Qed.
Lemma lem218481 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term39 m n p) = True.
Proof. exact (TRANS (@lem218477 m n p h1) (@lem218480)). Qed.
Lemma lem218482 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = (term39 m n p).
Proof. exact (SYM (@lem218481 m n p h1)). Qed.
Lemma lem218483 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term39 m n p.
Proof. exact (EQ_MP (@lem218482 m n p h1) (@lem0)). Qed.
Lemma lem218543 (a : nat) : term41 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem218544 (a : nat) : (term41 a) = (term42 a).
Proof. exact (eq_refl (term41 a)). Qed.
Lemma lem218545 (a : nat) : term42 a.
Proof. exact (EQ_MP (@lem218544 a) (@lem218543 a)). Qed.
Lemma lem218546 (a : nat) (b : nat) : term43 a b.
Proof. exact (@lem218545 a b). Qed.
Lemma lem218547 (a : nat) (b : nat) : (term43 a b) = (term44 a b).
Proof. exact (eq_refl (term43 a b)). Qed.
Lemma lem218548 (a : nat) (b : nat) : term44 a b.
Proof. exact (EQ_MP (@lem218547 a b) (@lem218546 a b)). Qed.
Lemma lem218549 (a : nat) (b : nat) (n : nat) : term45 a b n.
Proof. exact (@lem218548 a b n). Qed.
Lemma lem218550 (a : nat) (n : nat) (b : nat) : (term45 a b n) = (term46 a n b).
Proof. exact (eq_refl (term45 a b n)). Qed.
Lemma lem218551 (a : nat) (n : nat) (b : nat) : term46 a n b.
Proof. exact (EQ_MP (@lem218550 a n b) (@lem218549 a b n)). Qed.
Lemma lem218552 (a : nat) (h1 : term17 a) : term17 a.
Proof. exact (h1). Qed.
Lemma lem218553 (n : nat) (b : nat) (a : nat) (h1 : term17 a) : (term47 n b a) = (term48 a n b).
Proof. exact (@lem218551 a n b (@lem218552 a h1)). Qed.
Lemma lem218559 (p : nat) : term49 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem218573 (a : nat) (n : nat) (b : nat) : term46 a n b.
Proof. exact (fun h0 : term17 a => @lem218553 n b a h0). Qed.
Lemma lem218574 (p : nat) (m : nat) (n : nat) : term50 p m n.
Proof. exact (@lem218573 p (term33 m n p) (Nat.mul m n)). Qed.
Lemma lem218576 (p : nat) (h1 : term17 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem218559 p (@lem218410 p h1)). Qed.
Lemma lem218577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem218578 (p : nat) (h1 : term17 p) : (term17 p) = (~ False).
Proof. exact (MK_COMB (@lem218577) (@lem218576 p h1)). Qed.
Lemma lem218580 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem218581 (p : nat) (h1 : term17 p) : (term17 p) = True.
Proof. exact (TRANS (@lem218578 p h1) (@lem218580)). Qed.
Lemma lem218582 (p : nat) (h1 : term17 p) : True = (term17 p).
Proof. exact (SYM (@lem218581 p h1)). Qed.
Lemma lem218583 (p : nat) (h1 : term17 p) : term17 p.
Proof. exact (EQ_MP (@lem218582 p h1) (@lem0)). Qed.
Lemma lem218584 (m : nat) (n : nat) (p : nat) (h1 : term17 p) : (term39 m n p) = (term51 p m n).
Proof. exact (@lem218574 p m n (@lem218583 p h1)). Qed.
Lemma lem218585 (m : nat) (n : nat) (p : nat) (h1 : term17 p) : (term51 p m n) = (term39 m n p).
Proof. exact (SYM (@lem218584 m n p h1)). Qed.
Lemma lem218587 (n : nat) : term20 n.
Proof. exact (EQ_MP (@lem218404 n) (@lem218403 n)). Qed.
Lemma lem218588 (p : nat) : term20 p.
Proof. exact (@lem218587 p). Qed.
Lemma lem218589 (p : nat) (h1 : term17 p) : term19 p.
Proof. exact (@lem218588 p (@lem218410 p h1)). Qed.
Lemma lem218590 (n : nat) (p : nat) (h1 : term17 p) : term52 p n.
Proof. exact (@lem218589 p h1 n). Qed.
Lemma lem218591 (n : nat) (p : nat) : (term52 p n) = (term18 n p).
Proof. exact (eq_refl (term52 p n)). Qed.
Lemma lem218592 (n : nat) (p : nat) (h1 : term17 p) : term18 n p.
Proof. exact (EQ_MP (@lem218591 n p) (@lem218590 n p h1)). Qed.
Lemma lem218593 (n : nat) (p : nat) (h1 : term18 n p) : term18 n p.
Proof. exact (h1). Qed.
Lemma lem218596 (n : nat) (p : nat) (h1 : term18 n p) : n = (term53 n p).
Proof. exact (proj1 (@lem218593 n p h1)). Qed.
Lemma lem218597 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem218598 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : (Nat.mul m n) = (term54 m n p).
Proof. exact (MK_COMB (@lem218597 m) (@lem218596 n p h1)). Qed.
Lemma lem218599 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term55 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem218600 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : (term51 p m n) = (term56 m n p).
Proof. exact (MK_COMB (@lem218599 m n p) (@lem218598 m n p h1)). Qed.
Lemma lem218601 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : (term56 m n p) = (term51 p m n).
Proof. exact (SYM (@lem218600 m n p h1)). Qed.
Lemma lem218603 (n : nat) (m : nat) (p : nat) : (term10 m n p) = (term11 n m p).
Proof. exact (EQ_MP (@lem218387 n m p) (@lem218386 n m p)). Qed.
Lemma lem218604 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term57 m n p).
Proof. exact (@lem218603 (term58 n p) m (Nat.modulo n p)). Qed.
Lemma lem218605 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term55 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem218606 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term59 m n p).
Proof. exact (MK_COMB (@lem218605 m n p) (@lem218604 m n p)). Qed.
Lemma lem218607 (m : nat) (n : nat) (p : nat) : (term59 m n p) = (term56 m n p).
Proof. exact (SYM (@lem218606 m n p)). Qed.
Lemma lem218611 (n : nat) (m : nat) (p : nat) : (term60 m n p) = (term60 n m p).
Proof. exact (proj2 (@lem218376 n m p)). Qed.
Lemma lem218612 (m : nat) (n : nat) (p : nat) : (term61 m n p) = (term62 m n p).
Proof. exact (@lem218611 m p (Nat.div n p)). Qed.
Lemma lem218622 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem218623 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term63 m n p).
Proof. exact (MK_COMB (@lem218622) (@lem218612 m n p)). Qed.
Lemma lem218631 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem218632 (n : nat) (p : nat) : (term58 n p) = (term64 n p).
Proof. exact (@lem218631 p (Nat.div n p)). Qed.
Lemma lem218636 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem218637 (m : nat) (n : nat) (p : nat) : (term65 m n p) = (term62 m n p).
Proof. exact (MK_COMB (@lem218636 m) (@lem218632 n p)). Qed.
Lemma lem218644 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem218645 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term67 m n p).
Proof. exact (MK_COMB (@lem218644) (@lem218637 m n p)). Qed.
Lemma lem218649 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term68 m n p).
Proof. exact (eq_refl (term68 m n p)). Qed.
Lemma lem218650 (m : nat) (n : nat) (p : nat) : (term57 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem218645 m n p) (@lem218649 m n p)). Qed.
Lemma lem218651 (m : nat) (n : nat) (p : nat) : (term59 m n p) = (term70 m n p).
Proof. exact (MK_COMB (@lem218623 m n p) (@lem218650 m n p)). Qed.
Lemma lem218653 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem218374 m n) (@lem218373 m n)). Qed.
Lemma lem218654 (m : nat) (n : nat) (p : nat) : (term70 m n p) = True.
Proof. exact (@lem218653 (term62 m n p) (term68 m n p)). Qed.
Lemma lem218655 (m : nat) (n : nat) (p : nat) : (term59 m n p) = True.
Proof. exact (TRANS (@lem218651 m n p) (@lem218654 m n p)). Qed.
Lemma lem218656 (m : nat) (n : nat) (p : nat) : True = (term59 m n p).
Proof. exact (SYM (@lem218655 m n p)). Qed.
Lemma lem218657 (m : nat) (n : nat) (p : nat) : term59 m n p.
Proof. exact (EQ_MP (@lem218656 m n p) (@lem0)). Qed.
Lemma lem218658 (m : nat) (n : nat) (p : nat) : term56 m n p.
Proof. exact (EQ_MP (@lem218607 m n p) (@lem218657 m n p)). Qed.
Lemma lem218659 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : term51 p m n.
Proof. exact (EQ_MP (@lem218601 m n p h1) (@lem218658 m n p)). Qed.
Lemma lem218660 (p : nat) (m : nat) (n : nat) : term71 p m n.
Proof. exact (fun h0 : term18 n p => @lem218659 m n p h0). Qed.
Lemma lem218661 (m : nat) (n : nat) (p : nat) (h1 : term17 p) : term51 p m n.
Proof. exact (@lem218660 p m n (@lem218592 n p h1)). Qed.
Lemma lem218663 (m : nat) (n : nat) (p : nat) (h1 : term17 p) : term39 m n p.
Proof. exact (EQ_MP (@lem218585 m n p h1) (@lem218661 m n p h1)). Qed.
Lemma lem218664 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (or_elim (@lem218408 p) (fun h0 : p = (NUMERAL 0) => @lem218483 m n p h0) (fun h0 : term17 p => @lem218663 m n p h0)). Qed.
Lemma lem218669 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun p : nat => @lem218664 m n p). Qed.
Lemma lem218674 (m : nat) : term73 m.
Proof. exact (fun n : nat => @lem218669 m n). Qed.
Lemma lem218679 : term74.
Proof. exact (fun m : nat => @lem218674 m). Qed.
