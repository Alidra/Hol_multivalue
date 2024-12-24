Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1250723_term_abbrevs.
Require Import ADD_AC_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1250378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250379 (x : nat) : (x = x) = True.
Proof. exact (@lem1250378 nat x). Qed.
Lemma lem1250380 (p : nat) : (p = p) = True.
Proof. exact (@lem1250379 p). Qed.
Lemma lem1250381 (p : nat) : True = (p = p).
Proof. exact (SYM (@lem1250380 p)). Qed.
Lemma lem1250382 (p : nat) : p = p.
Proof. exact (EQ_MP (@lem1250381 p) (@lem0)). Qed.
Lemma lem1250386 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250387 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term2 p d''' d' d'') = (term3 p d''' d' d'').
Proof. exact (@lem1250386 (term4 p d' d'' d''') d' d''). Qed.
Lemma lem1250389 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250390 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term3 p d''' d' d'') = (term5 p d''' d' d'').
Proof. exact (@lem1250389 p (term6 d' d'' d''') (Nat.add d' d'')). Qed.
Lemma lem1250397 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term2 p d''' d' d'') = (term5 p d''' d' d'').
Proof. exact (TRANS (@lem1250387 p d''' d' d'') (@lem1250390 p d''' d' d'')). Qed.
Lemma lem1250399 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250400 (d''' : nat) (d' : nat) (d'' : nat) : (term7 d''' d' d'') = (term8 d''' d' d'').
Proof. exact (@lem1250399 (Nat.add d' d'') (S d''') (Nat.add d' d'')). Qed.
Lemma lem1250402 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250403 (d''' : nat) (d' : nat) (d'' : nat) : (term8 d''' d' d'') = (term9 d''' d' d'').
Proof. exact (@lem1250402 d' d'' (term10 d''' d' d'')). Qed.
Lemma lem1250410 (d''' : nat) (d' : nat) (d'' : nat) : (term7 d''' d' d'') = (term9 d''' d' d'').
Proof. exact (TRANS (@lem1250400 d''' d' d'') (@lem1250403 d''' d' d'')). Qed.
Lemma lem1250418 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250419 (d' : nat) (d''' : nat) (d'' : nat) : (term10 d''' d' d'') = (term11 d' d''' d'').
Proof. exact (@lem1250418 d' (S d''') d''). Qed.
Lemma lem1250427 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1250428 (d'' : nat) (d''' : nat) : (term12 d''' d'') = (term13 d'' d''').
Proof. exact (@lem1250427 d'' (S d''')). Qed.
Lemma lem1250432 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250433 (d' : nat) (d'' : nat) (d''' : nat) : (term11 d' d''' d'') = (term14 d' d'' d''').
Proof. exact (MK_COMB (@lem1250432 d') (@lem1250428 d'' d''')). Qed.
Lemma lem1250440 (d' : nat) (d'' : nat) (d''' : nat) : (term10 d''' d' d'') = (term14 d' d'' d''').
Proof. exact (TRANS (@lem1250419 d' d''' d'') (@lem1250433 d' d'' d''')). Qed.
Lemma lem1250441 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250442 (d' : nat) (d'' : nat) (d''' : nat) : (term15 d''' d' d'') = (term16 d' d'' d''').
Proof. exact (MK_COMB (@lem1250441 d'') (@lem1250440 d' d'' d''')). Qed.
Lemma lem1250444 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250445 (d' : nat) (d'' : nat) (d''' : nat) : (term16 d' d'' d''') = (term17 d' d'' d''').
Proof. exact (@lem1250444 d' d'' (term13 d'' d''')). Qed.
Lemma lem1250461 (d' : nat) (d'' : nat) (d''' : nat) : (term15 d''' d' d'') = (term17 d' d'' d''').
Proof. exact (TRANS (@lem1250442 d' d'' d''') (@lem1250445 d' d'' d''')). Qed.
Lemma lem1250462 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250463 (d' : nat) (d'' : nat) (d''' : nat) : (term9 d''' d' d'') = (term18 d' d'' d''').
Proof. exact (MK_COMB (@lem1250462 d') (@lem1250461 d' d'' d''')). Qed.
Lemma lem1250470 (d' : nat) (d'' : nat) (d''' : nat) : (term7 d''' d' d'') = (term18 d' d'' d''').
Proof. exact (TRANS (@lem1250410 d''' d' d'') (@lem1250463 d' d'' d''')). Qed.
Lemma lem1250471 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1250472 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term5 p d''' d' d'') = (term19 p d' d'' d''').
Proof. exact (MK_COMB (@lem1250471 p) (@lem1250470 d' d'' d''')). Qed.
Lemma lem1250474 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250475 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term19 p d' d'' d''') = (term20 p d' d'' d''').
Proof. exact (@lem1250474 d' p (term17 d' d'' d''')). Qed.
Lemma lem1250483 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250484 (d' : nat) (p : nat) (d'' : nat) (d''' : nat) : (term21 p d' d'' d''') = (term21 d' p d'' d''').
Proof. exact (@lem1250483 d' p (term22 d'' d''')). Qed.
Lemma lem1250492 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250493 (p : nat) (d'' : nat) (d''' : nat) : (term17 p d'' d''') = (term16 p d'' d''').
Proof. exact (@lem1250492 d'' p (term13 d'' d''')). Qed.
Lemma lem1250501 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250502 (d'' : nat) (p : nat) (d''' : nat) : (term14 p d'' d''') = (term14 d'' p d''').
Proof. exact (@lem1250501 d'' p (S d''')). Qed.
Lemma lem1250512 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250513 (d'' : nat) (p : nat) (d''' : nat) : (term16 p d'' d''') = (term23 d'' p d''').
Proof. exact (MK_COMB (@lem1250512 d'') (@lem1250502 d'' p d''')). Qed.
Lemma lem1250520 (d'' : nat) (p : nat) (d''' : nat) : (term17 p d'' d''') = (term23 d'' p d''').
Proof. exact (TRANS (@lem1250493 p d'' d''') (@lem1250513 d'' p d''')). Qed.
Lemma lem1250521 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250522 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term21 d' p d'' d''') = (term24 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250521 d') (@lem1250520 d'' p d''')). Qed.
Lemma lem1250529 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term21 p d' d'' d''') = (term24 d' d'' p d''').
Proof. exact (TRANS (@lem1250484 d' p d'' d''') (@lem1250522 d' d'' p d''')). Qed.
Lemma lem1250530 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250531 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term20 p d' d'' d''') = (term25 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250530 d') (@lem1250529 d' d'' p d''')). Qed.
Lemma lem1250538 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term19 p d' d'' d''') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250475 p d' d'' d''') (@lem1250531 d' d'' p d''')). Qed.
Lemma lem1250539 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 p d''' d' d'') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250472 p d' d'' d''') (@lem1250538 d' d'' p d''')). Qed.
Lemma lem1250540 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term2 p d''' d' d'') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250397 p d''' d' d'') (@lem1250539 d' d'' p d''')). Qed.
Lemma lem1250541 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250542 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term26 p d''' d' d'') = (term27 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250541) (@lem1250540 d' d'' p d''')). Qed.
Lemma lem1250544 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250545 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term19 p d'' d' d''') = (term20 p d'' d' d''').
Proof. exact (@lem1250544 d'' p (term17 d'' d' d''')). Qed.
Lemma lem1250553 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250554 (d'' : nat) (p : nat) (d' : nat) (d''' : nat) : (term21 p d'' d' d''') = (term21 d'' p d' d''').
Proof. exact (@lem1250553 d'' p (term22 d' d''')). Qed.
Lemma lem1250562 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250563 (p : nat) (d' : nat) (d''' : nat) : (term17 p d' d''') = (term16 p d' d''').
Proof. exact (@lem1250562 d' p (term13 d' d''')). Qed.
Lemma lem1250571 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250572 (d' : nat) (p : nat) (d''' : nat) : (term14 p d' d''') = (term14 d' p d''').
Proof. exact (@lem1250571 d' p (S d''')). Qed.
Lemma lem1250582 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250583 (d' : nat) (p : nat) (d''' : nat) : (term16 p d' d''') = (term23 d' p d''').
Proof. exact (MK_COMB (@lem1250582 d') (@lem1250572 d' p d''')). Qed.
Lemma lem1250590 (d' : nat) (p : nat) (d''' : nat) : (term17 p d' d''') = (term23 d' p d''').
Proof. exact (TRANS (@lem1250563 p d' d''') (@lem1250583 d' p d''')). Qed.
Lemma lem1250591 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250592 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term21 d'' p d' d''') = (term24 d'' d' p d''').
Proof. exact (MK_COMB (@lem1250591 d'') (@lem1250590 d' p d''')). Qed.
Lemma lem1250594 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250595 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term24 d'' d' p d''') = (term28 d'' d' p d''').
Proof. exact (@lem1250594 d' d'' (term14 d' p d''')). Qed.
Lemma lem1250603 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250604 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term29 d'' d' p d''') = (term29 d' d'' p d''').
Proof. exact (@lem1250603 d' d'' (term13 p d''')). Qed.
Lemma lem1250620 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250621 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term28 d'' d' p d''') = (term30 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250620 d') (@lem1250604 d' d'' p d''')). Qed.
Lemma lem1250628 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term24 d'' d' p d''') = (term30 d' d'' p d''').
Proof. exact (TRANS (@lem1250595 d'' d' p d''') (@lem1250621 d' d'' p d''')). Qed.
Lemma lem1250629 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term21 d'' p d' d''') = (term30 d' d'' p d''').
Proof. exact (TRANS (@lem1250592 d'' d' p d''') (@lem1250628 d' d'' p d''')). Qed.
Lemma lem1250630 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term21 p d'' d' d''') = (term30 d' d'' p d''').
Proof. exact (TRANS (@lem1250554 d'' p d' d''') (@lem1250629 d' d'' p d''')). Qed.
Lemma lem1250631 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250632 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term20 p d'' d' d''') = (term31 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250631 d'') (@lem1250630 d' d'' p d''')). Qed.
Lemma lem1250634 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250635 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term31 d' d'' p d''') = (term32 d' d'' p d''').
Proof. exact (@lem1250634 d' d'' (term29 d' d'' p d''')). Qed.
Lemma lem1250643 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250644 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term28 d' d'' p d''') = (term24 d' d'' p d''').
Proof. exact (@lem1250643 d' d'' (term14 d'' p d''')). Qed.
Lemma lem1250666 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250667 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term32 d' d'' p d''') = (term25 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250666 d') (@lem1250644 d' d'' p d''')). Qed.
Lemma lem1250674 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term31 d' d'' p d''') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250635 d' d'' p d''') (@lem1250667 d' d'' p d''')). Qed.
Lemma lem1250675 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term20 p d'' d' d''') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250632 d' d'' p d''') (@lem1250674 d' d'' p d''')). Qed.
Lemma lem1250676 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term19 p d'' d' d''') = (term25 d' d'' p d''').
Proof. exact (TRANS (@lem1250545 p d'' d' d''') (@lem1250675 d' d'' p d''')). Qed.
Lemma lem1250677 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term2 p d''' d' d'') = (term19 p d'' d' d''')) = ((term25 d' d'' p d''') = (term25 d' d'' p d''')).
Proof. exact (MK_COMB (@lem1250542 d' d'' p d''') (@lem1250676 d' d'' p d''')). Qed.
Lemma lem1250679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250680 (x : nat) : (x = x) = True.
Proof. exact (@lem1250679 nat x). Qed.
Lemma lem1250681 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term25 d' d'' p d''') = (term25 d' d'' p d''')) = True.
Proof. exact (@lem1250680 (term25 d' d'' p d''')). Qed.
Lemma lem1250682 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p d''' d' d'') = (term19 p d'' d' d''')) = True.
Proof. exact (TRANS (@lem1250677 d' d'' p d''') (@lem1250681 d' d'' p d''')). Qed.
Lemma lem1250683 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 p d''' d' d'') = (term19 p d'' d' d''')).
Proof. exact (SYM (@lem1250682 p d'' d' d''')). Qed.
Lemma lem1250684 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 p d''' d' d'') = (term19 p d'' d' d''').
Proof. exact (EQ_MP (@lem1250683 p d'' d' d''') (@lem0)). Qed.
Lemma lem1250685 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250686 (p : nat) : (@eq nat p) = (@eq nat p).
Proof. exact (MK_COMB (@lem1250685) (@lem1250382 p)). Qed.
Lemma lem1250687 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (p = (term2 p d''' d' d'')) = (p = (term19 p d'' d' d''')).
Proof. exact (MK_COMB (@lem1250686 p) (@lem1250684 p d'' d' d''')). Qed.
Lemma lem1250688 (m : nat) : term33 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1250689 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1250690 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1250689 m) (@lem1250688 m)). Qed.
Lemma lem1250691 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1250690 m n). Qed.
Lemma lem1250692 (m : nat) (n : nat) : (term35 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1250710 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250692 m n) (@lem1250691 m n)). Qed.
Lemma lem1250715 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (p = (term19 p d'' d' d''')) = ((term18 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1250710 p (term18 d'' d' d''')). Qed.
Lemma lem1250716 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term36 p d''' d' d'') = (term36 p d''' d' d'').
Proof. exact (eq_refl (term36 p d''' d' d'')). Qed.
Lemma lem1250717 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((p = (term2 p d''' d' d'')) = (p = (term19 p d'' d' d'''))) = ((p = (term2 p d''' d' d'')) = ((term18 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1250716 p d''' d' d'') (@lem1250715 p d'' d' d''')). Qed.
Lemma lem1250718 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (p = (term2 p d''' d' d'')) = ((term18 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250717 p d'' d' d''') (@lem1250687 p d'' d' d''')). Qed.
Lemma lem1250719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1250720 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term37 p d''' d' d'') = (term38 d'' d' d''').
Proof. exact (MK_COMB (@lem1250719) (@lem1250718 p d'' d' d''')). Qed.
Lemma lem1250721 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1250722 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term39 p d''' d' d'') = (term40 d'' d' d''').
Proof. exact (MK_COMB (@lem1250720 p d'' d' d''') (@lem1250721)). Qed.
Lemma lem1250723 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term40 d'' d' d''') = (term39 p d''' d' d'').
Proof. exact (SYM (@lem1250722 p d'' d' d''')). Qed.
