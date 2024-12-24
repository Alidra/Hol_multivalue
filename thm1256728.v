Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1256728_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1256356 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1256357 (x : nat) : (x = x) = True.
Proof. exact (@lem1256356 nat x). Qed.
Lemma lem1256358 (p : nat) (n : nat) (d'' : nat) : ((term0 p n d'') = (term0 p n d'')) = True.
Proof. exact (@lem1256357 (term0 p n d'')). Qed.
Lemma lem1256359 (p : nat) (n : nat) (d'' : nat) : True = ((term0 p n d'') = (term0 p n d'')).
Proof. exact (SYM (@lem1256358 p n d'')). Qed.
Lemma lem1256360 (p : nat) (n : nat) (d'' : nat) : (term0 p n d'') = (term0 p n d'').
Proof. exact (EQ_MP (@lem1256359 p n d'') (@lem0)). Qed.
Lemma lem1256364 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256365 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term2 p d'' d''' n d') = (term3 p d'' d''' n d').
Proof. exact (@lem1256364 (term4 p d' d'' d''') n d'). Qed.
Lemma lem1256367 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256368 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term3 p d'' d''' n d') = (term5 p d'' d''' n d').
Proof. exact (@lem1256367 p (term6 d' d'' d''') (Nat.add n d')). Qed.
Lemma lem1256375 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term2 p d'' d''' n d') = (term5 p d'' d''' n d').
Proof. exact (TRANS (@lem1256365 p d'' d''' n d') (@lem1256368 p d'' d''' n d')). Qed.
Lemma lem1256377 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256378 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term7 d'' d''' n d') = (term8 d'' d''' n d').
Proof. exact (@lem1256377 (Nat.add d' d'') (S d''') (Nat.add n d')). Qed.
Lemma lem1256380 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256381 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term8 d'' d''' n d') = (term9 d'' d''' n d').
Proof. exact (@lem1256380 d' d'' (term10 d''' n d')). Qed.
Lemma lem1256388 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term7 d'' d''' n d') = (term9 d'' d''' n d').
Proof. exact (TRANS (@lem1256378 d'' d''' n d') (@lem1256381 d'' d''' n d')). Qed.
Lemma lem1256396 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256397 (n : nat) (d''' : nat) (d' : nat) : (term10 d''' n d') = (term11 n d''' d').
Proof. exact (@lem1256396 n (S d''') d'). Qed.
Lemma lem1256405 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1256406 (d' : nat) (d''' : nat) : (term12 d''' d') = (term13 d' d''').
Proof. exact (@lem1256405 d' (S d''')). Qed.
Lemma lem1256410 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1256411 (n : nat) (d' : nat) (d''' : nat) : (term11 n d''' d') = (term14 n d' d''').
Proof. exact (MK_COMB (@lem1256410 n) (@lem1256406 d' d''')). Qed.
Lemma lem1256413 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256414 (d' : nat) (n : nat) (d''' : nat) : (term14 n d' d''') = (term14 d' n d''').
Proof. exact (@lem1256413 d' n (S d''')). Qed.
Lemma lem1256424 (d' : nat) (n : nat) (d''' : nat) : (term11 n d''' d') = (term14 d' n d''').
Proof. exact (TRANS (@lem1256411 n d' d''') (@lem1256414 d' n d''')). Qed.
Lemma lem1256425 (d' : nat) (n : nat) (d''' : nat) : (term10 d''' n d') = (term14 d' n d''').
Proof. exact (TRANS (@lem1256397 n d''' d') (@lem1256424 d' n d''')). Qed.
Lemma lem1256426 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256427 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term15 d'' d''' n d') = (term16 d'' d' n d''').
Proof. exact (MK_COMB (@lem1256426 d'') (@lem1256425 d' n d''')). Qed.
Lemma lem1256429 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256430 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 d'' d' n d''') = (term16 d' d'' n d''').
Proof. exact (@lem1256429 d' d'' (term13 n d''')). Qed.
Lemma lem1256446 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 d'' d''' n d') = (term16 d' d'' n d''').
Proof. exact (TRANS (@lem1256427 d'' d' n d''') (@lem1256430 d' d'' n d''')). Qed.
Lemma lem1256447 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256448 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term9 d'' d''' n d') = (term17 d' d'' n d''').
Proof. exact (MK_COMB (@lem1256447 d') (@lem1256446 d' d'' n d''')). Qed.
Lemma lem1256455 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 d'' d''' n d') = (term17 d' d'' n d''').
Proof. exact (TRANS (@lem1256388 d'' d''' n d') (@lem1256448 d' d'' n d''')). Qed.
Lemma lem1256456 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1256457 (p : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 p d'' d''' n d') = (term18 p d' d'' n d''').
Proof. exact (MK_COMB (@lem1256456 p) (@lem1256455 d' d'' n d''')). Qed.
Lemma lem1256459 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256460 (p : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term18 p d' d'' n d''') = (term19 p d' d'' n d''').
Proof. exact (@lem1256459 d' p (term16 d' d'' n d''')). Qed.
Lemma lem1256468 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256469 (d' : nat) (p : nat) (d'' : nat) (n : nat) (d''' : nat) : (term20 p d' d'' n d''') = (term20 d' p d'' n d''').
Proof. exact (@lem1256468 d' p (term14 d'' n d''')). Qed.
Lemma lem1256477 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256478 (d'' : nat) (p : nat) (n : nat) (d''' : nat) : (term16 p d'' n d''') = (term16 d'' p n d''').
Proof. exact (@lem1256477 d'' p (term13 n d''')). Qed.
Lemma lem1256486 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256487 (n : nat) (p : nat) (d''' : nat) : (term14 p n d''') = (term14 n p d''').
Proof. exact (@lem1256486 n p (S d''')). Qed.
Lemma lem1256497 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256498 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 d'' p n d''') = (term16 d'' n p d''').
Proof. exact (MK_COMB (@lem1256497 d'') (@lem1256487 n p d''')). Qed.
Lemma lem1256505 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 p d'' n d''') = (term16 d'' n p d''').
Proof. exact (TRANS (@lem1256478 d'' p n d''') (@lem1256498 d'' n p d''')). Qed.
Lemma lem1256506 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256507 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term20 d' p d'' n d''') = (term20 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1256506 d') (@lem1256505 d'' n p d''')). Qed.
Lemma lem1256514 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term20 p d' d'' n d''') = (term20 d' d'' n p d''').
Proof. exact (TRANS (@lem1256469 d' p d'' n d''') (@lem1256507 d' d'' n p d''')). Qed.
Lemma lem1256515 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256516 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term19 p d' d'' n d''') = (term21 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1256515 d') (@lem1256514 d' d'' n p d''')). Qed.
Lemma lem1256523 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term18 p d' d'' n d''') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256460 p d' d'' n d''') (@lem1256516 d' d'' n p d''')). Qed.
Lemma lem1256524 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term5 p d'' d''' n d') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256457 p d' d'' n d''') (@lem1256523 d' d'' n p d''')). Qed.
Lemma lem1256525 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term2 p d'' d''' n d') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256375 p d'' d''' n d') (@lem1256524 d' d'' n p d''')). Qed.
Lemma lem1256526 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256527 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term22 p d'' d''' n d') = (term23 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1256526) (@lem1256525 d' d'' n p d''')). Qed.
Lemma lem1256529 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256530 (n : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term24 p n d'' d' d''') = (term24 n p d'' d' d''').
Proof. exact (@lem1256529 n p (term25 d'' d' d''')). Qed.
Lemma lem1256538 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256539 (d'' : nat) (p : nat) (d' : nat) (d''' : nat) : (term26 p d'' d' d''') = (term26 d'' p d' d''').
Proof. exact (@lem1256538 d'' p (term27 d' d''')). Qed.
Lemma lem1256547 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256548 (p : nat) (d' : nat) (d''' : nat) : (term25 p d' d''') = (term28 p d' d''').
Proof. exact (@lem1256547 d' p (term13 d' d''')). Qed.
Lemma lem1256556 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256557 (d' : nat) (p : nat) (d''' : nat) : (term14 p d' d''') = (term14 d' p d''').
Proof. exact (@lem1256556 d' p (S d''')). Qed.
Lemma lem1256567 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256568 (d' : nat) (p : nat) (d''' : nat) : (term28 p d' d''') = (term29 d' p d''').
Proof. exact (MK_COMB (@lem1256567 d') (@lem1256557 d' p d''')). Qed.
Lemma lem1256575 (d' : nat) (p : nat) (d''' : nat) : (term25 p d' d''') = (term29 d' p d''').
Proof. exact (TRANS (@lem1256548 p d' d''') (@lem1256568 d' p d''')). Qed.
Lemma lem1256576 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256577 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term26 d'' p d' d''') = (term30 d'' d' p d''').
Proof. exact (MK_COMB (@lem1256576 d'') (@lem1256575 d' p d''')). Qed.
Lemma lem1256579 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256580 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term30 d'' d' p d''') = (term31 d'' d' p d''').
Proof. exact (@lem1256579 d' d'' (term14 d' p d''')). Qed.
Lemma lem1256588 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256589 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term16 d'' d' p d''') = (term16 d' d'' p d''').
Proof. exact (@lem1256588 d' d'' (term13 p d''')). Qed.
Lemma lem1256605 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256606 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term31 d'' d' p d''') = (term17 d' d'' p d''').
Proof. exact (MK_COMB (@lem1256605 d') (@lem1256589 d' d'' p d''')). Qed.
Lemma lem1256613 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term30 d'' d' p d''') = (term17 d' d'' p d''').
Proof. exact (TRANS (@lem1256580 d'' d' p d''') (@lem1256606 d' d'' p d''')). Qed.
Lemma lem1256614 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term26 d'' p d' d''') = (term17 d' d'' p d''').
Proof. exact (TRANS (@lem1256577 d'' d' p d''') (@lem1256613 d' d'' p d''')). Qed.
Lemma lem1256615 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term26 p d'' d' d''') = (term17 d' d'' p d''').
Proof. exact (TRANS (@lem1256539 d'' p d' d''') (@lem1256614 d' d'' p d''')). Qed.
Lemma lem1256616 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1256617 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term24 n p d'' d' d''') = (term18 n d' d'' p d''').
Proof. exact (MK_COMB (@lem1256616 n) (@lem1256615 d' d'' p d''')). Qed.
Lemma lem1256619 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256620 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term18 n d' d'' p d''') = (term19 n d' d'' p d''').
Proof. exact (@lem1256619 d' n (term16 d' d'' p d''')). Qed.
Lemma lem1256628 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256629 (d' : nat) (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term20 n d' d'' p d''') = (term20 d' n d'' p d''').
Proof. exact (@lem1256628 d' n (term14 d'' p d''')). Qed.
Lemma lem1256637 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256638 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 n d'' p d''') = (term16 d'' n p d''').
Proof. exact (@lem1256637 d'' n (term13 p d''')). Qed.
Lemma lem1256654 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256655 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term20 d' n d'' p d''') = (term20 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1256654 d') (@lem1256638 d'' n p d''')). Qed.
Lemma lem1256662 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term20 n d' d'' p d''') = (term20 d' d'' n p d''').
Proof. exact (TRANS (@lem1256629 d' n d'' p d''') (@lem1256655 d' d'' n p d''')). Qed.
Lemma lem1256663 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256664 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term19 n d' d'' p d''') = (term21 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1256663 d') (@lem1256662 d' d'' n p d''')). Qed.
Lemma lem1256671 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term18 n d' d'' p d''') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256620 n d' d'' p d''') (@lem1256664 d' d'' n p d''')). Qed.
Lemma lem1256672 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term24 n p d'' d' d''') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256617 n d' d'' p d''') (@lem1256671 d' d'' n p d''')). Qed.
Lemma lem1256673 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term24 p n d'' d' d''') = (term21 d' d'' n p d''').
Proof. exact (TRANS (@lem1256530 n p d'' d' d''') (@lem1256672 d' d'' n p d''')). Qed.
Lemma lem1256674 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term2 p d'' d''' n d') = (term24 p n d'' d' d''')) = ((term21 d' d'' n p d''') = (term21 d' d'' n p d''')).
Proof. exact (MK_COMB (@lem1256527 d' d'' n p d''') (@lem1256673 d' d'' n p d''')). Qed.
Lemma lem1256676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1256677 (x : nat) : (x = x) = True.
Proof. exact (@lem1256676 nat x). Qed.
Lemma lem1256678 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term21 d' d'' n p d''') = (term21 d' d'' n p d''')) = True.
Proof. exact (@lem1256677 (term21 d' d'' n p d''')). Qed.
Lemma lem1256679 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p d'' d''' n d') = (term24 p n d'' d' d''')) = True.
Proof. exact (TRANS (@lem1256674 d' d'' n p d''') (@lem1256678 d' d'' n p d''')). Qed.
Lemma lem1256680 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 p d'' d''' n d') = (term24 p n d'' d' d''')).
Proof. exact (SYM (@lem1256679 p n d'' d' d''')). Qed.
Lemma lem1256681 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 p d'' d''' n d') = (term24 p n d'' d' d''').
Proof. exact (EQ_MP (@lem1256680 p n d'' d' d''') (@lem0)). Qed.
Lemma lem1256682 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256683 (p : nat) (n : nat) (d'' : nat) : (term32 p n d'') = (term32 p n d'').
Proof. exact (MK_COMB (@lem1256682) (@lem1256360 p n d'')). Qed.
Lemma lem1256684 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term2 p d'' d''' n d')) = ((term0 p n d'') = (term24 p n d'' d' d''')).
Proof. exact (MK_COMB (@lem1256683 p n d'') (@lem1256681 p n d'' d' d''')). Qed.
Lemma lem1256685 (m : nat) : term33 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1256686 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1256687 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1256686 m) (@lem1256685 m)). Qed.
Lemma lem1256688 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1256687 m n). Qed.
Lemma lem1256689 (m : nat) (n : nat) : (term35 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1256697 (m : nat) : term36 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1256698 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1256699 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1256698 m) (@lem1256697 m)). Qed.
Lemma lem1256700 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1256699 m n). Qed.
Lemma lem1256701 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1256702 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1256701 m n) (@lem1256700 m n)). Qed.
Lemma lem1256703 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1256702 m n p). Qed.
Lemma lem1256704 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1256707 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1256704 m n p) (@lem1256703 m n p)). Qed.
Lemma lem1256708 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term24 p n d'' d' d''')) = ((Nat.add n d'') = (term26 n d'' d' d''')).
Proof. exact (@lem1256707 p (Nat.add n d'') (term26 n d'' d' d''')). Qed.
Lemma lem1256710 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1256704 m n p) (@lem1256703 m n p)). Qed.
Lemma lem1256711 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n d'') = (term26 n d'' d' d''')) = (d'' = (term25 d'' d' d''')).
Proof. exact (@lem1256710 n d'' (term25 d'' d' d''')). Qed.
Lemma lem1256713 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1256689 m n) (@lem1256688 m n)). Qed.
Lemma lem1256718 (d'' : nat) (d' : nat) (d''' : nat) : (d'' = (term25 d'' d' d''')) = ((term27 d' d''') = (NUMERAL 0)).
Proof. exact (@lem1256713 d'' (term27 d' d''')). Qed.
Lemma lem1256719 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n d'') = (term26 n d'' d' d''')) = ((term27 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1256711 n d'' d' d''') (@lem1256718 d'' d' d''')). Qed.
Lemma lem1256720 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term24 p n d'' d' d''')) = ((term27 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1256708 p n d'' d' d''') (@lem1256719 n d'' d' d''')). Qed.
Lemma lem1256721 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term41 p d'' d''' n d') = (term41 p d'' d''' n d').
Proof. exact (eq_refl (term41 p d'' d''' n d')). Qed.
Lemma lem1256722 (p : nat) (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (((term0 p n d'') = (term2 p d'' d''' n d')) = ((term0 p n d'') = (term24 p n d'' d' d'''))) = (((term0 p n d'') = (term2 p d'' d''' n d')) = ((term27 d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1256721 p d'' d''' n d') (@lem1256720 p n d'' d' d''')). Qed.
Lemma lem1256723 (p : nat) (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term2 p d'' d''' n d')) = ((term27 d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1256722 p d'' n d' d''') (@lem1256684 p n d'' d' d''')). Qed.
Lemma lem1256724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1256725 (p : nat) (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term42 p d'' d''' n d') = (term43 d' d''').
Proof. exact (MK_COMB (@lem1256724) (@lem1256723 p d'' n d' d''')). Qed.
Lemma lem1256726 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1256727 (p : nat) (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term44 p d'' d''' n d') = (term45 d' d''').
Proof. exact (MK_COMB (@lem1256725 p d'' n d' d''') (@lem1256726)). Qed.
Lemma lem1256728 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term45 d' d''') = (term44 p d'' d''' n d').
Proof. exact (SYM (@lem1256727 p d'' n d' d''')). Qed.
