Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1255830_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1255402 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255403 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) (n : nat) : (term2 p d' d'' d''' n) = (term3 p d' d'' d''' n).
Proof. exact (@lem1255402 p (term4 d' d'' d''') n). Qed.
Lemma lem1255411 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255412 (d' : nat) (d'' : nat) (d''' : nat) (n : nat) : (term5 d' d'' d''' n) = (term6 d' d'' d''' n).
Proof. exact (@lem1255411 (Nat.add d' d'') (S d''') n). Qed.
Lemma lem1255414 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255415 (d' : nat) (d'' : nat) (d''' : nat) (n : nat) : (term6 d' d'' d''' n) = (term7 d' d'' d''' n).
Proof. exact (@lem1255414 d' d'' (term8 d''' n)). Qed.
Lemma lem1255422 (d' : nat) (d'' : nat) (d''' : nat) (n : nat) : (term5 d' d'' d''' n) = (term7 d' d'' d''' n).
Proof. exact (TRANS (@lem1255412 d' d'' d''' n) (@lem1255415 d' d'' d''' n)). Qed.
Lemma lem1255430 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255431 (n : nat) (d''' : nat) : (term8 d''' n) = (term9 n d''').
Proof. exact (@lem1255430 n (S d''')). Qed.
Lemma lem1255435 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255436 (d'' : nat) (n : nat) (d''' : nat) : (term10 d'' d''' n) = (term11 d'' n d''').
Proof. exact (MK_COMB (@lem1255435 d'') (@lem1255431 n d''')). Qed.
Lemma lem1255443 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255444 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 d' d'' d''' n) = (term12 d' d'' n d''').
Proof. exact (MK_COMB (@lem1255443 d') (@lem1255436 d'' n d''')). Qed.
Lemma lem1255451 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 d' d'' d''' n) = (term12 d' d'' n d''').
Proof. exact (TRANS (@lem1255422 d' d'' d''' n) (@lem1255444 d' d'' n d''')). Qed.
Lemma lem1255452 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255453 (p : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term3 p d' d'' d''' n) = (term13 p d' d'' n d''').
Proof. exact (MK_COMB (@lem1255452 p) (@lem1255451 d' d'' n d''')). Qed.
Lemma lem1255455 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255456 (d' : nat) (p : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 p d' d'' n d''') = (term13 d' p d'' n d''').
Proof. exact (@lem1255455 d' p (term11 d'' n d''')). Qed.
Lemma lem1255464 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255465 (d'' : nat) (p : nat) (n : nat) (d''' : nat) : (term12 p d'' n d''') = (term12 d'' p n d''').
Proof. exact (@lem1255464 d'' p (term9 n d''')). Qed.
Lemma lem1255473 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255474 (n : nat) (p : nat) (d''' : nat) : (term11 p n d''') = (term11 n p d''').
Proof. exact (@lem1255473 n p (S d''')). Qed.
Lemma lem1255484 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255485 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 d'' p n d''') = (term12 d'' n p d''').
Proof. exact (MK_COMB (@lem1255484 d'') (@lem1255474 n p d''')). Qed.
Lemma lem1255492 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 p d'' n d''') = (term12 d'' n p d''').
Proof. exact (TRANS (@lem1255465 d'' p n d''') (@lem1255485 d'' n p d''')). Qed.
Lemma lem1255493 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255494 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 d' p d'' n d''') = (term13 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1255493 d') (@lem1255492 d'' n p d''')). Qed.
Lemma lem1255501 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 p d' d'' n d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255456 d' p d'' n d''') (@lem1255494 d' d'' n p d''')). Qed.
Lemma lem1255502 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term3 p d' d'' d''' n) = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255453 p d' d'' n d''') (@lem1255501 d' d'' n p d''')). Qed.
Lemma lem1255503 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term2 p d' d'' d''' n) = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255403 p d' d'' d''' n) (@lem1255502 d' d'' n p d''')). Qed.
Lemma lem1255504 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255505 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term14 p d' d'' d''' n) = (term15 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1255504) (@lem1255503 d' d'' n p d''')). Qed.
Lemma lem1255507 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255508 (n : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term13 p n d'' d' d''') = (term13 n p d'' d' d''').
Proof. exact (@lem1255507 n p (term11 d'' d' d''')). Qed.
Lemma lem1255516 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255517 (d'' : nat) (p : nat) (d' : nat) (d''' : nat) : (term12 p d'' d' d''') = (term12 d'' p d' d''').
Proof. exact (@lem1255516 d'' p (term9 d' d''')). Qed.
Lemma lem1255525 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255526 (d' : nat) (p : nat) (d''' : nat) : (term11 p d' d''') = (term11 d' p d''').
Proof. exact (@lem1255525 d' p (S d''')). Qed.
Lemma lem1255536 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255537 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term12 d'' p d' d''') = (term12 d'' d' p d''').
Proof. exact (MK_COMB (@lem1255536 d'') (@lem1255526 d' p d''')). Qed.
Lemma lem1255539 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255540 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term12 d'' d' p d''') = (term12 d' d'' p d''').
Proof. exact (@lem1255539 d' d'' (term9 p d''')). Qed.
Lemma lem1255556 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term12 d'' p d' d''') = (term12 d' d'' p d''').
Proof. exact (TRANS (@lem1255537 d'' d' p d''') (@lem1255540 d' d'' p d''')). Qed.
Lemma lem1255557 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term12 p d'' d' d''') = (term12 d' d'' p d''').
Proof. exact (TRANS (@lem1255517 d'' p d' d''') (@lem1255556 d' d'' p d''')). Qed.
Lemma lem1255558 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1255559 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term13 n p d'' d' d''') = (term13 n d' d'' p d''').
Proof. exact (MK_COMB (@lem1255558 n) (@lem1255557 d' d'' p d''')). Qed.
Lemma lem1255561 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255562 (d' : nat) (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term13 n d' d'' p d''') = (term13 d' n d'' p d''').
Proof. exact (@lem1255561 d' n (term11 d'' p d''')). Qed.
Lemma lem1255570 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255571 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 n d'' p d''') = (term12 d'' n p d''').
Proof. exact (@lem1255570 d'' n (term9 p d''')). Qed.
Lemma lem1255587 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255588 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 d' n d'' p d''') = (term13 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1255587 d') (@lem1255571 d'' n p d''')). Qed.
Lemma lem1255595 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 n d' d'' p d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255562 d' n d'' p d''') (@lem1255588 d' d'' n p d''')). Qed.
Lemma lem1255596 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 n p d'' d' d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255559 n d' d'' p d''') (@lem1255595 d' d'' n p d''')). Qed.
Lemma lem1255597 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term13 p n d'' d' d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1255508 n p d'' d' d''') (@lem1255596 d' d'' n p d''')). Qed.
Lemma lem1255598 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term2 p d' d'' d''' n) = (term13 p n d'' d' d''')) = ((term13 d' d'' n p d''') = (term13 d' d'' n p d''')).
Proof. exact (MK_COMB (@lem1255505 d' d'' n p d''') (@lem1255597 d' d'' n p d''')). Qed.
Lemma lem1255600 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1255601 (x : nat) : (x = x) = True.
Proof. exact (@lem1255600 nat x). Qed.
Lemma lem1255602 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term13 d' d'' n p d''') = (term13 d' d'' n p d''')) = True.
Proof. exact (@lem1255601 (term13 d' d'' n p d''')). Qed.
Lemma lem1255603 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p d' d'' d''' n) = (term13 p n d'' d' d''')) = True.
Proof. exact (TRANS (@lem1255598 d' d'' n p d''') (@lem1255602 d' d'' n p d''')). Qed.
Lemma lem1255604 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 p d' d'' d''' n) = (term13 p n d'' d' d''')).
Proof. exact (SYM (@lem1255603 p n d'' d' d''')). Qed.
Lemma lem1255605 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 p d' d'' d''' n) = (term13 p n d'' d' d''').
Proof. exact (EQ_MP (@lem1255604 p n d'' d' d''') (@lem0)). Qed.
Lemma lem1255609 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255610 (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term16 p n d'' d') = (term17 p n d'' d').
Proof. exact (@lem1255609 p (Nat.add n d'') d'). Qed.
Lemma lem1255618 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255619 (n : nat) (d'' : nat) (d' : nat) : (term0 n d'' d') = (term1 n d'' d').
Proof. exact (@lem1255618 n d'' d'). Qed.
Lemma lem1255621 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255622 (d'' : nat) (n : nat) (d' : nat) : (term1 n d'' d') = (term1 d'' n d').
Proof. exact (@lem1255621 d'' n d'). Qed.
Lemma lem1255629 (d'' : nat) (n : nat) (d' : nat) : (term0 n d'' d') = (term1 d'' n d').
Proof. exact (TRANS (@lem1255619 n d'' d') (@lem1255622 d'' n d')). Qed.
Lemma lem1255631 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255632 (d' : nat) (n : nat) : (Nat.add n d') = (Nat.add d' n).
Proof. exact (@lem1255631 d' n). Qed.
Lemma lem1255636 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255637 (d'' : nat) (d' : nat) (n : nat) : (term1 d'' n d') = (term1 d'' d' n).
Proof. exact (MK_COMB (@lem1255636 d'') (@lem1255632 d' n)). Qed.
Lemma lem1255639 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255640 (d' : nat) (d'' : nat) (n : nat) : (term1 d'' d' n) = (term1 d' d'' n).
Proof. exact (@lem1255639 d' d'' n). Qed.
Lemma lem1255650 (d' : nat) (d'' : nat) (n : nat) : (term1 d'' n d') = (term1 d' d'' n).
Proof. exact (TRANS (@lem1255637 d'' d' n) (@lem1255640 d' d'' n)). Qed.
Lemma lem1255651 (d' : nat) (d'' : nat) (n : nat) : (term0 n d'' d') = (term1 d' d'' n).
Proof. exact (TRANS (@lem1255629 d'' n d') (@lem1255650 d' d'' n)). Qed.
Lemma lem1255652 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255653 (p : nat) (d' : nat) (d'' : nat) (n : nat) : (term17 p n d'' d') = (term18 p d' d'' n).
Proof. exact (MK_COMB (@lem1255652 p) (@lem1255651 d' d'' n)). Qed.
Lemma lem1255655 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255656 (d' : nat) (p : nat) (d'' : nat) (n : nat) : (term18 p d' d'' n) = (term18 d' p d'' n).
Proof. exact (@lem1255655 d' p (Nat.add d'' n)). Qed.
Lemma lem1255664 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255665 (d'' : nat) (p : nat) (n : nat) : (term1 p d'' n) = (term1 d'' p n).
Proof. exact (@lem1255664 d'' p n). Qed.
Lemma lem1255673 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255674 (n : nat) (p : nat) : (Nat.add p n) = (Nat.add n p).
Proof. exact (@lem1255673 n p). Qed.
Lemma lem1255678 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255679 (d'' : nat) (n : nat) (p : nat) : (term1 d'' p n) = (term1 d'' n p).
Proof. exact (MK_COMB (@lem1255678 d'') (@lem1255674 n p)). Qed.
Lemma lem1255686 (d'' : nat) (n : nat) (p : nat) : (term1 p d'' n) = (term1 d'' n p).
Proof. exact (TRANS (@lem1255665 d'' p n) (@lem1255679 d'' n p)). Qed.
Lemma lem1255687 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255688 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 d' p d'' n) = (term18 d' d'' n p).
Proof. exact (MK_COMB (@lem1255687 d') (@lem1255686 d'' n p)). Qed.
Lemma lem1255695 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 p d' d'' n) = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255656 d' p d'' n) (@lem1255688 d' d'' n p)). Qed.
Lemma lem1255696 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term17 p n d'' d') = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255653 p d' d'' n) (@lem1255695 d' d'' n p)). Qed.
Lemma lem1255697 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term16 p n d'' d') = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255610 p n d'' d') (@lem1255696 d' d'' n p)). Qed.
Lemma lem1255698 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255699 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term19 p n d'' d') = (term20 d' d'' n p).
Proof. exact (MK_COMB (@lem1255698) (@lem1255697 d' d'' n p)). Qed.
Lemma lem1255701 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255702 (n : nat) (p : nat) (d'' : nat) (d' : nat) : (term18 p n d'' d') = (term18 n p d'' d').
Proof. exact (@lem1255701 n p (Nat.add d'' d')). Qed.
Lemma lem1255710 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255711 (d'' : nat) (p : nat) (d' : nat) : (term1 p d'' d') = (term1 d'' p d').
Proof. exact (@lem1255710 d'' p d'). Qed.
Lemma lem1255719 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255720 (d' : nat) (p : nat) : (Nat.add p d') = (Nat.add d' p).
Proof. exact (@lem1255719 d' p). Qed.
Lemma lem1255724 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255725 (d'' : nat) (d' : nat) (p : nat) : (term1 d'' p d') = (term1 d'' d' p).
Proof. exact (MK_COMB (@lem1255724 d'') (@lem1255720 d' p)). Qed.
Lemma lem1255727 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255728 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' d' p) = (term1 d' d'' p).
Proof. exact (@lem1255727 d' d'' p). Qed.
Lemma lem1255738 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' p d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1255725 d'' d' p) (@lem1255728 d' d'' p)). Qed.
Lemma lem1255739 (d' : nat) (d'' : nat) (p : nat) : (term1 p d'' d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1255711 d'' p d') (@lem1255738 d' d'' p)). Qed.
Lemma lem1255740 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1255741 (n : nat) (d' : nat) (d'' : nat) (p : nat) : (term18 n p d'' d') = (term18 n d' d'' p).
Proof. exact (MK_COMB (@lem1255740 n) (@lem1255739 d' d'' p)). Qed.
Lemma lem1255743 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255744 (d' : nat) (n : nat) (d'' : nat) (p : nat) : (term18 n d' d'' p) = (term18 d' n d'' p).
Proof. exact (@lem1255743 d' n (Nat.add d'' p)). Qed.
Lemma lem1255752 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255753 (d'' : nat) (n : nat) (p : nat) : (term1 n d'' p) = (term1 d'' n p).
Proof. exact (@lem1255752 d'' n p). Qed.
Lemma lem1255763 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255764 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 d' n d'' p) = (term18 d' d'' n p).
Proof. exact (MK_COMB (@lem1255763 d') (@lem1255753 d'' n p)). Qed.
Lemma lem1255771 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 n d' d'' p) = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255744 d' n d'' p) (@lem1255764 d' d'' n p)). Qed.
Lemma lem1255772 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 n p d'' d') = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255741 n d' d'' p) (@lem1255771 d' d'' n p)). Qed.
Lemma lem1255773 (d' : nat) (d'' : nat) (n : nat) (p : nat) : (term18 p n d'' d') = (term18 d' d'' n p).
Proof. exact (TRANS (@lem1255702 n p d'' d') (@lem1255772 d' d'' n p)). Qed.
Lemma lem1255774 (d' : nat) (d'' : nat) (n : nat) (p : nat) : ((term16 p n d'' d') = (term18 p n d'' d')) = ((term18 d' d'' n p) = (term18 d' d'' n p)).
Proof. exact (MK_COMB (@lem1255699 d' d'' n p) (@lem1255773 d' d'' n p)). Qed.
Lemma lem1255776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1255777 (x : nat) : (x = x) = True.
Proof. exact (@lem1255776 nat x). Qed.
Lemma lem1255778 (d' : nat) (d'' : nat) (n : nat) (p : nat) : ((term18 d' d'' n p) = (term18 d' d'' n p)) = True.
Proof. exact (@lem1255777 (term18 d' d'' n p)). Qed.
Lemma lem1255779 (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term16 p n d'' d') = (term18 p n d'' d')) = True.
Proof. exact (TRANS (@lem1255774 d' d'' n p) (@lem1255778 d' d'' n p)). Qed.
Lemma lem1255780 (p : nat) (n : nat) (d'' : nat) (d' : nat) : True = ((term16 p n d'' d') = (term18 p n d'' d')).
Proof. exact (SYM (@lem1255779 p n d'' d')). Qed.
Lemma lem1255781 (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term16 p n d'' d') = (term18 p n d'' d').
Proof. exact (EQ_MP (@lem1255780 p n d'' d') (@lem0)). Qed.
Lemma lem1255782 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255783 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term14 p d' d'' d''' n) = (term15 p n d'' d' d''').
Proof. exact (MK_COMB (@lem1255782) (@lem1255605 p n d'' d' d''')). Qed.
Lemma lem1255784 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 p d' d'' d''' n) = (term16 p n d'' d')) = ((term13 p n d'' d' d''') = (term18 p n d'' d')).
Proof. exact (MK_COMB (@lem1255783 p n d'' d' d''') (@lem1255781 p n d'' d')). Qed.
Lemma lem1255791 (m : nat) : term21 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1255792 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1255793 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1255792 m) (@lem1255791 m)). Qed.
Lemma lem1255794 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1255793 m n). Qed.
Lemma lem1255795 (m : nat) (n : nat) : (term23 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1255797 (m : nat) : term24 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1255798 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1255799 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1255798 m) (@lem1255797 m)). Qed.
Lemma lem1255800 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1255799 m n). Qed.
Lemma lem1255801 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1255802 (m : nat) (n : nat) : term27 m n.
Proof. exact (EQ_MP (@lem1255801 m n) (@lem1255800 m n)). Qed.
Lemma lem1255803 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem1255802 m n p). Qed.
Lemma lem1255804 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem1255807 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1255804 m n p) (@lem1255803 m n p)). Qed.
Lemma lem1255808 (p : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : ((term13 p n d'' d' d''') = (term18 p n d'' d')) = ((term12 n d'' d' d''') = (term1 n d'' d')).
Proof. exact (@lem1255807 p (term12 n d'' d' d''') (term1 n d'' d')). Qed.
Lemma lem1255810 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1255804 m n p) (@lem1255803 m n p)). Qed.
Lemma lem1255811 (n : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term12 n d'' d' d''') = (term1 n d'' d')) = ((term11 d'' d' d''') = (Nat.add d'' d')).
Proof. exact (@lem1255810 n (term11 d'' d' d''') (Nat.add d'' d')). Qed.
Lemma lem1255813 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1255804 m n p) (@lem1255803 m n p)). Qed.
Lemma lem1255814 (d'' : nat) (d''' : nat) (d' : nat) : ((term11 d'' d' d''') = (Nat.add d'' d')) = ((term9 d' d''') = d').
Proof. exact (@lem1255813 d'' (term9 d' d''') d'). Qed.
Lemma lem1255816 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1255795 m n) (@lem1255794 m n)). Qed.
Lemma lem1255819 (d' : nat) (d''' : nat) : ((term9 d' d''') = d') = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1255816 d' (S d''')). Qed.
Lemma lem1255820 (d'' : nat) (d' : nat) (d''' : nat) : ((term11 d'' d' d''') = (Nat.add d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1255814 d'' d''' d') (@lem1255819 d' d''')). Qed.
Lemma lem1255821 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term12 n d'' d' d''') = (term1 n d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1255811 n d''' d'' d') (@lem1255820 d'' d' d''')). Qed.
Lemma lem1255822 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term13 p n d'' d' d''') = (term18 p n d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1255808 p d''' n d'' d') (@lem1255821 n d'' d' d''')). Qed.
Lemma lem1255823 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term29 d''' p n d'' d') = (term29 d''' p n d'' d').
Proof. exact (eq_refl (term29 d''' p n d'' d')). Qed.
Lemma lem1255824 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((term2 p d' d'' d''' n) = (term16 p n d'' d')) = ((term13 p n d'' d' d''') = (term18 p n d'' d'))) = (((term2 p d' d'' d''' n) = (term16 p n d'' d')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1255823 d''' p n d'' d') (@lem1255822 p n d'' d' d''')). Qed.
Lemma lem1255825 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p d' d'' d''' n) = (term16 p n d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1255824 p n d'' d' d''') (@lem1255784 d''' p n d'' d')). Qed.
Lemma lem1255826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1255827 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term30 d''' p n d'' d') = (term31 d''').
Proof. exact (MK_COMB (@lem1255826) (@lem1255825 p n d'' d' d''')). Qed.
Lemma lem1255828 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1255829 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term32 d''' p n d'' d') = (term33 d''').
Proof. exact (MK_COMB (@lem1255827 p n d'' d' d''') (@lem1255828)). Qed.
Lemma lem1255830 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term33 d''') = (term32 d''' p n d'' d').
Proof. exact (SYM (@lem1255829 p n d'' d' d''')). Qed.
