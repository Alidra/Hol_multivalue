Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem87448 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem87449 (n : nat) (m : nat) : term1 n m.
Proof. exact (@lem87448 (term2 n m)). Qed.
Lemma lem87450 (n : nat) (m : nat) : (term3 n m) = ((term4 m n) = (term5 n m)).
Proof. exact (eq_refl (term3 n m)). Qed.
Lemma lem87451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem87452 (n : nat) (m : nat) : (term6 n m) = (term7 n m).
Proof. exact (MK_COMB (@lem87451) (@lem87450 n m)). Qed.
Lemma lem87453 (n : nat) (m : nat) (p : nat) : (term8 n m p) = ((term9 m n p) = (term10 n m p)).
Proof. exact (eq_refl (term8 n m p)). Qed.
Lemma lem87454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87455 (n : nat) (m : nat) (p : nat) : (term11 n m p) = (term12 n m p).
Proof. exact (MK_COMB (@lem87454) (@lem87453 n m p)). Qed.
Lemma lem87456 (n : nat) (m : nat) (p : nat) : (term13 n m p) = ((term14 m n p) = (term15 n m p)).
Proof. exact (eq_refl (term13 n m p)). Qed.
Lemma lem87457 (n : nat) (m : nat) (p : nat) : (term16 n m p) = (term17 n m p).
Proof. exact (MK_COMB (@lem87455 n m p) (@lem87456 n m p)). Qed.
Lemma lem87458 (n : nat) (m : nat) : (term18 n m) = (term19 n m).
Proof. exact (fun_ext (fun p : nat => @lem87457 n m p)). Qed.
Lemma lem87459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87460 (n : nat) (m : nat) : (term20 n m) = (term21 n m).
Proof. exact (MK_COMB (@lem87459) (@lem87458 n m)). Qed.
Lemma lem87461 (n : nat) (m : nat) : (term22 n m) = (term23 n m).
Proof. exact (MK_COMB (@lem87452 n m) (@lem87460 n m)). Qed.
Lemma lem87462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87463 (n : nat) (m : nat) : (term24 n m) = (term25 n m).
Proof. exact (MK_COMB (@lem87462) (@lem87461 n m)). Qed.
Lemma lem87464 (n : nat) (m : nat) (p : nat) : (term8 n m p) = ((term9 m n p) = (term10 n m p)).
Proof. exact (eq_refl (term8 n m p)). Qed.
Lemma lem87465 (n : nat) (m : nat) : (term26 n m) = (term2 n m).
Proof. exact (fun_ext (fun p : nat => @lem87464 n m p)). Qed.
Lemma lem87466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87467 (n : nat) (m : nat) : (term27 n m) = (term28 n m).
Proof. exact (MK_COMB (@lem87466) (@lem87465 n m)). Qed.
Lemma lem87468 (n : nat) (m : nat) : (term1 n m) = (term29 n m).
Proof. exact (MK_COMB (@lem87463 n m) (@lem87467 n m)). Qed.
Lemma lem87469 (n : nat) (m : nat) : term29 n m.
Proof. exact (EQ_MP (@lem87468 n m) (@lem87449 n m)). Qed.
Lemma lem87475 : term30.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem87476 : term31.
Proof. exact (proj2 (@lem87475)). Qed.
Lemma lem87477 : term32.
Proof. exact (proj2 (@lem87476)). Qed.
Lemma lem87493 : term33.
Proof. exact (proj1 (@lem87477)). Qed.
Lemma lem87494 (m : nat) : term34 m.
Proof. exact (@lem87493 m). Qed.
Lemma lem87495 (m : nat) : (term34 m) = ((term35 m) = m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem87509 : term36.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem87525 : term37.
Proof. exact (proj1 (@lem87509)). Qed.
Lemma lem87526 (m : nat) : term38 m.
Proof. exact (@lem87525 m). Qed.
Lemma lem87527 (m : nat) : (term38 m) = ((term39 m) = m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem87540 : term40.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem87541 (m : nat) : term41 m.
Proof. exact (@lem87540 m). Qed.
Lemma lem87542 (m : nat) : (term41 m) = ((term42 m) = term43).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem87547 (m : nat) : (term39 m) = m.
Proof. exact (EQ_MP (@lem87527 m) (@lem87526 m)). Qed.
Lemma lem87548 (n : nat) : (term39 n) = n.
Proof. exact (@lem87547 n). Qed.
Lemma lem87549 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem87550 (m : nat) (n : nat) : (term4 m n) = (Nat.pow m n).
Proof. exact (MK_COMB (@lem87549 m) (@lem87548 n)). Qed.
Lemma lem87551 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87552 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem87551) (@lem87550 m n)). Qed.
Lemma lem87557 (m : nat) : (term42 m) = term43.
Proof. exact (EQ_MP (@lem87542 m) (@lem87541 m)). Qed.
Lemma lem87558 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem87559 (m : nat) (n : nat) : (term5 n m) = (term47 m n).
Proof. exact (MK_COMB (@lem87558 m n) (@lem87557 m)). Qed.
Lemma lem87561 (m : nat) : (term35 m) = m.
Proof. exact (EQ_MP (@lem87495 m) (@lem87494 m)). Qed.
Lemma lem87562 (m : nat) (n : nat) : (term47 m n) = (Nat.pow m n).
Proof. exact (@lem87561 (Nat.pow m n)). Qed.
Lemma lem87563 (m : nat) (n : nat) : (term5 n m) = (Nat.pow m n).
Proof. exact (TRANS (@lem87559 m n) (@lem87562 m n)). Qed.
Lemma lem87564 (m : nat) (n : nat) : ((term4 m n) = (term5 n m)) = ((Nat.pow m n) = (Nat.pow m n)).
Proof. exact (MK_COMB (@lem87552 m n) (@lem87563 m n)). Qed.
Lemma lem87566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87567 (x : nat) : (x = x) = True.
Proof. exact (@lem87566 nat x). Qed.
Lemma lem87568 (m : nat) (n : nat) : ((Nat.pow m n) = (Nat.pow m n)) = True.
Proof. exact (@lem87567 (Nat.pow m n)). Qed.
Lemma lem87569 (n : nat) (m : nat) : ((term4 m n) = (term5 n m)) = True.
Proof. exact (TRANS (@lem87564 m n) (@lem87568 m n)). Qed.
Lemma lem87570 (n : nat) (m : nat) : True = ((term4 m n) = (term5 n m)).
Proof. exact (SYM (@lem87569 n m)). Qed.
Lemma lem87571 (n : nat) (m : nat) : (term4 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem87570 n m) (@lem0)). Qed.
Lemma lem87572 (n : nat) (m : nat) (p : nat) : term48 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem87610 : term36.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem87611 : term49.
Proof. exact (proj2 (@lem87610)). Qed.
Lemma lem87612 : term50.
Proof. exact (proj2 (@lem87611)). Qed.
Lemma lem87613 (m : nat) : term51 m.
Proof. exact (@lem87612 m). Qed.
Lemma lem87614 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem87615 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem87614 m) (@lem87613 m)). Qed.
Lemma lem87616 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem87615 m n). Qed.
Lemma lem87617 (m : nat) (n : nat) : (term53 m n) = ((term54 m n) = (term55 m n)).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem87634 : term56.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem87635 (m : nat) : term57 m.
Proof. exact (@lem87634 m). Qed.
Lemma lem87636 (m : nat) : (term57 m) = (term58 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem87637 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem87636 m) (@lem87635 m)). Qed.
Lemma lem87638 (m : nat) (n : nat) : term59 m n.
Proof. exact (@lem87637 m n). Qed.
Lemma lem87639 (m : nat) (n : nat) : (term59 m n) = ((term60 m n) = (term61 m n)).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem87648 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (EQ_MP (@lem87617 m n) (@lem87616 m n)). Qed.
Lemma lem87649 (n : nat) (p : nat) : (term54 n p) = (term55 n p).
Proof. exact (@lem87648 n p). Qed.
Lemma lem87650 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem87651 (m : nat) (n : nat) (p : nat) : (term14 m n p) = (term62 m n p).
Proof. exact (MK_COMB (@lem87650 m) (@lem87649 n p)). Qed.
Lemma lem87653 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem87639 m n) (@lem87638 m n)). Qed.
Lemma lem87654 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term63 m n p).
Proof. exact (@lem87653 m (Nat.add n p)). Qed.
Lemma lem87659 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term9 m n p) = (term10 n m p).
Proof. exact (h1). Qed.
Lemma lem87663 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem87664 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term63 m n p) = (term64 n m p).
Proof. exact (MK_COMB (@lem87663 m) (@lem87659 n m p h1)). Qed.
Lemma lem87671 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term62 m n p) = (term64 n m p).
Proof. exact (TRANS (@lem87654 m n p) (@lem87664 n m p h1)). Qed.
Lemma lem87672 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term14 m n p) = (term64 n m p).
Proof. exact (TRANS (@lem87651 m n p) (@lem87671 n m p h1)). Qed.
Lemma lem87673 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87674 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term65 m n p) = (term66 n m p).
Proof. exact (MK_COMB (@lem87673) (@lem87672 n m p h1)). Qed.
Lemma lem87679 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem87639 m n) (@lem87638 m n)). Qed.
Lemma lem87680 (m : nat) (p : nat) : (term60 m p) = (term61 m p).
Proof. exact (@lem87679 m p). Qed.
Lemma lem87684 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem87685 (n : nat) (m : nat) (p : nat) : (term15 n m p) = (term67 n m p).
Proof. exact (MK_COMB (@lem87684 m n) (@lem87680 m p)). Qed.
Lemma lem87687 (n : nat) (m : nat) (p : nat) : (term68 m n p) = (term68 n m p).
Proof. exact (proj2 (@lem87572 n m p)). Qed.
Lemma lem87688 (n : nat) (m : nat) (p : nat) : (term67 n m p) = (term64 n m p).
Proof. exact (@lem87687 m (Nat.pow m n) (Nat.pow m p)). Qed.
Lemma lem87698 (n : nat) (m : nat) (p : nat) : (term15 n m p) = (term64 n m p).
Proof. exact (TRANS (@lem87685 n m p) (@lem87688 n m p)). Qed.
Lemma lem87699 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : ((term14 m n p) = (term15 n m p)) = ((term64 n m p) = (term64 n m p)).
Proof. exact (MK_COMB (@lem87674 n m p h1) (@lem87698 n m p)). Qed.
Lemma lem87701 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87702 (x : nat) : (x = x) = True.
Proof. exact (@lem87701 nat x). Qed.
Lemma lem87703 (n : nat) (m : nat) (p : nat) : ((term64 n m p) = (term64 n m p)) = True.
Proof. exact (@lem87702 (term64 n m p)). Qed.
Lemma lem87704 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : ((term14 m n p) = (term15 n m p)) = True.
Proof. exact (TRANS (@lem87699 n m p h1) (@lem87703 n m p)). Qed.
Lemma lem87705 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : True = ((term14 m n p) = (term15 n m p)).
Proof. exact (SYM (@lem87704 n m p h1)). Qed.
Lemma lem87706 (n : nat) (m : nat) (p : nat) (h1 : (term9 m n p) = (term10 n m p)) : (term14 m n p) = (term15 n m p).
Proof. exact (EQ_MP (@lem87705 n m p h1) (@lem0)). Qed.
Lemma lem87707 (n : nat) (m : nat) (p : nat) : term17 n m p.
Proof. exact (fun h0 : (term9 m n p) = (term10 n m p) => @lem87706 n m p h0). Qed.
Lemma lem87712 (n : nat) (m : nat) : term21 n m.
Proof. exact (fun p : nat => @lem87707 n m p). Qed.
Lemma lem87713 (n : nat) (m : nat) : term23 n m.
Proof. exact (conj (@lem87571 n m) (@lem87712 n m)). Qed.
Lemma lem87714 (n : nat) (m : nat) : term28 n m.
Proof. exact (@lem87469 n m (@lem87713 n m)). Qed.
Lemma lem87719 (m : nat) : term69 m.
Proof. exact (fun n : nat => @lem87714 n m). Qed.
Lemma lem87724 : term70.
Proof. exact (fun m : nat => @lem87719 m). Qed.
