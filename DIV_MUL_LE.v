Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MUL_LE_term_abbrevs.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem178524 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem178525 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem178526 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem178525 m) (@lem178524 m)). Qed.
Lemma lem178527 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem178526 m n). Qed.
Lemma lem178528 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem178529 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem178528 m n) (@lem178527 m n)). Qed.
Lemma lem178530 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem178532 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem178533 (m : nat) (h1 : term4) : term5 m.
Proof. exact (@lem178532 h1 m). Qed.
Lemma lem178534 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem178535 (m : nat) (h1 : term4) : term6 m.
Proof. exact (EQ_MP (@lem178534 m) (@lem178533 m h1)). Qed.
Lemma lem178536 (m : nat) (n : nat) (h1 : term4) : term7 m n.
Proof. exact (@lem178535 m h1 n). Qed.
Lemma lem178537 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem178538 (m : nat) (n : nat) (h1 : term4) : term8 m n.
Proof. exact (EQ_MP (@lem178537 m n) (@lem178536 m n h1)). Qed.
Lemma lem178539 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem178540 (m : nat) (n : nat) (h1 : term4) (h2 : term9 n) : term10 m n.
Proof. exact (@lem178538 m n h1 (@lem178539 n h2)). Qed.
Lemma lem178541 (n : nat) (h1 : term4) (h2 : term9 n) : term11 n.
Proof. exact (fun m : nat => @lem178540 m n h1 h2). Qed.
Lemma lem178542 (n : nat) (h1 : term4) : term12 n.
Proof. exact (fun h0 : term9 n => @lem178541 n h1 h0). Qed.
Lemma lem178543 (h1 : term4) : term13.
Proof. exact (fun n : nat => @lem178542 n h1). Qed.
Lemma lem178544 : term14.
Proof. exact (fun h0 : term4 => @lem178543 h0). Qed.
Lemma lem178545 : term13.
Proof. exact (@lem178544 (@lem157261)). Qed.
Lemma lem178546 (n : nat) : term15 n.
Proof. exact (@lem178545 n). Qed.
Lemma lem178547 (n : nat) : (term15 n) = (term12 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem178549 (n : nat) : term16 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem178550 (n : nat) : (term16 n) = (term17 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem178551 (n : nat) : term17 n.
Proof. exact (EQ_MP (@lem178550 n) (@lem178549 n)). Qed.
Lemma lem178553 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem178554 (n : nat) : term18 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem178555 (n : nat) : (term18 n) = (term19 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem178556 (n : nat) : term19 n.
Proof. exact (EQ_MP (@lem178555 n) (@lem178554 n)). Qed.
Lemma lem178557 (n : nat) : (term19 n) = ((term19 n) = True).
Proof. exact (@lem7 (term19 n)). Qed.
Lemma lem178589 : term20.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem178590 (n : nat) : term21 n.
Proof. exact (@lem178589 n). Qed.
Lemma lem178591 (n : nat) : (term21 n) = ((term22 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem178594 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178595 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem178596 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term23.
Proof. exact (MK_COMB (@lem178595) (@lem178594 n h1)). Qed.
Lemma lem178598 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178599 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem178600 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term24 m).
Proof. exact (MK_COMB (@lem178599 m) (@lem178598 n h1)). Qed.
Lemma lem178601 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 m n) = (term26 m).
Proof. exact (MK_COMB (@lem178596 n h1) (@lem178600 m n h1)). Qed.
Lemma lem178603 (n : nat) : (term22 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem178591 n) (@lem178590 n)). Qed.
Lemma lem178604 (m : nat) : (term26 m) = (NUMERAL 0).
Proof. exact (@lem178603 (term24 m)). Qed.
Lemma lem178605 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term25 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem178601 m n h1) (@lem178604 m)). Qed.
Lemma lem178606 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem178607 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term27 m n) = term28.
Proof. exact (MK_COMB (@lem178606) (@lem178605 m n h1)). Qed.
Lemma lem178608 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem178609 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term29 n m) = (term19 m).
Proof. exact (MK_COMB (@lem178607 m n h1) (@lem178608 m)). Qed.
Lemma lem178611 (n : nat) : (term19 n) = True.
Proof. exact (EQ_MP (@lem178557 n) (@lem178556 n)). Qed.
Lemma lem178612 (m : nat) : (term19 m) = True.
Proof. exact (@lem178611 m). Qed.
Lemma lem178613 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term29 n m) = True.
Proof. exact (TRANS (@lem178609 m n h1) (@lem178612 m)). Qed.
Lemma lem178614 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term29 n m).
Proof. exact (SYM (@lem178613 m n h1)). Qed.
Lemma lem178615 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term29 n m.
Proof. exact (EQ_MP (@lem178614 m n h1) (@lem0)). Qed.
Lemma lem178671 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem178547 n) (@lem178546 n)). Qed.
Lemma lem178672 (n : nat) (h1 : term9 n) : term11 n.
Proof. exact (@lem178671 n (@lem178553 n h1)). Qed.
Lemma lem178673 (m : nat) (n : nat) (h1 : term9 n) : term30 n m.
Proof. exact (@lem178672 n h1 m). Qed.
Lemma lem178674 (m : nat) (n : nat) : (term30 n m) = (term10 m n).
Proof. exact (eq_refl (term30 n m)). Qed.
Lemma lem178675 (m : nat) (n : nat) (h1 : term9 n) : term10 m n.
Proof. exact (EQ_MP (@lem178674 m n) (@lem178673 m n h1)). Qed.
Lemma lem178676 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem178679 (m : nat) (n : nat) (h1 : term10 m n) : m = (term31 m n).
Proof. exact (proj1 (@lem178676 m n h1)). Qed.
Lemma lem178680 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem178681 (m : nat) (n : nat) (h1 : term10 m n) : (term29 n m) = (term32 m n).
Proof. exact (MK_COMB (@lem178680 m n) (@lem178679 m n h1)). Qed.
Lemma lem178682 (m : nat) (n : nat) (h1 : term10 m n) : (term32 m n) = (term29 n m).
Proof. exact (SYM (@lem178681 m n h1)). Qed.
Lemma lem178689 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem178690 (m : nat) (n : nat) : (term33 m n) = (term25 m n).
Proof. exact (@lem178689 n (Nat.div m n)). Qed.
Lemma lem178694 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem178695 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem178694) (@lem178690 m n)). Qed.
Lemma lem178696 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem178697 (m : nat) (n : nat) : (term31 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem178695 m n) (@lem178696 m n)). Qed.
Lemma lem178698 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem178699 (m : nat) (n : nat) : (term32 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem178698 m n) (@lem178697 m n)). Qed.
Lemma lem178701 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem178530 m n) (@lem178529 m n)). Qed.
Lemma lem178702 (m : nat) (n : nat) : (term37 m n) = True.
Proof. exact (@lem178701 (term25 m n) (Nat.modulo m n)). Qed.
Lemma lem178703 (m : nat) (n : nat) : (term32 m n) = True.
Proof. exact (TRANS (@lem178699 m n) (@lem178702 m n)). Qed.
Lemma lem178704 (m : nat) (n : nat) : True = (term32 m n).
Proof. exact (SYM (@lem178703 m n)). Qed.
Lemma lem178705 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem178704 m n) (@lem0)). Qed.
Lemma lem178706 (m : nat) (n : nat) (h1 : term10 m n) : term29 n m.
Proof. exact (EQ_MP (@lem178682 m n h1) (@lem178705 m n)). Qed.
Lemma lem178707 (n : nat) (m : nat) : term38 n m.
Proof. exact (fun h0 : term10 m n => @lem178706 m n h0). Qed.
Lemma lem178709 (m : nat) (n : nat) (h1 : term9 n) : term29 n m.
Proof. exact (@lem178707 n m (@lem178675 m n h1)). Qed.
Lemma lem178710 (n : nat) (m : nat) : term29 n m.
Proof. exact (or_elim (@lem178551 n) (fun h0 : n = (NUMERAL 0) => @lem178615 m n h0) (fun h0 : term9 n => @lem178709 m n h0)). Qed.
Lemma lem178715 (m : nat) : term39 m.
Proof. exact (fun n : nat => @lem178710 n m). Qed.
Lemma lem178720 : term40.
Proof. exact (fun m : nat => @lem178715 m). Qed.
