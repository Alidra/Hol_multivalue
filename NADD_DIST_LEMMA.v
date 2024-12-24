Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_DIST_LEMMA_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import DIST_REFL_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_0_spec.
Require Import LE_ADD2_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_SUC_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1266570 (m : nat) (h1 : (S m) = (term0 m)) : (S m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem1266571 (m : nat) (h1 : (S m) = (term0 m)) : (term0 m) = (S m).
Proof. exact (SYM (@lem1266570 m h1)). Qed.
Lemma lem1266572 (m : nat) (h1 : (term0 m) = (S m)) : (term0 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem1266573 (m : nat) (h1 : (term0 m) = (S m)) : (S m) = (term0 m).
Proof. exact (SYM (@lem1266572 m h1)). Qed.
Lemma lem1266574 (m : nat) : ((S m) = (term0 m)) = ((term0 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term0 m) => @lem1266571 m h1) (fun h1 : (term0 m) = (S m) => @lem1266573 m h1)). Qed.
Lemma lem1266575 : term1 = term2.
Proof. exact (fun_ext (fun m : nat => @lem1266574 m)). Qed.
Lemma lem1266576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1266577 : term3 = term4.
Proof. exact (MK_COMB (@lem1266576) (@lem1266575)). Qed.
Lemma lem1266578 : term4.
Proof. exact (EQ_MP (@lem1266577) (@lem80621)). Qed.
Lemma lem1266579 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1266580 (m : nat) (h1 : term5) : term6 m.
Proof. exact (@lem1266579 h1 m). Qed.
Lemma lem1266581 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1266582 (m : nat) (h1 : term5) : term7 m.
Proof. exact (EQ_MP (@lem1266581 m) (@lem1266580 m h1)). Qed.
Lemma lem1266583 (m : nat) (n : nat) (h1 : term5) : term8 m n.
Proof. exact (@lem1266582 m h1 n). Qed.
Lemma lem1266584 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem1266585 (m : nat) (n : nat) (h1 : term5) : term9 m n.
Proof. exact (EQ_MP (@lem1266584 m n) (@lem1266583 m n h1)). Qed.
Lemma lem1266586 (m : nat) (n : nat) (p : nat) (h1 : term5) : term10 m n p.
Proof. exact (@lem1266585 m n h1 p). Qed.
Lemma lem1266587 (m : nat) (n : nat) (p : nat) : (term10 m n p) = (term11 m n p).
Proof. exact (eq_refl (term10 m n p)). Qed.
Lemma lem1266588 (m : nat) (n : nat) (p : nat) (h1 : term5) : term11 m n p.
Proof. exact (EQ_MP (@lem1266587 m n p) (@lem1266586 m n p h1)). Qed.
Lemma lem1266589 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term5) : term12 m n p q.
Proof. exact (@lem1266588 m n p h1 q). Qed.
Lemma lem1266590 (m : nat) (n : nat) (p : nat) (q : nat) : (term12 m n p q) = (term13 m n p q).
Proof. exact (eq_refl (term12 m n p q)). Qed.
Lemma lem1266591 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term5) : term13 m n p q.
Proof. exact (EQ_MP (@lem1266590 m n p q) (@lem1266589 m n p q h1)). Qed.
Lemma lem1266592 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term14 m p n q) : term14 m p n q.
Proof. exact (h1). Qed.
Lemma lem1266593 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term5) (h2 : term14 m p n q) : term15 m n p q.
Proof. exact (@lem1266591 m n p q h1 (@lem1266592 m p n q h2)). Qed.
Lemma lem1266594 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term14 m p n q) : term16 m n p q.
Proof. exact (fun h0 : term5 => @lem1266593 m p n q h0 h1). Qed.
Lemma lem1266595 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1266596 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term5) (h2 : term14 m p n q) : term15 m n p q.
Proof. exact (@lem1266594 m p n q h2 (@lem1266595 h1)). Qed.
Lemma lem1266597 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term5) : term13 m n p q.
Proof. exact (fun h0 : term14 m p n q => @lem1266596 m p n q h1 h0). Qed.
Lemma lem1266598 (m : nat) (n : nat) (p : nat) (h1 : term5) : term11 m n p.
Proof. exact (fun q : nat => @lem1266597 m n p q h1). Qed.
Lemma lem1266599 (m : nat) (n : nat) (h1 : term5) : term9 m n.
Proof. exact (fun p : nat => @lem1266598 m n p h1). Qed.
Lemma lem1266600 (m : nat) (h1 : term5) : term7 m.
Proof. exact (fun n : nat => @lem1266599 m n h1). Qed.
Lemma lem1266601 (h1 : term5) : term5.
Proof. exact (fun m : nat => @lem1266600 m h1). Qed.
Lemma lem1266602 : term17.
Proof. exact (fun h0 : term5 => @lem1266601 h0). Qed.
Lemma lem1266603 : term5.
Proof. exact (@lem1266602 (@lem101399)). Qed.
Lemma lem1266604 (m : nat) : term6 m.
Proof. exact (@lem1266603 m). Qed.
Lemma lem1266605 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1266606 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem1266605 m) (@lem1266604 m)). Qed.
Lemma lem1266607 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem1266606 m n). Qed.
Lemma lem1266608 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem1266609 (m : nat) (n : nat) : term9 m n.
Proof. exact (EQ_MP (@lem1266608 m n) (@lem1266607 m n)). Qed.
Lemma lem1266610 (m : nat) (n : nat) (p : nat) : term10 m n p.
Proof. exact (@lem1266609 m n p). Qed.
Lemma lem1266611 (m : nat) (n : nat) (p : nat) : (term10 m n p) = (term11 m n p).
Proof. exact (eq_refl (term10 m n p)). Qed.
Lemma lem1266612 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (EQ_MP (@lem1266611 m n p) (@lem1266610 m n p)). Qed.
Lemma lem1266613 (m : nat) (n : nat) (p : nat) (q : nat) : term12 m n p q.
Proof. exact (@lem1266612 m n p q). Qed.
Lemma lem1266614 (m : nat) (n : nat) (p : nat) (q : nat) : (term12 m n p q) = (term13 m n p q).
Proof. exact (eq_refl (term12 m n p q)). Qed.
Lemma lem1266616 (m : nat) : term18 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1266617 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1266618 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1266617 m) (@lem1266616 m)). Qed.
Lemma lem1266619 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1266618 m n). Qed.
Lemma lem1266620 (n : nat) (m : nat) : (term20 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1266622 (m : nat) : term21 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1266623 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1266624 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1266623 m) (@lem1266622 m)). Qed.
Lemma lem1266625 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1266624 m n). Qed.
Lemma lem1266626 (n : nat) (m : nat) : (term23 m n) = (term24 n m).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1266627 (n : nat) (m : nat) : term24 n m.
Proof. exact (EQ_MP (@lem1266626 n m) (@lem1266625 m n)). Qed.
Lemma lem1266628 (n : nat) (m : nat) (p : nat) : term25 n m p.
Proof. exact (@lem1266627 n m p). Qed.
Lemma lem1266629 (n : nat) (m : nat) (p : nat) : (term25 n m p) = ((term26 m n p) = (term27 n m p)).
Proof. exact (eq_refl (term25 n m p)). Qed.
Lemma lem1266631 (m : nat) : term28 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem1266632 (m : nat) : (term28 m) = ((S m) = (term0 m)).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1266634 (m : nat) : term29 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1266635 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1266636 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1266635 m) (@lem1266634 m)). Qed.
Lemma lem1266637 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem1266636 m n). Qed.
Lemma lem1266638 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1266639 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem1266638 m n) (@lem1266637 m n)). Qed.
Lemma lem1266640 (m : nat) (n : nat) (p : nat) : term33 m n p.
Proof. exact (@lem1266639 m n p). Qed.
Lemma lem1266641 (m : nat) (n : nat) (p : nat) : (term33 m n p) = (term34 m n p).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem1266642 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (EQ_MP (@lem1266641 m n p) (@lem1266640 m n p)). Qed.
Lemma lem1266643 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1266644 (m : nat) (h1 : term35) : term36 m.
Proof. exact (@lem1266643 h1 m). Qed.
Lemma lem1266645 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1266646 (m : nat) (h1 : term35) : term37 m.
Proof. exact (EQ_MP (@lem1266645 m) (@lem1266644 m h1)). Qed.
Lemma lem1266647 (m : nat) (n : nat) (h1 : term35) : term38 m n.
Proof. exact (@lem1266646 m h1 n). Qed.
Lemma lem1266648 (n : nat) (m : nat) : (term38 m n) = (term39 n m).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1266649 (n : nat) (m : nat) (h1 : term35) : term39 n m.
Proof. exact (EQ_MP (@lem1266648 n m) (@lem1266647 m n h1)). Qed.
Lemma lem1266650 (n : nat) (m : nat) (p : nat) (h1 : term35) : term40 n m p.
Proof. exact (@lem1266649 n m h1 p). Qed.
Lemma lem1266651 (n : nat) (m : nat) (p : nat) : (term40 n m p) = (term41 n m p).
Proof. exact (eq_refl (term40 n m p)). Qed.
Lemma lem1266652 (n : nat) (m : nat) (p : nat) (h1 : term35) : term41 n m p.
Proof. exact (EQ_MP (@lem1266651 n m p) (@lem1266650 n m p h1)). Qed.
Lemma lem1266653 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1266654 (p : nat) (m : nat) (n : nat) (h1 : term35) (h2 : Peano.le m n) : term42 n m p.
Proof. exact (@lem1266652 n m p h1 (@lem1266653 m n h2)). Qed.
Lemma lem1266655 (m : nat) (n : nat) (h1 : term35) (h2 : Peano.le m n) : term43 n m.
Proof. exact (fun p : nat => @lem1266654 p m n h1 h2). Qed.
Lemma lem1266656 (n : nat) (m : nat) (h1 : term35) : term44 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1266655 m n h1 h0). Qed.
Lemma lem1266657 (m : nat) (h1 : term35) : term45 m.
Proof. exact (fun n : nat => @lem1266656 n m h1). Qed.
Lemma lem1266658 (h1 : term35) : term46.
Proof. exact (fun m : nat => @lem1266657 m h1). Qed.
Lemma lem1266659 : term47.
Proof. exact (fun h0 : term35 => @lem1266658 h0). Qed.
Lemma lem1266660 : term46.
Proof. exact (@lem1266659 (@lem272809)). Qed.
Lemma lem1266661 (m : nat) : term48 m.
Proof. exact (@lem1266660 m). Qed.
Lemma lem1266662 (m : nat) : (term48 m) = (term45 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem1266663 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1266662 m) (@lem1266661 m)). Qed.
Lemma lem1266664 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1266663 m n). Qed.
Lemma lem1266665 (n : nat) (m : nat) : (term49 m n) = (term44 n m).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1266668 (n : nat) (m : nat) : term44 n m.
Proof. exact (EQ_MP (@lem1266665 n m) (@lem1266664 m n)). Qed.
Lemma lem1266669 (n : nat) (m : nat) (p : nat) : term50 n m p.
Proof. exact (@lem1266668 (term51 m n p) (term52 m p)). Qed.
Lemma lem1266670 (n : nat) (m : nat) (p : nat) : term53 n m p.
Proof. exact (@lem1266669 n m p (@lem1266642 m n p)). Qed.
Lemma lem1266671 (n : nat) (m : nat) : term54 n m.
Proof. exact (fun p : nat => @lem1266670 n m p). Qed.
Lemma lem1266672 (n : nat) : term55 n.
Proof. exact (fun m : nat => @lem1266671 n m). Qed.
Lemma lem1266673 : term56.
Proof. exact (fun n : nat => @lem1266672 n). Qed.
Lemma lem1266674 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1266675 (n : nat) (h1 : term56) : term57 n.
Proof. exact (@lem1266674 h1 n). Qed.
Lemma lem1266676 (n : nat) : (term57 n) = (term55 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem1266677 (n : nat) (h1 : term56) : term55 n.
Proof. exact (EQ_MP (@lem1266676 n) (@lem1266675 n h1)). Qed.
Lemma lem1266678 (n : nat) (m : nat) (h1 : term56) : term58 n m.
Proof. exact (@lem1266677 n h1 m). Qed.
Lemma lem1266679 (n : nat) (m : nat) : (term58 n m) = (term54 n m).
Proof. exact (eq_refl (term58 n m)). Qed.
Lemma lem1266680 (n : nat) (m : nat) (h1 : term56) : term54 n m.
Proof. exact (EQ_MP (@lem1266679 n m) (@lem1266678 n m h1)). Qed.
Lemma lem1266681 (n : nat) (m : nat) (p : nat) (h1 : term56) : term59 n m p.
Proof. exact (@lem1266680 n m h1 p). Qed.
Lemma lem1266682 (n : nat) (m : nat) (p : nat) : (term59 n m p) = (term53 n m p).
Proof. exact (eq_refl (term59 n m p)). Qed.
Lemma lem1266683 (n : nat) (m : nat) (p : nat) (h1 : term56) : term53 n m p.
Proof. exact (EQ_MP (@lem1266682 n m p) (@lem1266681 n m p h1)). Qed.
Lemma lem1266684 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term56) : term60 n m p p'.
Proof. exact (@lem1266683 n m p h1 p'). Qed.
Lemma lem1266685 (n : nat) (m : nat) (p : nat) (p' : nat) : (term60 n m p p') = (term61 n m p p').
Proof. exact (eq_refl (term60 n m p p')). Qed.
Lemma lem1266686 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term56) : term61 n m p p'.
Proof. exact (EQ_MP (@lem1266685 n m p p') (@lem1266684 n m p p' h1)). Qed.
Lemma lem1266687 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term62 m n p p') : term62 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1266688 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term56) (h2 : term62 m n p p') : term63 m p p'.
Proof. exact (@lem1266686 n m p p' h1 (@lem1266687 m n p p' h2)). Qed.
Lemma lem1266689 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term62 m n p p') : term64 m p p'.
Proof. exact (fun h0 : term56 => @lem1266688 m n p p' h0 h1). Qed.
Lemma lem1266690 (m : nat) (p : nat) (p' : nat) (h1 : term65 m p p') : term65 m p p'.
Proof. exact (h1). Qed.
Lemma lem1266691 (m : nat) (p : nat) (p' : nat) (h1 : term65 m p p') : term64 m p p'.
Proof. exact (ex_elim (@lem1266690 m p p' h1) (fun n : nat => fun h0 : term66 m p p' n => @lem1266689 m n p p' h0)). Qed.
Lemma lem1266692 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1266693 (m : nat) (p : nat) (p' : nat) (h1 : term56) (h2 : term65 m p p') : term63 m p p'.
Proof. exact (@lem1266691 m p p' h2 (@lem1266692 h1)). Qed.
Lemma lem1266694 (m : nat) (p : nat) (p' : nat) (h1 : term56) : term67 m p p'.
Proof. exact (fun h0 : term65 m p p' => @lem1266693 m p p' h1 h0). Qed.
Lemma lem1266695 (m : nat) (p : nat) (h1 : term56) : term68 m p.
Proof. exact (fun p' : nat => @lem1266694 m p p' h1). Qed.
Lemma lem1266696 (m : nat) (h1 : term56) : term69 m.
Proof. exact (fun p : nat => @lem1266695 m p h1). Qed.
Lemma lem1266697 (h1 : term56) : term70.
Proof. exact (fun m : nat => @lem1266696 m h1). Qed.
Lemma lem1266698 : term71.
Proof. exact (fun h0 : term56 => @lem1266697 h0). Qed.
Lemma lem1266699 : term70.
Proof. exact (@lem1266698 (@lem1266673)). Qed.
Lemma lem1266700 (m : nat) : term72 m.
Proof. exact (@lem1266699 m). Qed.
Lemma lem1266701 (m : nat) : (term72 m) = (term69 m).
Proof. exact (eq_refl (term72 m)). Qed.
Lemma lem1266702 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem1266701 m) (@lem1266700 m)). Qed.
Lemma lem1266703 (m : nat) (p : nat) : term73 m p.
Proof. exact (@lem1266702 m p). Qed.
Lemma lem1266704 (m : nat) (p : nat) : (term73 m p) = (term68 m p).
Proof. exact (eq_refl (term73 m p)). Qed.
Lemma lem1266705 (m : nat) (p : nat) : term68 m p.
Proof. exact (EQ_MP (@lem1266704 m p) (@lem1266703 m p)). Qed.
Lemma lem1266706 (m : nat) (p : nat) (p' : nat) : term74 m p p'.
Proof. exact (@lem1266705 m p p'). Qed.
Lemma lem1266707 (m : nat) (p : nat) (p' : nat) : (term74 m p p') = (term67 m p p').
Proof. exact (eq_refl (term74 m p p')). Qed.
Lemma lem1266709 (n : nat) : term75 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1266710 (n : nat) : (term75 n) = (term76 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem1266711 (n : nat) : term76 n.
Proof. exact (EQ_MP (@lem1266710 n) (@lem1266709 n)). Qed.
Lemma lem1266712 (n : nat) : (term76 n) = ((term76 n) = True).
Proof. exact (@lem7 (term76 n)). Qed.
Lemma lem1266714 (n : nat) : term77 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1266715 (n : nat) : (term77 n) = ((term78 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem1266717 : term79.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1266718 : term80.
Proof. exact (proj2 (@lem1266717)). Qed.
Lemma lem1266719 : term81.
Proof. exact (proj2 (@lem1266718)). Qed.
Lemma lem1266720 (m : nat) : term82 m.
Proof. exact (@lem1266719 m). Qed.
Lemma lem1266721 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1266722 (m : nat) : term83 m.
Proof. exact (EQ_MP (@lem1266721 m) (@lem1266720 m)). Qed.
Lemma lem1266723 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem1266722 m n). Qed.
Lemma lem1266724 (m : nat) (n : nat) : (term84 m n) = ((term85 m n) = (term86 m n)).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1266733 : term87.
Proof. exact (proj1 (@lem1266717)). Qed.
Lemma lem1266734 (m : nat) : term88 m.
Proof. exact (@lem1266733 m). Qed.
Lemma lem1266735 (m : nat) : (term88 m) = ((term89 m) = m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1266741 (x : nadd) : term90 x.
Proof. exact (@lem1266568 x). Qed.
Lemma lem1266742 (x : nadd) : (term90 x) = (term91 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1266743 (x : nadd) : term91 x.
Proof. exact (EQ_MP (@lem1266742 x) (@lem1266741 x)). Qed.
Lemma lem1266744 (x : nadd) (B : nat) (h1 : term92 x B) : term92 x B.
Proof. exact (h1). Qed.
Lemma lem1266746 (P : nat -> Prop) : term93 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1266747 (x : nadd) (m : nat) (B : nat) : term94 x m B.
Proof. exact (@lem1266746 (term95 x m B)). Qed.
Lemma lem1266748 (x : nadd) (m : nat) (B : nat) : (term96 x m B) = (term97 x m B).
Proof. exact (eq_refl (term96 x m B)). Qed.
Lemma lem1266749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1266750 (x : nadd) (m : nat) (B : nat) : (term98 x m B) = (term99 x m B).
Proof. exact (MK_COMB (@lem1266749) (@lem1266748 x m B)). Qed.
Lemma lem1266751 (x : nadd) (m : nat) (B : nat) (n : nat) : (term100 x m B n) = (term101 x m B n).
Proof. exact (eq_refl (term100 x m B n)). Qed.
Lemma lem1266752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1266753 (x : nadd) (m : nat) (B : nat) (n : nat) : (term102 x m B n) = (term103 x m B n).
Proof. exact (MK_COMB (@lem1266752) (@lem1266751 x m B n)). Qed.
Lemma lem1266754 (x : nadd) (m : nat) (B : nat) (n : nat) : (term104 x m B n) = (term105 x m B n).
Proof. exact (eq_refl (term104 x m B n)). Qed.
Lemma lem1266755 (x : nadd) (m : nat) (B : nat) (n : nat) : (term106 x m B n) = (term107 x m B n).
Proof. exact (MK_COMB (@lem1266753 x m B n) (@lem1266754 x m B n)). Qed.
Lemma lem1266756 (x : nadd) (m : nat) (B : nat) : (term108 x m B) = (term109 x m B).
Proof. exact (fun_ext (fun n : nat => @lem1266755 x m B n)). Qed.
Lemma lem1266757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1266758 (x : nadd) (m : nat) (B : nat) : (term110 x m B) = (term111 x m B).
Proof. exact (MK_COMB (@lem1266757) (@lem1266756 x m B)). Qed.
Lemma lem1266759 (x : nadd) (m : nat) (B : nat) : (term112 x m B) = (term113 x m B).
Proof. exact (MK_COMB (@lem1266750 x m B) (@lem1266758 x m B)). Qed.
Lemma lem1266760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1266761 (x : nadd) (m : nat) (B : nat) : (term114 x m B) = (term115 x m B).
Proof. exact (MK_COMB (@lem1266760) (@lem1266759 x m B)). Qed.
Lemma lem1266762 (x : nadd) (m : nat) (B : nat) (n : nat) : (term100 x m B n) = (term101 x m B n).
Proof. exact (eq_refl (term100 x m B n)). Qed.
Lemma lem1266763 (x : nadd) (m : nat) (B : nat) : (term116 x m B) = (term95 x m B).
Proof. exact (fun_ext (fun n : nat => @lem1266762 x m B n)). Qed.
Lemma lem1266764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1266765 (x : nadd) (m : nat) (B : nat) : (term117 x m B) = (term118 x m B).
Proof. exact (MK_COMB (@lem1266764) (@lem1266763 x m B)). Qed.
Lemma lem1266766 (x : nadd) (m : nat) (B : nat) : (term94 x m B) = (term119 x m B).
Proof. exact (MK_COMB (@lem1266761 x m B) (@lem1266765 x m B)). Qed.
Lemma lem1266767 (x : nadd) (m : nat) (B : nat) : term119 x m B.
Proof. exact (EQ_MP (@lem1266766 x m B) (@lem1266747 x m B)). Qed.
Lemma lem1266768 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term101 x m B n) : term101 x m B n.
Proof. exact (h1). Qed.
Lemma lem1266772 (m : nat) : (term89 m) = m.
Proof. exact (EQ_MP (@lem1266735 m) (@lem1266734 m)). Qed.
Lemma lem1266773 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1266774 (x : nadd) (m : nat) : (term120 x m) = (dest_nadd x m).
Proof. exact (MK_COMB (@lem1266773 x) (@lem1266772 m)). Qed.
Lemma lem1266775 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1266776 (x : nadd) (m : nat) : (term121 x m) = (term122 x m).
Proof. exact (MK_COMB (@lem1266775) (@lem1266774 x m)). Qed.
Lemma lem1266777 (x : nadd) (m : nat) : (dest_nadd x m) = (dest_nadd x m).
Proof. exact (eq_refl (dest_nadd x m)). Qed.
Lemma lem1266778 (x : nadd) (m : nat) : (term123 x m) = (term124 x m).
Proof. exact (MK_COMB (@lem1266776 x m) (@lem1266777 x m)). Qed.
Lemma lem1266779 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1266780 (x : nadd) (m : nat) : (term125 x m) = (term126 x m).
Proof. exact (MK_COMB (@lem1266779) (@lem1266778 x m)). Qed.
Lemma lem1266782 (n : nat) : (term78 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1266715 n) (@lem1266714 n)). Qed.
Lemma lem1266783 (x : nadd) (m : nat) : (term126 x m) = (NUMERAL 0).
Proof. exact (@lem1266782 (dest_nadd x m)). Qed.
Lemma lem1266784 (x : nadd) (m : nat) : (term125 x m) = (NUMERAL 0).
Proof. exact (TRANS (@lem1266780 x m) (@lem1266783 x m)). Qed.
Lemma lem1266785 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266786 (x : nadd) (m : nat) : (term127 x m) = term128.
Proof. exact (MK_COMB (@lem1266785) (@lem1266784 x m)). Qed.
Lemma lem1266787 (B : nat) : (term129 B) = (term129 B).
Proof. exact (eq_refl (term129 B)). Qed.
Lemma lem1266788 (x : nadd) (m : nat) (B : nat) : (term97 x m B) = (term130 B).
Proof. exact (MK_COMB (@lem1266786 x m) (@lem1266787 B)). Qed.
Lemma lem1266790 (n : nat) : (term76 n) = True.
Proof. exact (EQ_MP (@lem1266712 n) (@lem1266711 n)). Qed.
Lemma lem1266791 (B : nat) : (term130 B) = True.
Proof. exact (@lem1266790 (term129 B)). Qed.
Lemma lem1266792 (x : nadd) (m : nat) (B : nat) : (term97 x m B) = True.
Proof. exact (TRANS (@lem1266788 x m B) (@lem1266791 B)). Qed.
Lemma lem1266793 (x : nadd) (m : nat) (B : nat) : True = (term97 x m B).
Proof. exact (SYM (@lem1266792 x m B)). Qed.
Lemma lem1266794 (x : nadd) (m : nat) (B : nat) : term97 x m B.
Proof. exact (EQ_MP (@lem1266793 x m B) (@lem0)). Qed.
Lemma lem1266798 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1266724 m n) (@lem1266723 m n)). Qed.
Lemma lem1266799 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1266800 (x : nadd) (m : nat) (n : nat) : (term131 x m n) = (term132 x m n).
Proof. exact (MK_COMB (@lem1266799 x) (@lem1266798 m n)). Qed.
Lemma lem1266801 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1266802 (x : nadd) (m : nat) (n : nat) : (term133 x m n) = (term134 x m n).
Proof. exact (MK_COMB (@lem1266801) (@lem1266800 x m n)). Qed.
Lemma lem1266803 (x : nadd) (m : nat) : (dest_nadd x m) = (dest_nadd x m).
Proof. exact (eq_refl (dest_nadd x m)). Qed.
Lemma lem1266804 (n : nat) (x : nadd) (m : nat) : (term135 n x m) = (term136 n x m).
Proof. exact (MK_COMB (@lem1266802 x m n) (@lem1266803 x m)). Qed.
Lemma lem1266805 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1266806 (n : nat) (x : nadd) (m : nat) : (term137 n x m) = (term138 n x m).
Proof. exact (MK_COMB (@lem1266805) (@lem1266804 n x m)). Qed.
Lemma lem1266809 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266810 (n : nat) (x : nadd) (m : nat) : (term139 n x m) = (term140 n x m).
Proof. exact (MK_COMB (@lem1266809) (@lem1266806 n x m)). Qed.
Lemma lem1266811 (B : nat) (n : nat) : (term141 B n) = (term141 B n).
Proof. exact (eq_refl (term141 B n)). Qed.
Lemma lem1266812 (x : nadd) (m : nat) (B : nat) (n : nat) : (term105 x m B n) = (term142 x m B n).
Proof. exact (MK_COMB (@lem1266810 n x m) (@lem1266811 B n)). Qed.
Lemma lem1266813 (x : nadd) (m : nat) (B : nat) (n : nat) : (term142 x m B n) = (term105 x m B n).
Proof. exact (SYM (@lem1266812 x m B n)). Qed.
Lemma lem1266815 (m : nat) (p : nat) (p' : nat) : term67 m p p'.
Proof. exact (EQ_MP (@lem1266707 m p p') (@lem1266706 m p p')). Qed.
Lemma lem1266816 (x : nadd) (m : nat) (B : nat) (n : nat) : term143 x m B n.
Proof. exact (@lem1266815 (term132 x m n) (dest_nadd x m) (term141 B n)). Qed.
Lemma lem1266818 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem1266632 m) (@lem1266631 m)). Qed.
Lemma lem1266819 (m : nat) (n : nat) : (term86 m n) = (term144 m n).
Proof. exact (@lem1266818 (Nat.add m n)). Qed.
Lemma lem1266820 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1266821 (x : nadd) (m : nat) (n : nat) : (term132 x m n) = (term145 x m n).
Proof. exact (MK_COMB (@lem1266820 x) (@lem1266819 m n)). Qed.
Lemma lem1266822 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1266823 (x : nadd) (m : nat) (n : nat) : (term134 x m n) = (term146 x m n).
Proof. exact (MK_COMB (@lem1266822) (@lem1266821 x m n)). Qed.
Lemma lem1266824 (x : nadd) (m : nat) (n : nat) : (term147 x m n) = (term147 x m n).
Proof. exact (eq_refl (term147 x m n)). Qed.
Lemma lem1266825 (x : nadd) (m : nat) (n : nat) : (term148 x m n) = (term149 x m n).
Proof. exact (MK_COMB (@lem1266823 x m n) (@lem1266824 x m n)). Qed.
Lemma lem1266826 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1266827 (x : nadd) (m : nat) (n : nat) : (term150 x m n) = (term151 x m n).
Proof. exact (MK_COMB (@lem1266826) (@lem1266825 x m n)). Qed.
Lemma lem1266828 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1266829 (x : nadd) (m : nat) (n : nat) : (term152 x m n) = (term153 x m n).
Proof. exact (MK_COMB (@lem1266828) (@lem1266827 x m n)). Qed.
Lemma lem1266830 (n : nat) (x : nadd) (m : nat) : (term154 n x m) = (term154 n x m).
Proof. exact (eq_refl (term154 n x m)). Qed.
Lemma lem1266831 (n : nat) (x : nadd) (m : nat) : (term155 n x m) = (term156 n x m).
Proof. exact (MK_COMB (@lem1266829 x m n) (@lem1266830 n x m)). Qed.
Lemma lem1266832 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266833 (n : nat) (x : nadd) (m : nat) : (term157 n x m) = (term158 n x m).
Proof. exact (MK_COMB (@lem1266832) (@lem1266831 n x m)). Qed.
Lemma lem1266835 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem1266632 m) (@lem1266631 m)). Qed.
Lemma lem1266836 (n : nat) : (S n) = (term0 n).
Proof. exact (@lem1266835 n). Qed.
Lemma lem1266837 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1266838 (B : nat) (n : nat) : (term141 B n) = (term159 B n).
Proof. exact (MK_COMB (@lem1266837 B) (@lem1266836 n)). Qed.
Lemma lem1266840 (n : nat) (m : nat) (p : nat) : (term26 m n p) = (term27 n m p).
Proof. exact (EQ_MP (@lem1266629 n m p) (@lem1266628 n m p)). Qed.
Lemma lem1266841 (n : nat) (B : nat) : (term159 B n) = (term160 n B).
Proof. exact (@lem1266840 n B term161). Qed.
Lemma lem1266842 (n : nat) (B : nat) : (term141 B n) = (term160 n B).
Proof. exact (TRANS (@lem1266838 B n) (@lem1266841 n B)). Qed.
Lemma lem1266843 (x : nadd) (m : nat) (n : nat) (B : nat) : (term162 x m B n) = (term163 x m n B).
Proof. exact (MK_COMB (@lem1266833 n x m) (@lem1266842 n B)). Qed.
Lemma lem1266844 (x : nadd) (m : nat) (B : nat) (n : nat) : (term163 x m n B) = (term162 x m B n).
Proof. exact (SYM (@lem1266843 x m n B)). Qed.
Lemma lem1266846 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1266620 n m) (@lem1266619 m n)). Qed.
Lemma lem1266847 (B : nat) (n : nat) : (term160 n B) = (term164 B n).
Proof. exact (@lem1266846 (term165 B) (Nat.mul B n)). Qed.
Lemma lem1266848 (n : nat) (x : nadd) (m : nat) : (term158 n x m) = (term158 n x m).
Proof. exact (eq_refl (term158 n x m)). Qed.
Lemma lem1266849 (x : nadd) (m : nat) (B : nat) (n : nat) : (term163 x m n B) = (term166 x m B n).
Proof. exact (MK_COMB (@lem1266848 n x m) (@lem1266847 B n)). Qed.
Lemma lem1266850 (x : nadd) (m : nat) (n : nat) (B : nat) : (term166 x m B n) = (term163 x m n B).
Proof. exact (SYM (@lem1266849 x m B n)). Qed.
Lemma lem1266852 (m : nat) (n : nat) (p : nat) (q : nat) : term13 m n p q.
Proof. exact (EQ_MP (@lem1266614 m n p q) (@lem1266613 m n p q)). Qed.
Lemma lem1266853 (x : nadd) (m : nat) (B : nat) (n : nat) : term167 x m B n.
Proof. exact (@lem1266852 (term151 x m n) (term154 n x m) (term165 B) (Nat.mul B n)). Qed.
Lemma lem1266854 : term168.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1266855 : term169.
Proof. exact (proj2 (@lem1266854)). Qed.
Lemma lem1266856 : term170.
Proof. exact (proj2 (@lem1266855)). Qed.
Lemma lem1266872 : term171.
Proof. exact (proj1 (@lem1266856)). Qed.
Lemma lem1266873 (m : nat) : term172 m.
Proof. exact (@lem1266872 m). Qed.
Lemma lem1266874 (m : nat) : (term172 m) = ((term165 m) = m).
Proof. exact (eq_refl (term172 m)). Qed.
Lemma lem1266888 (m : nat) : term173 m.
Proof. exact (@lem1266578 m). Qed.
Lemma lem1266889 (m : nat) : (term173 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem1266891 (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term174 x B n.
Proof. exact (@lem1266744 x B h1 n). Qed.
Lemma lem1266892 (x : nadd) (n : nat) (B : nat) : (term174 x B n) = (term175 x n B).
Proof. exact (eq_refl (term174 x B n)). Qed.
Lemma lem1266893 (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term175 x n B.
Proof. exact (EQ_MP (@lem1266892 x n B) (@lem1266891 n x B h1)). Qed.
Lemma lem1266894 (x : nadd) (n : nat) (B : nat) : (term175 x n B) = ((term175 x n B) = True).
Proof. exact (@lem7 (term175 x n B)). Qed.
Lemma lem1266896 (x : nadd) (m : nat) (B : nat) (n : nat) : (term101 x m B n) = ((term101 x m B n) = True).
Proof. exact (@lem7 (term101 x m B n)). Qed.
Lemma lem1266901 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem1266889 m) (@lem1266888 m)). Qed.
Lemma lem1266902 (m : nat) (n : nat) : (term144 m n) = (term86 m n).
Proof. exact (@lem1266901 (Nat.add m n)). Qed.
Lemma lem1266903 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1266904 (x : nadd) (m : nat) (n : nat) : (term145 x m n) = (term132 x m n).
Proof. exact (MK_COMB (@lem1266903 x) (@lem1266902 m n)). Qed.
Lemma lem1266905 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1266906 (x : nadd) (m : nat) (n : nat) : (term146 x m n) = (term134 x m n).
Proof. exact (MK_COMB (@lem1266905) (@lem1266904 x m n)). Qed.
Lemma lem1266907 (x : nadd) (m : nat) (n : nat) : (term147 x m n) = (term147 x m n).
Proof. exact (eq_refl (term147 x m n)). Qed.
Lemma lem1266908 (x : nadd) (m : nat) (n : nat) : (term149 x m n) = (term148 x m n).
Proof. exact (MK_COMB (@lem1266906 x m n) (@lem1266907 x m n)). Qed.
Lemma lem1266909 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1266910 (x : nadd) (m : nat) (n : nat) : (term151 x m n) = (term150 x m n).
Proof. exact (MK_COMB (@lem1266909) (@lem1266908 x m n)). Qed.
Lemma lem1266911 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266912 (x : nadd) (m : nat) (n : nat) : (term176 x m n) = (term177 x m n).
Proof. exact (MK_COMB (@lem1266911) (@lem1266910 x m n)). Qed.
Lemma lem1266914 (m : nat) : (term165 m) = m.
Proof. exact (EQ_MP (@lem1266874 m) (@lem1266873 m)). Qed.
Lemma lem1266915 (B : nat) : (term165 B) = B.
Proof. exact (@lem1266914 B). Qed.
Lemma lem1266916 (x : nadd) (m : nat) (n : nat) (B : nat) : (term178 x m n B) = (term179 x m n B).
Proof. exact (MK_COMB (@lem1266912 x m n) (@lem1266915 B)). Qed.
Lemma lem1266918 (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : (term175 x n B) = True.
Proof. exact (EQ_MP (@lem1266894 x n B) (@lem1266893 n x B h1)). Qed.
Lemma lem1266919 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : (term179 x m n B) = True.
Proof. exact (@lem1266918 (Nat.add m n) x B h1). Qed.
Lemma lem1266920 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : (term178 x m n B) = True.
Proof. exact (TRANS (@lem1266916 x m n B) (@lem1266919 m n x B h1)). Qed.
Lemma lem1266921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1266922 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : (term180 x m n B) = (and True).
Proof. exact (MK_COMB (@lem1266921) (@lem1266920 m n x B h1)). Qed.
Lemma lem1266924 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term101 x m B n) : (term101 x m B n) = True.
Proof. exact (EQ_MP (@lem1266896 x m B n) (@lem1266768 x m B n h1)). Qed.
Lemma lem1266925 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : (term181 x m B n) = (True /\ True).
Proof. exact (MK_COMB (@lem1266922 m n x B h1) (@lem1266924 x m B n h2)). Qed.
Lemma lem1266927 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1266928 : (True /\ True) = True.
Proof. exact (@lem1266927 True). Qed.
Lemma lem1266929 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : (term181 x m B n) = True.
Proof. exact (TRANS (@lem1266925 x m B n h1 h2) (@lem1266928)). Qed.
Lemma lem1266930 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : True = (term181 x m B n).
Proof. exact (SYM (@lem1266929 x m B n h1 h2)). Qed.
Lemma lem1266931 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term181 x m B n.
Proof. exact (EQ_MP (@lem1266930 x m B n h1 h2) (@lem0)). Qed.
Lemma lem1266932 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term166 x m B n.
Proof. exact (@lem1266853 x m B n (@lem1266931 x m B n h1 h2)). Qed.
Lemma lem1266933 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term163 x m n B.
Proof. exact (EQ_MP (@lem1266850 x m n B) (@lem1266932 x m B n h1 h2)). Qed.
Lemma lem1266934 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term162 x m B n.
Proof. exact (EQ_MP (@lem1266844 x m B n) (@lem1266933 x m B n h1 h2)). Qed.
Lemma lem1266935 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term182 x m B n.
Proof. exact (ex_intro (term183 x m B n) (term147 x m n) (@lem1266934 x m B n h1 h2)). Qed.
Lemma lem1266936 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term142 x m B n.
Proof. exact (@lem1266816 x m B n (@lem1266935 x m B n h1 h2)). Qed.
Lemma lem1266937 (x : nadd) (m : nat) (B : nat) (n : nat) (h1 : term92 x B) (h2 : term101 x m B n) : term105 x m B n.
Proof. exact (EQ_MP (@lem1266813 x m B n) (@lem1266936 x m B n h1 h2)). Qed.
Lemma lem1266938 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term107 x m B n.
Proof. exact (fun h0 : term101 x m B n => @lem1266937 x m B n h1 h0). Qed.
Lemma lem1266943 (m : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term111 x m B.
Proof. exact (fun n : nat => @lem1266938 m n x B h1). Qed.
Lemma lem1266944 (m : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term113 x m B.
Proof. exact (conj (@lem1266794 x m B) (@lem1266943 m x B h1)). Qed.
Lemma lem1266945 (m : nat) (x : nadd) (B : nat) (h1 : term92 x B) : term118 x m B.
Proof. exact (@lem1266767 x m B (@lem1266944 m x B h1)). Qed.
Lemma lem1266950 (x : nadd) (B : nat) (h1 : term92 x B) : term184 x B.
Proof. exact (fun m : nat => @lem1266945 m x B h1). Qed.
Lemma lem1266951 (x : nadd) (B : nat) (h1 : term92 x B) : term185 x.
Proof. exact (ex_intro (term186 x) B (@lem1266950 x B h1)). Qed.
Lemma lem1266952 (x : nadd) : term185 x.
Proof. exact (ex_elim (@lem1266743 x) (fun B : nat => fun h0 : term187 x B => @lem1266951 x B h0)). Qed.
Lemma lem1266957 : term188.
Proof. exact (fun x : nadd => @lem1266952 x). Qed.
