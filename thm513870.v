Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513870_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import SUC_INJ_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem513556 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513557 : (NUMERAL 0) = 0.
Proof. exact (@lem513556 0). Qed.
Lemma lem513558 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513559 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem513558) (@lem513557)). Qed.
Lemma lem513560 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem513561 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem513559) (@lem513560 n)). Qed.
Lemma lem513562 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513563 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem513562) (@lem513561 n)). Qed.
Lemma lem513564 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem513565 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem513563 n) (@lem513564 n)). Qed.
Lemma lem513566 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem513565 n)). Qed.
Lemma lem513567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513568 : term6 = term7.
Proof. exact (MK_COMB (@lem513567) (@lem513566)). Qed.
Lemma lem513569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513570 : term8 = term9.
Proof. exact (MK_COMB (@lem513569) (@lem513568)). Qed.
Lemma lem513572 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513573 : (NUMERAL 0) = 0.
Proof. exact (@lem513572 0). Qed.
Lemma lem513574 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem513575 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem513574 m) (@lem513573)). Qed.
Lemma lem513576 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513577 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem513576) (@lem513575 m)). Qed.
Lemma lem513578 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem513579 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem513577 m) (@lem513578 m)). Qed.
Lemma lem513580 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem513579 m)). Qed.
Lemma lem513581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513582 : term15 = term16.
Proof. exact (MK_COMB (@lem513581) (@lem513580)). Qed.
Lemma lem513583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513584 : term17 = term18.
Proof. exact (MK_COMB (@lem513583) (@lem513582)). Qed.
Lemma lem513585 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem513586 : term20 = term21.
Proof. exact (MK_COMB (@lem513584) (@lem513585)). Qed.
Lemma lem513587 : term22 = term23.
Proof. exact (MK_COMB (@lem513570) (@lem513586)). Qed.
Lemma lem513588 : term23.
Proof. exact (EQ_MP (@lem513587) (@lem77629)). Qed.
Lemma lem513589 (m : nat) : term24 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem513590 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem513591 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem513590 m) (@lem513589 m)). Qed.
Lemma lem513592 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem513591 m n). Qed.
Lemma lem513593 (m : nat) (n : nat) : (term26 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem513595 : term21.
Proof. exact (proj2 (@lem513588)). Qed.
Lemma lem513596 : term19.
Proof. exact (proj2 (@lem513595)). Qed.
Lemma lem513597 : term27.
Proof. exact (proj2 (@lem513596)). Qed.
Lemma lem513598 (m : nat) : term28 m.
Proof. exact (@lem513597 m). Qed.
Lemma lem513599 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem513600 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem513599 m) (@lem513598 m)). Qed.
Lemma lem513601 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem513600 m n). Qed.
Lemma lem513602 (m : nat) (n : nat) : (term30 m n) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem513604 : term33.
Proof. exact (proj1 (@lem513596)). Qed.
Lemma lem513605 (m : nat) : term34 m.
Proof. exact (@lem513604 m). Qed.
Lemma lem513606 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem513607 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem513606 m) (@lem513605 m)). Qed.
Lemma lem513608 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem513607 m n). Qed.
Lemma lem513609 (m : nat) (n : nat) : (term36 m n) = ((term37 m n) = (term32 m n)).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem513611 : term16.
Proof. exact (proj1 (@lem513595)). Qed.
Lemma lem513612 (m : nat) : term38 m.
Proof. exact (@lem513611 m). Qed.
Lemma lem513613 (m : nat) : (term38 m) = ((Nat.add m 0) = m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem513615 : term7.
Proof. exact (proj1 (@lem513588)). Qed.
Lemma lem513616 (n : nat) : term39 n.
Proof. exact (@lem513615 n). Qed.
Lemma lem513617 (n : nat) : (term39 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem513619 (n : nat) : term40 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem513620 (n : nat) : (term40 n) = ((BIT1 n) = (term41 n)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem513622 (n : nat) : term42 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem513623 (n : nat) : (term42 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem513625 (n : nat) : term43 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem513626 (n : nat) : (term43 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem513629 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513626 n) (@lem513625 n)). Qed.
Lemma lem513630 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem513629 m). Qed.
Lemma lem513631 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513632 (m : nat) : (term44 m) = (Nat.add m).
Proof. exact (MK_COMB (@lem513631) (@lem513630 m)). Qed.
Lemma lem513634 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513626 n) (@lem513625 n)). Qed.
Lemma lem513635 (m : nat) (n : nat) : (term45 m n) = (Nat.add m n).
Proof. exact (MK_COMB (@lem513632 m) (@lem513634 n)). Qed.
Lemma lem513636 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513637 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem513636) (@lem513635 m n)). Qed.
Lemma lem513639 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513626 n) (@lem513625 n)). Qed.
Lemma lem513640 (m : nat) (n : nat) : (term48 m n) = (Nat.add m n).
Proof. exact (@lem513639 (Nat.add m n)). Qed.
Lemma lem513641 (m : nat) (n : nat) : ((term45 m n) = (term48 m n)) = ((Nat.add m n) = (Nat.add m n)).
Proof. exact (MK_COMB (@lem513637 m n) (@lem513640 m n)). Qed.
Lemma lem513642 (m : nat) : (term49 m) = (term50 m).
Proof. exact (fun_ext (fun n : nat => @lem513641 m n)). Qed.
Lemma lem513643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513644 (m : nat) : (term51 m) = (term52 m).
Proof. exact (MK_COMB (@lem513643) (@lem513642 m)). Qed.
Lemma lem513645 : term53 = term54.
Proof. exact (fun_ext (fun m : nat => @lem513644 m)). Qed.
Lemma lem513646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513647 : term55 = term56.
Proof. exact (MK_COMB (@lem513646) (@lem513645)). Qed.
Lemma lem513648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513649 : term57 = term58.
Proof. exact (MK_COMB (@lem513648) (@lem513647)). Qed.
Lemma lem513651 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem513617 n) (@lem513616 n)). Qed.
Lemma lem513652 : (Nat.add 0 0) = 0.
Proof. exact (@lem513651 0). Qed.
Lemma lem513653 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513654 : term59 = (@eq nat 0).
Proof. exact (MK_COMB (@lem513653) (@lem513652)). Qed.
Lemma lem513655 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem513656 : ((Nat.add 0 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem513654) (@lem513655)). Qed.
Lemma lem513657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513658 : term60 = term61.
Proof. exact (MK_COMB (@lem513657) (@lem513656)). Qed.
Lemma lem513660 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem513617 n) (@lem513616 n)). Qed.
Lemma lem513661 (n : nat) : (term62 n) = (BIT0 n).
Proof. exact (@lem513660 (BIT0 n)). Qed.
Lemma lem513663 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513664 (n : nat) : (term62 n) = (Nat.add n n).
Proof. exact (TRANS (@lem513661 n) (@lem513663 n)). Qed.
Lemma lem513665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513666 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem513665) (@lem513664 n)). Qed.
Lemma lem513668 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513669 (n : nat) : ((term62 n) = (BIT0 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (MK_COMB (@lem513666 n) (@lem513668 n)). Qed.
Lemma lem513670 : term65 = term66.
Proof. exact (fun_ext (fun n : nat => @lem513669 n)). Qed.
Lemma lem513671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513672 : term67 = term68.
Proof. exact (MK_COMB (@lem513671) (@lem513670)). Qed.
Lemma lem513673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513674 : term69 = term70.
Proof. exact (MK_COMB (@lem513673) (@lem513672)). Qed.
Lemma lem513676 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem513617 n) (@lem513616 n)). Qed.
Lemma lem513677 (n : nat) : (term71 n) = (BIT1 n).
Proof. exact (@lem513676 (BIT1 n)). Qed.
Lemma lem513679 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513680 (n : nat) : (term71 n) = (term41 n).
Proof. exact (TRANS (@lem513677 n) (@lem513679 n)). Qed.
Lemma lem513681 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513682 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem513681) (@lem513680 n)). Qed.
Lemma lem513684 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513685 (n : nat) : ((term71 n) = (BIT1 n)) = ((term41 n) = (term41 n)).
Proof. exact (MK_COMB (@lem513682 n) (@lem513684 n)). Qed.
Lemma lem513687 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513688 (n : nat) : ((term41 n) = (term41 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (@lem513687 (Nat.add n n) (Nat.add n n)). Qed.
Lemma lem513689 (n : nat) : ((term71 n) = (BIT1 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (TRANS (@lem513685 n) (@lem513688 n)). Qed.
Lemma lem513690 : term74 = term66.
Proof. exact (fun_ext (fun n : nat => @lem513689 n)). Qed.
Lemma lem513691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513692 : term75 = term68.
Proof. exact (MK_COMB (@lem513691) (@lem513690)). Qed.
Lemma lem513693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513694 : term76 = term70.
Proof. exact (MK_COMB (@lem513693) (@lem513692)). Qed.
Lemma lem513696 (m : nat) : (Nat.add m 0) = m.
Proof. exact (EQ_MP (@lem513613 m) (@lem513612 m)). Qed.
Lemma lem513697 (n : nat) : (term77 n) = (BIT0 n).
Proof. exact (@lem513696 (BIT0 n)). Qed.
Lemma lem513699 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513700 (n : nat) : (term77 n) = (Nat.add n n).
Proof. exact (TRANS (@lem513697 n) (@lem513699 n)). Qed.
Lemma lem513701 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513702 (n : nat) : (term78 n) = (term64 n).
Proof. exact (MK_COMB (@lem513701) (@lem513700 n)). Qed.
Lemma lem513704 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513705 (n : nat) : ((term77 n) = (BIT0 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (MK_COMB (@lem513702 n) (@lem513704 n)). Qed.
Lemma lem513706 : term79 = term66.
Proof. exact (fun_ext (fun n : nat => @lem513705 n)). Qed.
Lemma lem513707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513708 : term80 = term68.
Proof. exact (MK_COMB (@lem513707) (@lem513706)). Qed.
Lemma lem513709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513710 : term81 = term70.
Proof. exact (MK_COMB (@lem513709) (@lem513708)). Qed.
Lemma lem513712 (m : nat) : (Nat.add m 0) = m.
Proof. exact (EQ_MP (@lem513613 m) (@lem513612 m)). Qed.
Lemma lem513713 (n : nat) : (term82 n) = (BIT1 n).
Proof. exact (@lem513712 (BIT1 n)). Qed.
Lemma lem513715 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513716 (n : nat) : (term82 n) = (term41 n).
Proof. exact (TRANS (@lem513713 n) (@lem513715 n)). Qed.
Lemma lem513717 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513718 (n : nat) : (term83 n) = (term73 n).
Proof. exact (MK_COMB (@lem513717) (@lem513716 n)). Qed.
Lemma lem513720 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513721 (n : nat) : ((term82 n) = (BIT1 n)) = ((term41 n) = (term41 n)).
Proof. exact (MK_COMB (@lem513718 n) (@lem513720 n)). Qed.
Lemma lem513723 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513724 (n : nat) : ((term41 n) = (term41 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (@lem513723 (Nat.add n n) (Nat.add n n)). Qed.
Lemma lem513725 (n : nat) : ((term82 n) = (BIT1 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (TRANS (@lem513721 n) (@lem513724 n)). Qed.
Lemma lem513726 : term84 = term66.
Proof. exact (fun_ext (fun n : nat => @lem513725 n)). Qed.
Lemma lem513727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513728 : term85 = term68.
Proof. exact (MK_COMB (@lem513727) (@lem513726)). Qed.
Lemma lem513729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513730 : term86 = term70.
Proof. exact (MK_COMB (@lem513729) (@lem513728)). Qed.
Lemma lem513732 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513733 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem513732 m). Qed.
Lemma lem513734 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513735 (m : nat) : (term87 m) = (term88 m).
Proof. exact (MK_COMB (@lem513734) (@lem513733 m)). Qed.
Lemma lem513737 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513738 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem513735 m) (@lem513737 n)). Qed.
Lemma lem513739 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513740 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem513739) (@lem513738 m n)). Qed.
Lemma lem513742 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513743 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (@lem513742 (Nat.add m n)). Qed.
Lemma lem513744 (m : nat) (n : nat) : ((term89 m n) = (term93 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (MK_COMB (@lem513740 m n) (@lem513743 m n)). Qed.
Lemma lem513745 (m : nat) : (term95 m) = (term96 m).
Proof. exact (fun_ext (fun n : nat => @lem513744 m n)). Qed.
Lemma lem513746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513747 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem513746) (@lem513745 m)). Qed.
Lemma lem513748 : term99 = term100.
Proof. exact (fun_ext (fun m : nat => @lem513747 m)). Qed.
Lemma lem513749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513750 : term101 = term102.
Proof. exact (MK_COMB (@lem513749) (@lem513748)). Qed.
Lemma lem513751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513752 : term103 = term104.
Proof. exact (MK_COMB (@lem513751) (@lem513750)). Qed.
Lemma lem513754 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513755 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem513754 m). Qed.
Lemma lem513756 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513757 (m : nat) : (term87 m) = (term88 m).
Proof. exact (MK_COMB (@lem513756) (@lem513755 m)). Qed.
Lemma lem513759 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513760 (m : nat) (n : nat) : (term105 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem513757 m) (@lem513759 n)). Qed.
Lemma lem513762 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513602 m n) (@lem513601 m n)). Qed.
Lemma lem513763 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (@lem513762 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem513764 (m : nat) (n : nat) : (term105 m n) = (term107 m n).
Proof. exact (TRANS (@lem513760 m n) (@lem513763 m n)). Qed.
Lemma lem513765 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513766 (m : nat) (n : nat) : (term108 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem513765) (@lem513764 m n)). Qed.
Lemma lem513768 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513769 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (@lem513768 (Nat.add m n)). Qed.
Lemma lem513770 (m : nat) (n : nat) : ((term105 m n) = (term110 m n)) = ((term107 m n) = (term111 m n)).
Proof. exact (MK_COMB (@lem513766 m n) (@lem513769 m n)). Qed.
Lemma lem513772 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513773 (m : nat) (n : nat) : ((term107 m n) = (term111 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (@lem513772 (term90 m n) (term94 m n)). Qed.
Lemma lem513774 (m : nat) (n : nat) : ((term105 m n) = (term110 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (TRANS (@lem513770 m n) (@lem513773 m n)). Qed.
Lemma lem513775 (m : nat) : (term112 m) = (term96 m).
Proof. exact (fun_ext (fun n : nat => @lem513774 m n)). Qed.
Lemma lem513776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513777 (m : nat) : (term113 m) = (term98 m).
Proof. exact (MK_COMB (@lem513776) (@lem513775 m)). Qed.
Lemma lem513778 : term114 = term100.
Proof. exact (fun_ext (fun m : nat => @lem513777 m)). Qed.
Lemma lem513779 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513780 : term115 = term102.
Proof. exact (MK_COMB (@lem513779) (@lem513778)). Qed.
Lemma lem513781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513782 : term116 = term104.
Proof. exact (MK_COMB (@lem513781) (@lem513780)). Qed.
Lemma lem513784 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513785 (m : nat) : (BIT1 m) = (term41 m).
Proof. exact (@lem513784 m). Qed.
Lemma lem513786 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513787 (m : nat) : (term117 m) = (term118 m).
Proof. exact (MK_COMB (@lem513786) (@lem513785 m)). Qed.
Lemma lem513789 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513790 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem513787 m) (@lem513789 n)). Qed.
Lemma lem513792 (m : nat) (n : nat) : (term37 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513609 m n) (@lem513608 m n)). Qed.
Lemma lem513793 (m : nat) (n : nat) : (term120 m n) = (term107 m n).
Proof. exact (@lem513792 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem513794 (m : nat) (n : nat) : (term119 m n) = (term107 m n).
Proof. exact (TRANS (@lem513790 m n) (@lem513793 m n)). Qed.
Lemma lem513795 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513796 (m : nat) (n : nat) : (term121 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem513795) (@lem513794 m n)). Qed.
Lemma lem513798 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513799 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (@lem513798 (Nat.add m n)). Qed.
Lemma lem513800 (m : nat) (n : nat) : ((term119 m n) = (term110 m n)) = ((term107 m n) = (term111 m n)).
Proof. exact (MK_COMB (@lem513796 m n) (@lem513799 m n)). Qed.
Lemma lem513802 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513803 (m : nat) (n : nat) : ((term107 m n) = (term111 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (@lem513802 (term90 m n) (term94 m n)). Qed.
Lemma lem513804 (m : nat) (n : nat) : ((term119 m n) = (term110 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (TRANS (@lem513800 m n) (@lem513803 m n)). Qed.
Lemma lem513805 (m : nat) : (term122 m) = (term96 m).
Proof. exact (fun_ext (fun n : nat => @lem513804 m n)). Qed.
Lemma lem513806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513807 (m : nat) : (term123 m) = (term98 m).
Proof. exact (MK_COMB (@lem513806) (@lem513805 m)). Qed.
Lemma lem513808 : term124 = term100.
Proof. exact (fun_ext (fun m : nat => @lem513807 m)). Qed.
Lemma lem513809 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513810 : term125 = term102.
Proof. exact (MK_COMB (@lem513809) (@lem513808)). Qed.
Lemma lem513811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513812 : term126 = term104.
Proof. exact (MK_COMB (@lem513811) (@lem513810)). Qed.
Lemma lem513814 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513815 (m : nat) : (BIT1 m) = (term41 m).
Proof. exact (@lem513814 m). Qed.
Lemma lem513816 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513817 (m : nat) : (term117 m) = (term118 m).
Proof. exact (MK_COMB (@lem513816) (@lem513815 m)). Qed.
Lemma lem513819 (n : nat) : (BIT1 n) = (term41 n).
Proof. exact (EQ_MP (@lem513620 n) (@lem513619 n)). Qed.
Lemma lem513820 (m : nat) (n : nat) : (term127 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem513817 m) (@lem513819 n)). Qed.
Lemma lem513822 (m : nat) (n : nat) : (term37 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513609 m n) (@lem513608 m n)). Qed.
Lemma lem513823 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (@lem513822 (Nat.add m m) (term41 n)). Qed.
Lemma lem513825 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513602 m n) (@lem513601 m n)). Qed.
Lemma lem513826 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (@lem513825 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem513827 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513828 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem513827) (@lem513826 m n)). Qed.
Lemma lem513829 (m : nat) (n : nat) : (term128 m n) = (term130 m n).
Proof. exact (TRANS (@lem513823 m n) (@lem513828 m n)). Qed.
Lemma lem513830 (m : nat) (n : nat) : (term127 m n) = (term130 m n).
Proof. exact (TRANS (@lem513820 m n) (@lem513829 m n)). Qed.
Lemma lem513831 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513832 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem513831) (@lem513830 m n)). Qed.
Lemma lem513834 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513623 n) (@lem513622 n)). Qed.
Lemma lem513835 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (@lem513834 (term32 m n)). Qed.
Lemma lem513837 (m : nat) (n : nat) : (term37 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513609 m n) (@lem513608 m n)). Qed.
Lemma lem513838 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (@lem513837 (Nat.add m n) (term32 m n)). Qed.
Lemma lem513839 (m : nat) (n : nat) : (term133 m n) = (term135 m n).
Proof. exact (TRANS (@lem513835 m n) (@lem513838 m n)). Qed.
Lemma lem513841 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem513602 m n) (@lem513601 m n)). Qed.
Lemma lem513842 (m : nat) (n : nat) : (term136 m n) = (term111 m n).
Proof. exact (@lem513841 (Nat.add m n) (Nat.add m n)). Qed.
Lemma lem513843 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513844 (m : nat) (n : nat) : (term135 m n) = (term137 m n).
Proof. exact (MK_COMB (@lem513843) (@lem513842 m n)). Qed.
Lemma lem513845 (m : nat) (n : nat) : (term133 m n) = (term137 m n).
Proof. exact (TRANS (@lem513839 m n) (@lem513844 m n)). Qed.
Lemma lem513846 (m : nat) (n : nat) : ((term127 m n) = (term133 m n)) = ((term130 m n) = (term137 m n)).
Proof. exact (MK_COMB (@lem513832 m n) (@lem513845 m n)). Qed.
Lemma lem513848 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513849 (m : nat) (n : nat) : ((term130 m n) = (term137 m n)) = ((term107 m n) = (term111 m n)).
Proof. exact (@lem513848 (term107 m n) (term111 m n)). Qed.
Lemma lem513851 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem513593 m n) (@lem513592 m n)). Qed.
Lemma lem513852 (m : nat) (n : nat) : ((term107 m n) = (term111 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (@lem513851 (term90 m n) (term94 m n)). Qed.
Lemma lem513853 (m : nat) (n : nat) : ((term130 m n) = (term137 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (TRANS (@lem513849 m n) (@lem513852 m n)). Qed.
Lemma lem513854 (m : nat) (n : nat) : ((term127 m n) = (term133 m n)) = ((term90 m n) = (term94 m n)).
Proof. exact (TRANS (@lem513846 m n) (@lem513853 m n)). Qed.
Lemma lem513855 (m : nat) : (term138 m) = (term96 m).
Proof. exact (fun_ext (fun n : nat => @lem513854 m n)). Qed.
Lemma lem513856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513857 (m : nat) : (term139 m) = (term98 m).
Proof. exact (MK_COMB (@lem513856) (@lem513855 m)). Qed.
Lemma lem513858 : term140 = term100.
Proof. exact (fun_ext (fun m : nat => @lem513857 m)). Qed.
Lemma lem513859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513860 : term141 = term102.
Proof. exact (MK_COMB (@lem513859) (@lem513858)). Qed.
Lemma lem513861 : term142 = term143.
Proof. exact (MK_COMB (@lem513812) (@lem513860)). Qed.
Lemma lem513862 : term144 = term145.
Proof. exact (MK_COMB (@lem513782) (@lem513861)). Qed.
Lemma lem513863 : term146 = term147.
Proof. exact (MK_COMB (@lem513752) (@lem513862)). Qed.
Lemma lem513864 : term148 = term149.
Proof. exact (MK_COMB (@lem513730) (@lem513863)). Qed.
Lemma lem513865 : term150 = term151.
Proof. exact (MK_COMB (@lem513710) (@lem513864)). Qed.
Lemma lem513866 : term152 = term153.
Proof. exact (MK_COMB (@lem513694) (@lem513865)). Qed.
Lemma lem513867 : term154 = term155.
Proof. exact (MK_COMB (@lem513674) (@lem513866)). Qed.
Lemma lem513868 : term156 = term157.
Proof. exact (MK_COMB (@lem513658) (@lem513867)). Qed.
Lemma lem513869 : term158 = term159.
Proof. exact (MK_COMB (@lem513649) (@lem513868)). Qed.
Lemma lem513870 : term159 = term158.
Proof. exact (SYM (@lem513869)). Qed.
