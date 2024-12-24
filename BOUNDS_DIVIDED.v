Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOUNDS_DIVIDED_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1260601 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1260602 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1260603 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1260602 m) (@lem1260601 m)). Qed.
Lemma lem1260604 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1260603 m n). Qed.
Lemma lem1260605 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1260606 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1260605 m n) (@lem1260604 m n)). Qed.
Lemma lem1260607 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1260609 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1260610 (m : nat) (h1 : term4) : term5 m.
Proof. exact (@lem1260609 h1 m). Qed.
Lemma lem1260611 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1260612 (m : nat) (h1 : term4) : term6 m.
Proof. exact (EQ_MP (@lem1260611 m) (@lem1260610 m h1)). Qed.
Lemma lem1260613 (m : nat) (n : nat) (h1 : term4) : term7 m n.
Proof. exact (@lem1260612 m h1 n). Qed.
Lemma lem1260614 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem1260615 (n : nat) (m : nat) (h1 : term4) : term8 n m.
Proof. exact (EQ_MP (@lem1260614 n m) (@lem1260613 m n h1)). Qed.
Lemma lem1260616 (n : nat) (m : nat) (p : nat) (h1 : term4) : term9 n m p.
Proof. exact (@lem1260615 n m h1 p). Qed.
Lemma lem1260617 (n : nat) (m : nat) (p : nat) : (term9 n m p) = (term10 n m p).
Proof. exact (eq_refl (term9 n m p)). Qed.
Lemma lem1260618 (n : nat) (m : nat) (p : nat) (h1 : term4) : term10 n m p.
Proof. exact (EQ_MP (@lem1260617 n m p) (@lem1260616 n m p h1)). Qed.
Lemma lem1260619 (m : nat) (n : nat) (p : nat) (h1 : term11 m n p) : term11 m n p.
Proof. exact (h1). Qed.
Lemma lem1260620 (m : nat) (n : nat) (p : nat) (h1 : term4) (h2 : term11 m n p) : Peano.le m p.
Proof. exact (@lem1260618 n m p h1 (@lem1260619 m n p h2)). Qed.
Lemma lem1260621 (m : nat) (n : nat) (p : nat) (h1 : term11 m n p) : term12 m p.
Proof. exact (fun h0 : term4 => @lem1260620 m n p h0 h1). Qed.
Lemma lem1260622 (m : nat) (p : nat) (h1 : term13 m p) : term13 m p.
Proof. exact (h1). Qed.
Lemma lem1260623 (m : nat) (p : nat) (h1 : term13 m p) : term12 m p.
Proof. exact (ex_elim (@lem1260622 m p h1) (fun n : nat => fun h0 : term14 m p n => @lem1260621 m n p h0)). Qed.
Lemma lem1260624 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1260625 (m : nat) (p : nat) (h1 : term4) (h2 : term13 m p) : Peano.le m p.
Proof. exact (@lem1260623 m p h2 (@lem1260624 h1)). Qed.
Lemma lem1260626 (m : nat) (p : nat) (h1 : term4) : term15 m p.
Proof. exact (fun h0 : term13 m p => @lem1260625 m p h1 h0). Qed.
Lemma lem1260627 (m : nat) (h1 : term4) : term16 m.
Proof. exact (fun p : nat => @lem1260626 m p h1). Qed.
Lemma lem1260628 (h1 : term4) : term17.
Proof. exact (fun m : nat => @lem1260627 m h1). Qed.
Lemma lem1260629 : term18.
Proof. exact (fun h0 : term4 => @lem1260628 h0). Qed.
Lemma lem1260630 : term17.
Proof. exact (@lem1260629 (@lem93743)). Qed.
Lemma lem1260631 (m : nat) : term19 m.
Proof. exact (@lem1260630 m). Qed.
Lemma lem1260632 (m : nat) : (term19 m) = (term16 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem1260633 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1260632 m) (@lem1260631 m)). Qed.
Lemma lem1260634 (m : nat) (p : nat) : term20 m p.
Proof. exact (@lem1260633 m p). Qed.
Lemma lem1260635 (m : nat) (p : nat) : (term20 m p) = (term15 m p).
Proof. exact (eq_refl (term20 m p)). Qed.
Lemma lem1260640 (m : nat) (n : nat) (p : nat) (h1 : (term21 m n p) = (term22 m n p)) : (term21 m n p) = (term22 m n p).
Proof. exact (h1). Qed.
Lemma lem1260641 (m : nat) (n : nat) (p : nat) (h1 : (term21 m n p) = (term22 m n p)) : (term22 m n p) = (term21 m n p).
Proof. exact (SYM (@lem1260640 m n p h1)). Qed.
Lemma lem1260642 (m : nat) (n : nat) (p : nat) (h1 : (term22 m n p) = (term21 m n p)) : (term22 m n p) = (term21 m n p).
Proof. exact (h1). Qed.
Lemma lem1260643 (m : nat) (n : nat) (p : nat) (h1 : (term22 m n p) = (term21 m n p)) : (term21 m n p) = (term22 m n p).
Proof. exact (SYM (@lem1260642 m n p h1)). Qed.
Lemma lem1260644 (m : nat) (n : nat) (p : nat) : ((term21 m n p) = (term22 m n p)) = ((term22 m n p) = (term21 m n p)).
Proof. exact (prop_ext (fun h1 : (term21 m n p) = (term22 m n p) => @lem1260641 m n p h1) (fun h1 : (term22 m n p) = (term21 m n p) => @lem1260643 m n p h1)). Qed.
Lemma lem1260645 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (fun_ext (fun p : nat => @lem1260644 m n p)). Qed.
Lemma lem1260646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260647 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem1260646) (@lem1260645 m n)). Qed.
Lemma lem1260648 (m : nat) : (term27 m) = (term28 m).
Proof. exact (fun_ext (fun n : nat => @lem1260647 m n)). Qed.
Lemma lem1260649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260650 (m : nat) : (term29 m) = (term30 m).
Proof. exact (MK_COMB (@lem1260649) (@lem1260648 m)). Qed.
Lemma lem1260651 : term31 = term32.
Proof. exact (fun_ext (fun m : nat => @lem1260650 m)). Qed.
Lemma lem1260652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260653 : term33 = term34.
Proof. exact (MK_COMB (@lem1260652) (@lem1260651)). Qed.
Lemma lem1260654 : term34.
Proof. exact (EQ_MP (@lem1260653) (@lem77960)). Qed.
Lemma lem1260655 (m : nat) : term35 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1260656 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1260657 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1260656 m) (@lem1260655 m)). Qed.
Lemma lem1260658 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1260657 m n). Qed.
Lemma lem1260659 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1260660 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem1260659 m n) (@lem1260658 m n)). Qed.
Lemma lem1260661 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (@lem1260660 m n p). Qed.
Lemma lem1260662 (m : nat) (n : nat) (p : nat) : (term39 m n p) = ((term40 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem1260664 (m : nat) : term41 m.
Proof. exact (@lem1260654 m). Qed.
Lemma lem1260665 (m : nat) : (term41 m) = (term30 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1260666 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1260665 m) (@lem1260664 m)). Qed.
Lemma lem1260667 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem1260666 m n). Qed.
Lemma lem1260668 (m : nat) (n : nat) : (term42 m n) = (term26 m n).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem1260669 (m : nat) (n : nat) : term26 m n.
Proof. exact (EQ_MP (@lem1260668 m n) (@lem1260667 m n)). Qed.
Lemma lem1260670 (m : nat) (n : nat) (p : nat) : term43 m n p.
Proof. exact (@lem1260669 m n p). Qed.
Lemma lem1260671 (m : nat) (n : nat) (p : nat) : (term43 m n p) = ((term22 m n p) = (term21 m n p)).
Proof. exact (eq_refl (term43 m n p)). Qed.
Lemma lem1260673 (m : nat) : term44 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1260674 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1260675 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1260674 m) (@lem1260673 m)). Qed.
Lemma lem1260676 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem1260675 m n). Qed.
Lemma lem1260677 (n : nat) (m : nat) : (term46 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1260679 (m : nat) : term47 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1260680 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1260681 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1260680 m) (@lem1260679 m)). Qed.
Lemma lem1260682 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1260681 m n). Qed.
Lemma lem1260683 (n : nat) (m : nat) : (term49 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1260685 (m : nat) : term50 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1260686 (m : nat) : (term50 m) = (term51 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem1260687 (m : nat) : term51 m.
Proof. exact (EQ_MP (@lem1260686 m) (@lem1260685 m)). Qed.
Lemma lem1260688 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem1260687 m n). Qed.
Lemma lem1260689 (n : nat) (m : nat) : (term52 m n) = (term53 n m).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem1260690 (n : nat) (m : nat) : term53 n m.
Proof. exact (EQ_MP (@lem1260689 n m) (@lem1260688 m n)). Qed.
Lemma lem1260691 (n : nat) (m : nat) (p : nat) : term54 n m p.
Proof. exact (@lem1260690 n m p). Qed.
Lemma lem1260692 (n : nat) (m : nat) (p : nat) : (term54 n m p) = ((term55 m n p) = (term56 n m p)).
Proof. exact (eq_refl (term54 n m p)). Qed.
Lemma lem1260694 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1260695 (m : nat) (h1 : term4) : term5 m.
Proof. exact (@lem1260694 h1 m). Qed.
Lemma lem1260696 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1260697 (m : nat) (h1 : term4) : term6 m.
Proof. exact (EQ_MP (@lem1260696 m) (@lem1260695 m h1)). Qed.
Lemma lem1260698 (m : nat) (n : nat) (h1 : term4) : term7 m n.
Proof. exact (@lem1260697 m h1 n). Qed.
Lemma lem1260699 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem1260700 (n : nat) (m : nat) (h1 : term4) : term8 n m.
Proof. exact (EQ_MP (@lem1260699 n m) (@lem1260698 m n h1)). Qed.
Lemma lem1260701 (n : nat) (m : nat) (p : nat) (h1 : term4) : term9 n m p.
Proof. exact (@lem1260700 n m h1 p). Qed.
Lemma lem1260702 (n : nat) (m : nat) (p : nat) : (term9 n m p) = (term10 n m p).
Proof. exact (eq_refl (term9 n m p)). Qed.
Lemma lem1260703 (n : nat) (m : nat) (p : nat) (h1 : term4) : term10 n m p.
Proof. exact (EQ_MP (@lem1260702 n m p) (@lem1260701 n m p h1)). Qed.
Lemma lem1260704 (m : nat) (n : nat) (p : nat) (h1 : term11 m n p) : term11 m n p.
Proof. exact (h1). Qed.
Lemma lem1260705 (m : nat) (n : nat) (p : nat) (h1 : term4) (h2 : term11 m n p) : Peano.le m p.
Proof. exact (@lem1260703 n m p h1 (@lem1260704 m n p h2)). Qed.
Lemma lem1260706 (m : nat) (n : nat) (p : nat) (h1 : term11 m n p) : term12 m p.
Proof. exact (fun h0 : term4 => @lem1260705 m n p h0 h1). Qed.
Lemma lem1260707 (m : nat) (p : nat) (h1 : term13 m p) : term13 m p.
Proof. exact (h1). Qed.
Lemma lem1260708 (m : nat) (p : nat) (h1 : term13 m p) : term12 m p.
Proof. exact (ex_elim (@lem1260707 m p h1) (fun n : nat => fun h0 : term14 m p n => @lem1260706 m n p h0)). Qed.
Lemma lem1260709 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1260710 (m : nat) (p : nat) (h1 : term4) (h2 : term13 m p) : Peano.le m p.
Proof. exact (@lem1260708 m p h2 (@lem1260709 h1)). Qed.
Lemma lem1260711 (m : nat) (p : nat) (h1 : term4) : term15 m p.
Proof. exact (fun h0 : term13 m p => @lem1260710 m p h1 h0). Qed.
Lemma lem1260712 (m : nat) (h1 : term4) : term16 m.
Proof. exact (fun p : nat => @lem1260711 m p h1). Qed.
Lemma lem1260713 (h1 : term4) : term17.
Proof. exact (fun m : nat => @lem1260712 m h1). Qed.
Lemma lem1260714 : term18.
Proof. exact (fun h0 : term4 => @lem1260713 h0). Qed.
Lemma lem1260715 : term17.
Proof. exact (@lem1260714 (@lem93743)). Qed.
Lemma lem1260716 (m : nat) : term19 m.
Proof. exact (@lem1260715 m). Qed.
Lemma lem1260717 (m : nat) : (term19 m) = (term16 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem1260718 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1260717 m) (@lem1260716 m)). Qed.
Lemma lem1260719 (m : nat) (p : nat) : term20 m p.
Proof. exact (@lem1260718 m p). Qed.
Lemma lem1260720 (m : nat) (p : nat) : (term20 m p) = (term15 m p).
Proof. exact (eq_refl (term20 m p)). Qed.
Lemma lem1260722 (n : nat) : term57 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1260723 (n : nat) : (term57 n) = (term58 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem1260724 (n : nat) : term58 n.
Proof. exact (EQ_MP (@lem1260723 n) (@lem1260722 n)). Qed.
Lemma lem1260726 (n : nat) (h1 : term59 n) : term59 n.
Proof. exact (h1). Qed.
Lemma lem1260727 (n : nat) : term60 n.
Proof. exact (@lem104208 n). Qed.
Lemma lem1260728 (n : nat) : (term60 n) = (term61 n).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem1260729 (n : nat) : term61 n.
Proof. exact (EQ_MP (@lem1260728 n) (@lem1260727 n)). Qed.
Lemma lem1260730 (P : nat -> nat) (n : nat) : term62 P n.
Proof. exact (@lem1260729 n (P n)). Qed.
Lemma lem1260731 (P : nat -> nat) (n : nat) : (term62 P n) = (term63 P n).
Proof. exact (eq_refl (term62 P n)). Qed.
Lemma lem1260732 (P : nat -> nat) (n : nat) : term63 P n.
Proof. exact (EQ_MP (@lem1260731 P n) (@lem1260730 P n)). Qed.
Lemma lem1260733 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : term64 n P A B.
Proof. exact (@lem1260732 P n (term65 P A B)). Qed.
Lemma lem1260734 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term64 n P A B) = ((term66 n P A B) = (term67 n P A B)).
Proof. exact (eq_refl (term64 n P A B)). Qed.
Lemma lem1260735 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term66 n P A B) = (term67 n P A B).
Proof. exact (EQ_MP (@lem1260734 n P A B) (@lem1260733 n P A B)). Qed.
Lemma lem1260736 (m : nat) : term44 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1260737 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1260738 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1260737 m) (@lem1260736 m)). Qed.
Lemma lem1260739 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem1260738 m n). Qed.
Lemma lem1260740 (n : nat) (m : nat) : (term46 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1260742 : term68.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1260758 : term69.
Proof. exact (proj1 (@lem1260742)). Qed.
Lemma lem1260759 (m : nat) : term70 m.
Proof. exact (@lem1260758 m). Qed.
Lemma lem1260760 (m : nat) : (term70 m) = ((term71 m) = m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem1260766 (P : nat -> nat) (h1 : term72 P) : term72 P.
Proof. exact (h1). Qed.
Lemma lem1260767 (P : nat -> nat) (B : nat) (h1 : term73 P B) : term73 P B.
Proof. exact (h1). Qed.
Lemma lem1260768 (P : nat -> nat) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem1260769 (P : nat -> nat) (A : nat) (h1 : term75 P A) : term75 P A.
Proof. exact (h1). Qed.
Lemma lem1260770 (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term76 P A B.
Proof. exact (h1). Qed.
Lemma lem1260772 (m : nat) : (term71 m) = m.
Proof. exact (EQ_MP (@lem1260760 m) (@lem1260759 m)). Qed.
Lemma lem1260773 (B : nat) (n : nat) : (term77 B n) = (Nat.mul B n).
Proof. exact (@lem1260772 (Nat.mul B n)). Qed.
Lemma lem1260774 (P : nat -> nat) (n : nat) : (term78 P n) = (term78 P n).
Proof. exact (eq_refl (term78 P n)). Qed.
Lemma lem1260775 (P : nat -> nat) (B : nat) (n : nat) : (term79 P B n) = (term80 P B n).
Proof. exact (MK_COMB (@lem1260774 P n) (@lem1260773 B n)). Qed.
Lemma lem1260776 (P : nat -> nat) (B : nat) (n : nat) : (term80 P B n) = (term79 P B n).
Proof. exact (SYM (@lem1260775 P B n)). Qed.
Lemma lem1260778 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1260740 n m) (@lem1260739 m n)). Qed.
Lemma lem1260779 (n : nat) (B : nat) : (Nat.mul B n) = (Nat.mul n B).
Proof. exact (@lem1260778 n B). Qed.
Lemma lem1260780 (P : nat -> nat) (n : nat) : (term78 P n) = (term78 P n).
Proof. exact (eq_refl (term78 P n)). Qed.
Lemma lem1260781 (P : nat -> nat) (n : nat) (B : nat) : (term80 P B n) = (term81 P n B).
Proof. exact (MK_COMB (@lem1260780 P n) (@lem1260779 n B)). Qed.
Lemma lem1260782 (P : nat -> nat) (B : nat) (n : nat) : (term81 P n B) = (term80 P B n).
Proof. exact (SYM (@lem1260781 P n B)). Qed.
Lemma lem1260783 (m : nat) : term60 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1260784 (m : nat) : (term60 m) = (term61 m).
Proof. exact (eq_refl (term60 m)). Qed.
Lemma lem1260785 (m : nat) : term61 m.
Proof. exact (EQ_MP (@lem1260784 m) (@lem1260783 m)). Qed.
Lemma lem1260786 (m : nat) (n : nat) : term82 m n.
Proof. exact (@lem1260785 m n). Qed.
Lemma lem1260787 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem1260788 (m : nat) (n : nat) : term83 m n.
Proof. exact (EQ_MP (@lem1260787 m n) (@lem1260786 m n)). Qed.
Lemma lem1260789 (m : nat) (n : nat) (p : nat) : term84 m n p.
Proof. exact (@lem1260788 m n p). Qed.
Lemma lem1260790 (m : nat) (n : nat) (p : nat) : (term84 m n p) = ((term85 n m p) = (term86 m n p)).
Proof. exact (eq_refl (term84 m n p)). Qed.
Lemma lem1260792 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : term87 P B n.
Proof. exact (@lem1260767 P B h1 n). Qed.
Lemma lem1260793 (P : nat -> nat) (n : nat) (B : nat) : (term87 P B n) = (term88 P n B).
Proof. exact (eq_refl (term87 P B n)). Qed.
Lemma lem1260794 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : term88 P n B.
Proof. exact (EQ_MP (@lem1260793 P n B) (@lem1260792 n P B h1)). Qed.
Lemma lem1260795 (P : nat -> nat) (n : nat) (B : nat) : (term88 P n B) = ((term88 P n B) = True).
Proof. exact (@lem7 (term88 P n B)). Qed.
Lemma lem1260798 (m : nat) (n : nat) (p : nat) : (term85 n m p) = (term86 m n p).
Proof. exact (EQ_MP (@lem1260790 m n p) (@lem1260789 m n p)). Qed.
Lemma lem1260799 (P : nat -> nat) (n : nat) (B : nat) : (term81 P n B) = (term89 P n B).
Proof. exact (@lem1260798 n (P n) B). Qed.
Lemma lem1260805 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : (term88 P n B) = True.
Proof. exact (EQ_MP (@lem1260795 P n B) (@lem1260794 n P B h1)). Qed.
Lemma lem1260806 (n : nat) : (term90 n) = (term90 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem1260807 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : (term89 P n B) = (term91 n).
Proof. exact (MK_COMB (@lem1260806 n) (@lem1260805 n P B h1)). Qed.
Lemma lem1260809 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1260810 (n : nat) : (term91 n) = True.
Proof. exact (@lem1260809 (n = (NUMERAL 0))). Qed.
Lemma lem1260811 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : (term89 P n B) = True.
Proof. exact (TRANS (@lem1260807 n P B h1) (@lem1260810 n)). Qed.
Lemma lem1260812 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : (term81 P n B) = True.
Proof. exact (TRANS (@lem1260799 P n B) (@lem1260811 n P B h1)). Qed.
Lemma lem1260813 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : True = (term81 P n B).
Proof. exact (SYM (@lem1260812 n P B h1)). Qed.
Lemma lem1260814 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : term81 P n B.
Proof. exact (EQ_MP (@lem1260813 n P B h1) (@lem0)). Qed.
Lemma lem1260815 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : term80 P B n.
Proof. exact (EQ_MP (@lem1260782 P B n) (@lem1260814 n P B h1)). Qed.
Lemma lem1260816 (n : nat) (P : nat -> nat) (B : nat) (h1 : term73 P B) : term79 P B n.
Proof. exact (EQ_MP (@lem1260776 P B n) (@lem1260815 n P B h1)). Qed.
Lemma lem1260821 (P : nat -> nat) (B : nat) (h1 : term73 P B) : term92 P B.
Proof. exact (fun n : nat => @lem1260816 n P B h1). Qed.
Lemma lem1260822 (P : nat -> nat) (B : nat) (h1 : term73 P B) : term75 P B.
Proof. exact (ex_intro (term93 P B) (NUMERAL 0) (@lem1260821 P B h1)). Qed.
Lemma lem1260823 (P : nat -> nat) (B : nat) (h1 : term73 P B) : term74 P.
Proof. exact (ex_intro (term94 P) B (@lem1260822 P B h1)). Qed.
Lemma lem1260824 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1260825 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1260826 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1260825 m) (@lem1260824 m)). Qed.
Lemma lem1260827 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1260826 m n). Qed.
Lemma lem1260828 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1260829 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1260828 m n) (@lem1260827 m n)). Qed.
Lemma lem1260830 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1260844 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260845 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1260846 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term95.
Proof. exact (MK_COMB (@lem1260845) (@lem1260844 n h1)). Qed.
Lemma lem1260848 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260849 (P : nat -> nat) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1260850 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (P n) = (term96 P).
Proof. exact (MK_COMB (@lem1260849 P) (@lem1260848 n h1)). Qed.
Lemma lem1260851 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term97 P n) = (term98 P).
Proof. exact (MK_COMB (@lem1260846 n h1) (@lem1260850 P n h1)). Qed.
Lemma lem1260852 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1260853 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term78 P n) = (term99 P).
Proof. exact (MK_COMB (@lem1260852) (@lem1260851 P n h1)). Qed.
Lemma lem1260855 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260856 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1260857 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term95.
Proof. exact (MK_COMB (@lem1260856) (@lem1260855 n h1)). Qed.
Lemma lem1260858 (P : nat -> nat) (A : nat) (B : nat) : (term65 P A B) = (term65 P A B).
Proof. exact (eq_refl (term65 P A B)). Qed.
Lemma lem1260859 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term100 n P A B) = (term101 P A B).
Proof. exact (MK_COMB (@lem1260857 n h1) (@lem1260858 P A B)). Qed.
Lemma lem1260860 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term66 n P A B) = (term102 P A B).
Proof. exact (MK_COMB (@lem1260853 P n h1) (@lem1260859 P A B n h1)). Qed.
Lemma lem1260861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1260862 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term103 n P A B) = (term104 P A B).
Proof. exact (MK_COMB (@lem1260861) (@lem1260860 P A B n h1)). Qed.
Lemma lem1260868 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260869 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1260870 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term105.
Proof. exact (MK_COMB (@lem1260869) (@lem1260868 n h1)). Qed.
Lemma lem1260871 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1260872 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1260870 n h1) (@lem1260871)). Qed.
Lemma lem1260874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1260875 (x : nat) : (x = x) = True.
Proof. exact (@lem1260874 nat x). Qed.
Lemma lem1260876 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1260875 (NUMERAL 0)). Qed.
Lemma lem1260877 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1260872 n h1) (@lem1260876)). Qed.
Lemma lem1260878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1260879 (n : nat) (h1 : n = (NUMERAL 0)) : (term90 n) = (or True).
Proof. exact (MK_COMB (@lem1260878) (@lem1260877 n h1)). Qed.
Lemma lem1260883 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260884 (P : nat -> nat) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1260885 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (P n) = (term96 P).
Proof. exact (MK_COMB (@lem1260884 P) (@lem1260883 n h1)). Qed.
Lemma lem1260886 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1260887 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term106 P n) = (term107 P).
Proof. exact (MK_COMB (@lem1260886) (@lem1260885 P n h1)). Qed.
Lemma lem1260888 (P : nat -> nat) (A : nat) (B : nat) : (term65 P A B) = (term65 P A B).
Proof. exact (eq_refl (term65 P A B)). Qed.
Lemma lem1260889 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 n P A B) = (term109 P A B).
Proof. exact (MK_COMB (@lem1260887 P n h1) (@lem1260888 P A B)). Qed.
Lemma lem1260891 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1260830 m n) (@lem1260829 m n)). Qed.
Lemma lem1260892 (P : nat -> nat) (A : nat) (B : nat) : (term109 P A B) = True.
Proof. exact (@lem1260891 (term96 P) (Nat.add A B)). Qed.
Lemma lem1260893 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 n P A B) = True.
Proof. exact (TRANS (@lem1260889 P A B n h1) (@lem1260892 P A B)). Qed.
Lemma lem1260894 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 n P A B) = (True \/ True).
Proof. exact (MK_COMB (@lem1260879 n h1) (@lem1260893 P A B n h1)). Qed.
Lemma lem1260896 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1260897 : (True \/ True) = True.
Proof. exact (@lem1260896 True). Qed.
Lemma lem1260898 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 n P A B) = True.
Proof. exact (TRANS (@lem1260894 P A B n h1) (@lem1260897)). Qed.
Lemma lem1260899 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term66 n P A B) = (term67 n P A B)) = ((term102 P A B) = True).
Proof. exact (MK_COMB (@lem1260862 P A B n h1) (@lem1260898 P A B n h1)). Qed.
Lemma lem1260901 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1260902 (P : nat -> nat) (A : nat) (B : nat) : ((term102 P A B) = True) = (term102 P A B).
Proof. exact (@lem1260901 (term102 P A B)). Qed.
Lemma lem1260903 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term66 n P A B) = (term67 n P A B)) = (term102 P A B).
Proof. exact (TRANS (@lem1260899 P A B n h1) (@lem1260902 P A B)). Qed.
Lemma lem1260904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1260905 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term110 n P A B) = (term111 P A B).
Proof. exact (MK_COMB (@lem1260904) (@lem1260903 P A B n h1)). Qed.
Lemma lem1260909 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1260910 (P : nat -> nat) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1260911 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (P n) = (term96 P).
Proof. exact (MK_COMB (@lem1260910 P) (@lem1260909 n h1)). Qed.
Lemma lem1260912 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1260913 (P : nat -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term106 P n) = (term107 P).
Proof. exact (MK_COMB (@lem1260912) (@lem1260911 P n h1)). Qed.
Lemma lem1260914 (P : nat -> nat) (A : nat) (B : nat) : (term65 P A B) = (term65 P A B).
Proof. exact (eq_refl (term65 P A B)). Qed.
Lemma lem1260915 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 n P A B) = (term109 P A B).
Proof. exact (MK_COMB (@lem1260913 P n h1) (@lem1260914 P A B)). Qed.
Lemma lem1260917 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1260830 m n) (@lem1260829 m n)). Qed.
Lemma lem1260918 (P : nat -> nat) (A : nat) (B : nat) : (term109 P A B) = True.
Proof. exact (@lem1260917 (term96 P) (Nat.add A B)). Qed.
Lemma lem1260919 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 n P A B) = True.
Proof. exact (TRANS (@lem1260915 P A B n h1) (@lem1260918 P A B)). Qed.
Lemma lem1260920 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term112 n P A B) = (term113 P A B).
Proof. exact (MK_COMB (@lem1260905 P A B n h1) (@lem1260919 P A B n h1)). Qed.
Lemma lem1260922 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1260923 (P : nat -> nat) (A : nat) (B : nat) : (term113 P A B) = True.
Proof. exact (@lem1260922 (term102 P A B)). Qed.
Lemma lem1260924 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term112 n P A B) = True.
Proof. exact (TRANS (@lem1260920 P A B n h1) (@lem1260923 P A B)). Qed.
Lemma lem1260925 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term112 n P A B).
Proof. exact (SYM (@lem1260924 P A B n h1)). Qed.
Lemma lem1260926 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term112 n P A B.
Proof. exact (EQ_MP (@lem1260925 P A B n h1) (@lem0)). Qed.
Lemma lem1260940 (n : nat) : term114 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1260962 (n : nat) (h1 : term59 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1260940 n (@lem1260726 n h1)). Qed.
Lemma lem1260963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1260964 (n : nat) (h1 : term59 n) : (term90 n) = (or False).
Proof. exact (MK_COMB (@lem1260963) (@lem1260962 n h1)). Qed.
Lemma lem1260967 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term108 n P A B) = (term108 n P A B).
Proof. exact (eq_refl (term108 n P A B)). Qed.
Lemma lem1260968 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : (term67 n P A B) = (term115 n P A B).
Proof. exact (MK_COMB (@lem1260964 n h1) (@lem1260967 n P A B)). Qed.
Lemma lem1260970 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1260971 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term115 n P A B) = (term108 n P A B).
Proof. exact (@lem1260970 (term108 n P A B)). Qed.
Lemma lem1260974 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : (term67 n P A B) = (term108 n P A B).
Proof. exact (TRANS (@lem1260968 P A B n h1) (@lem1260971 n P A B)). Qed.
Lemma lem1260975 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term103 n P A B) = (term103 n P A B).
Proof. exact (eq_refl (term103 n P A B)). Qed.
Lemma lem1260976 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : ((term66 n P A B) = (term67 n P A B)) = ((term66 n P A B) = (term108 n P A B)).
Proof. exact (MK_COMB (@lem1260975 n P A B) (@lem1260974 P A B n h1)). Qed.
Lemma lem1260979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1260980 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : (term110 n P A B) = (term116 n P A B).
Proof. exact (MK_COMB (@lem1260979) (@lem1260976 P A B n h1)). Qed.
Lemma lem1260983 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term108 n P A B) = (term108 n P A B).
Proof. exact (eq_refl (term108 n P A B)). Qed.
Lemma lem1260984 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : (term112 n P A B) = (term117 n P A B).
Proof. exact (MK_COMB (@lem1260980 P A B n h1) (@lem1260983 n P A B)). Qed.
Lemma lem1260989 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : (term117 n P A B) = (term112 n P A B).
Proof. exact (SYM (@lem1260984 P A B n h1)). Qed.
Lemma lem1260990 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : (term66 n P A B) = (term108 n P A B)) : (term66 n P A B) = (term108 n P A B).
Proof. exact (h1). Qed.
Lemma lem1260991 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : (term66 n P A B) = (term108 n P A B)) : (term108 n P A B) = (term66 n P A B).
Proof. exact (SYM (@lem1260990 n P A B h1)). Qed.
Lemma lem1260992 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem1260993 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : (term66 n P A B) = (term108 n P A B)) : (term119 n P A B) = (term120 n P A B).
Proof. exact (MK_COMB (@lem1260992) (@lem1260991 n P A B h1)). Qed.
Lemma lem1260994 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term120 n P A B) = (term66 n P A B).
Proof. exact (eq_refl (term120 n P A B)). Qed.
Lemma lem1260995 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term121 n P A B) = (term121 n P A B).
Proof. exact (eq_refl (term121 n P A B)). Qed.
Lemma lem1260996 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : ((term119 n P A B) = (term120 n P A B)) = ((term119 n P A B) = (term66 n P A B)).
Proof. exact (MK_COMB (@lem1260995 n P A B) (@lem1260994 n P A B)). Qed.
Lemma lem1260997 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term119 n P A B) = (term108 n P A B).
Proof. exact (eq_refl (term119 n P A B)). Qed.
Lemma lem1260998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1260999 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term121 n P A B) = (term122 n P A B).
Proof. exact (MK_COMB (@lem1260998) (@lem1260997 n P A B)). Qed.
Lemma lem1261000 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term66 n P A B) = (term66 n P A B).
Proof. exact (eq_refl (term66 n P A B)). Qed.
Lemma lem1261001 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : ((term119 n P A B) = (term66 n P A B)) = ((term108 n P A B) = (term66 n P A B)).
Proof. exact (MK_COMB (@lem1260999 n P A B) (@lem1261000 n P A B)). Qed.
Lemma lem1261002 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : ((term119 n P A B) = (term120 n P A B)) = ((term108 n P A B) = (term66 n P A B)).
Proof. exact (TRANS (@lem1260996 n P A B) (@lem1261001 n P A B)). Qed.
Lemma lem1261003 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : (term66 n P A B) = (term108 n P A B)) : (term108 n P A B) = (term66 n P A B).
Proof. exact (EQ_MP (@lem1261002 n P A B) (@lem1260993 n P A B h1)). Qed.
Lemma lem1261004 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : (term66 n P A B) = (term108 n P A B)) : (term66 n P A B) = (term108 n P A B).
Proof. exact (SYM (@lem1261003 n P A B h1)). Qed.
Lemma lem1261006 (m : nat) (p : nat) : term15 m p.
Proof. exact (EQ_MP (@lem1260720 m p) (@lem1260719 m p)). Qed.
Lemma lem1261007 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : term123 n P A B.
Proof. exact (@lem1261006 (term97 P n) (term100 n P A B)). Qed.
Lemma lem1261008 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term124 P A B n.
Proof. exact (@lem1260770 P A B h1 n). Qed.
Lemma lem1261009 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term124 P A B n) = (term125 P A n B).
Proof. exact (eq_refl (term124 P A B n)). Qed.
Lemma lem1261010 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term125 P A n B.
Proof. exact (EQ_MP (@lem1261009 P A n B) (@lem1261008 n P A B h1)). Qed.
Lemma lem1261011 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term125 P A n B) = ((term125 P A n B) = True).
Proof. exact (@lem7 (term125 P A n B)). Qed.
Lemma lem1261029 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term125 P A n B) = True.
Proof. exact (EQ_MP (@lem1261011 P A n B) (@lem1261010 n P A B h1)). Qed.
Lemma lem1261030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1261031 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term126 P A n B) = (and True).
Proof. exact (MK_COMB (@lem1261030) (@lem1261029 n P A B h1)). Qed.
Lemma lem1261032 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term127 n P A B) = (term127 n P A B).
Proof. exact (eq_refl (term127 n P A B)). Qed.
Lemma lem1261033 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term128 n P A B) = (term129 n P A B).
Proof. exact (MK_COMB (@lem1261031 n P A B h1) (@lem1261032 n P A B)). Qed.
Lemma lem1261035 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1261036 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term129 n P A B) = (term127 n P A B).
Proof. exact (@lem1261035 (term127 n P A B)). Qed.
Lemma lem1261037 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term128 n P A B) = (term127 n P A B).
Proof. exact (TRANS (@lem1261033 n P A B h1) (@lem1261036 n P A B)). Qed.
Lemma lem1261038 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term127 n P A B) = (term128 n P A B).
Proof. exact (SYM (@lem1261037 n P A B h1)). Qed.
Lemma lem1261040 (n : nat) (m : nat) (p : nat) : (term55 m n p) = (term56 n m p).
Proof. exact (EQ_MP (@lem1260692 n m p) (@lem1260691 n m p)). Qed.
Lemma lem1261041 (P : nat -> nat) (n : nat) (A : nat) (B : nat) : (term100 n P A B) = (term130 P n A B).
Proof. exact (@lem1261040 (term96 P) n (Nat.add A B)). Qed.
Lemma lem1261043 (n : nat) (m : nat) (p : nat) : (term55 m n p) = (term56 n m p).
Proof. exact (EQ_MP (@lem1260692 n m p) (@lem1260691 n m p)). Qed.
Lemma lem1261044 (A : nat) (n : nat) (B : nat) : (term55 n A B) = (term56 A n B).
Proof. exact (@lem1261043 A n B). Qed.
Lemma lem1261045 (n : nat) (P : nat -> nat) : (term131 n P) = (term131 n P).
Proof. exact (eq_refl (term131 n P)). Qed.
Lemma lem1261046 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term130 P n A B) = (term132 P A n B).
Proof. exact (MK_COMB (@lem1261045 n P) (@lem1261044 A n B)). Qed.
Lemma lem1261047 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term100 n P A B) = (term132 P A n B).
Proof. exact (TRANS (@lem1261041 P n A B) (@lem1261046 P A n B)). Qed.
Lemma lem1261048 (A : nat) (n : nat) (B : nat) : (term133 A n B) = (term133 A n B).
Proof. exact (eq_refl (term133 A n B)). Qed.
Lemma lem1261049 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term127 n P A B) = (term134 P A n B).
Proof. exact (MK_COMB (@lem1261048 A n B) (@lem1261047 P A n B)). Qed.
Lemma lem1261050 (n : nat) (P : nat -> nat) (A : nat) (B : nat) : (term134 P A n B) = (term127 n P A B).
Proof. exact (SYM (@lem1261049 P A n B)). Qed.
Lemma lem1261052 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1260683 n m) (@lem1260682 m n)). Qed.
Lemma lem1261053 (A : nat) (B : nat) (n : nat) (P : nat -> nat) : (term132 P A n B) = (term135 A B n P).
Proof. exact (@lem1261052 (term56 A n B) (term136 n P)). Qed.
Lemma lem1261054 (A : nat) (n : nat) (B : nat) : (term133 A n B) = (term133 A n B).
Proof. exact (eq_refl (term133 A n B)). Qed.
Lemma lem1261055 (A : nat) (B : nat) (n : nat) (P : nat -> nat) : (term134 P A n B) = (term137 A B n P).
Proof. exact (MK_COMB (@lem1261054 A n B) (@lem1261053 A B n P)). Qed.
Lemma lem1261056 (P : nat -> nat) (A : nat) (n : nat) (B : nat) : (term137 A B n P) = (term134 P A n B).
Proof. exact (SYM (@lem1261055 A B n P)). Qed.
Lemma lem1261058 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1260677 n m) (@lem1260676 m n)). Qed.
Lemma lem1261059 (A : nat) (n : nat) : (Nat.mul n A) = (Nat.mul A n).
Proof. exact (@lem1261058 A n). Qed.
Lemma lem1261060 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1261061 (A : nat) (n : nat) : (term138 n A) = (term138 A n).
Proof. exact (MK_COMB (@lem1261060) (@lem1261059 A n)). Qed.
Lemma lem1261063 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1260677 n m) (@lem1260676 m n)). Qed.
Lemma lem1261064 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1261063 B n). Qed.
Lemma lem1261065 (A : nat) (B : nat) (n : nat) : (term56 A n B) = (term139 A B n).
Proof. exact (MK_COMB (@lem1261061 A n) (@lem1261064 B n)). Qed.
Lemma lem1261066 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1261067 (A : nat) (B : nat) (n : nat) : (term140 A n B) = (term141 A B n).
Proof. exact (MK_COMB (@lem1261066) (@lem1261065 A B n)). Qed.
Lemma lem1261069 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1260677 n m) (@lem1260676 m n)). Qed.
Lemma lem1261070 (P : nat -> nat) (n : nat) : (term136 n P) = (term142 P n).
Proof. exact (@lem1261069 (term96 P) n). Qed.
Lemma lem1261071 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term135 A B n P) = (term143 A B P n).
Proof. exact (MK_COMB (@lem1261067 A B n) (@lem1261070 P n)). Qed.
Lemma lem1261072 (A : nat) (n : nat) (B : nat) : (term133 A n B) = (term133 A n B).
Proof. exact (eq_refl (term133 A n B)). Qed.
Lemma lem1261073 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term137 A B n P) = (term144 A B P n).
Proof. exact (MK_COMB (@lem1261072 A n B) (@lem1261071 A B P n)). Qed.
Lemma lem1261074 (A : nat) (B : nat) (n : nat) (P : nat -> nat) : (term144 A B P n) = (term137 A B n P).
Proof. exact (SYM (@lem1261073 A B P n)). Qed.
Lemma lem1261078 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term21 m n p).
Proof. exact (EQ_MP (@lem1260671 m n p) (@lem1260670 m n p)). Qed.
Lemma lem1261079 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term143 A B P n) = (term145 A B P n).
Proof. exact (@lem1261078 (Nat.mul A n) (Nat.mul B n) (term142 P n)). Qed.
Lemma lem1261080 (A : nat) (n : nat) (B : nat) : (term133 A n B) = (term133 A n B).
Proof. exact (eq_refl (term133 A n B)). Qed.
Lemma lem1261081 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term144 A B P n) = (term146 A B P n).
Proof. exact (MK_COMB (@lem1261080 A n B) (@lem1261079 A B P n)). Qed.
Lemma lem1261083 (m : nat) (n : nat) (p : nat) : (term40 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1260662 m n p) (@lem1260661 m n p)). Qed.
Lemma lem1261084 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term146 A B P n) = (term147 B P n).
Proof. exact (@lem1261083 (Nat.mul A n) B (term148 B P n)). Qed.
Lemma lem1261085 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term144 A B P n) = (term147 B P n).
Proof. exact (TRANS (@lem1261081 A B P n) (@lem1261084 A B P n)). Qed.
Lemma lem1261086 (A : nat) (B : nat) (P : nat -> nat) (n : nat) : (term147 B P n) = (term144 A B P n).
Proof. exact (SYM (@lem1261085 A B P n)). Qed.
Lemma lem1261088 (m : nat) (p : nat) : term15 m p.
Proof. exact (EQ_MP (@lem1260635 m p) (@lem1260634 m p)). Qed.
Lemma lem1261089 (B : nat) (P : nat -> nat) (n : nat) : term149 B P n.
Proof. exact (@lem1261088 B (term148 B P n)). Qed.
Lemma lem1261093 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1260607 m n) (@lem1260606 m n)). Qed.
Lemma lem1261094 (B : nat) (P : nat -> nat) (n : nat) : (term150 B P n) = True.
Proof. exact (@lem1261093 (Nat.mul B n) (term142 P n)). Qed.
Lemma lem1261095 (B : nat) (n : nat) : (term151 B n) = (term151 B n).
Proof. exact (eq_refl (term151 B n)). Qed.
Lemma lem1261096 (P : nat -> nat) (B : nat) (n : nat) : (term152 B P n) = (term153 B n).
Proof. exact (MK_COMB (@lem1261095 B n) (@lem1261094 B P n)). Qed.
Lemma lem1261098 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1261099 (B : nat) (n : nat) : (term153 B n) = (term154 B n).
Proof. exact (@lem1261098 (term154 B n)). Qed.
Lemma lem1261100 (P : nat -> nat) (B : nat) (n : nat) : (term152 B P n) = (term154 B n).
Proof. exact (TRANS (@lem1261096 P B n) (@lem1261099 B n)). Qed.
Lemma lem1261101 (B : nat) (P : nat -> nat) (n : nat) : (term154 B n) = (term152 B P n).
Proof. exact (SYM (@lem1261100 P B n)). Qed.
Lemma lem1261103 (P : nat -> Prop) : term155 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1261104 (B : nat) : term156 B.
Proof. exact (@lem1261103 (term157 B)). Qed.
Lemma lem1261105 (B : nat) : (term158 B) = (term159 B).
Proof. exact (eq_refl (term158 B)). Qed.
Lemma lem1261106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1261107 (B : nat) : (term160 B) = (term161 B).
Proof. exact (MK_COMB (@lem1261106) (@lem1261105 B)). Qed.
Lemma lem1261108 (B : nat) (n : nat) : (term162 B n) = (term163 B n).
Proof. exact (eq_refl (term162 B n)). Qed.
Lemma lem1261109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261110 (B : nat) (n : nat) : (term164 B n) = (term165 B n).
Proof. exact (MK_COMB (@lem1261109) (@lem1261108 B n)). Qed.
Lemma lem1261111 (B : nat) (n : nat) : (term166 B n) = (term167 B n).
Proof. exact (eq_refl (term166 B n)). Qed.
Lemma lem1261112 (B : nat) (n : nat) : (term168 B n) = (term169 B n).
Proof. exact (MK_COMB (@lem1261110 B n) (@lem1261111 B n)). Qed.
Lemma lem1261113 (B : nat) : (term170 B) = (term171 B).
Proof. exact (fun_ext (fun n : nat => @lem1261112 B n)). Qed.
Lemma lem1261114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261115 (B : nat) : (term172 B) = (term173 B).
Proof. exact (MK_COMB (@lem1261114) (@lem1261113 B)). Qed.
Lemma lem1261116 (B : nat) : (term174 B) = (term175 B).
Proof. exact (MK_COMB (@lem1261107 B) (@lem1261115 B)). Qed.
Lemma lem1261117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261118 (B : nat) : (term176 B) = (term177 B).
Proof. exact (MK_COMB (@lem1261117) (@lem1261116 B)). Qed.
Lemma lem1261119 (B : nat) (n : nat) : (term162 B n) = (term163 B n).
Proof. exact (eq_refl (term162 B n)). Qed.
Lemma lem1261120 (B : nat) : (term178 B) = (term157 B).
Proof. exact (fun_ext (fun n : nat => @lem1261119 B n)). Qed.
Lemma lem1261121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261122 (B : nat) : (term179 B) = (term180 B).
Proof. exact (MK_COMB (@lem1261121) (@lem1261120 B)). Qed.
Lemma lem1261123 (B : nat) : (term156 B) = (term181 B).
Proof. exact (MK_COMB (@lem1261118 B) (@lem1261122 B)). Qed.
Lemma lem1261124 (B : nat) : term181 B.
Proof. exact (EQ_MP (@lem1261123 B) (@lem1261104 B)). Qed.
Lemma lem1261134 : term182.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1261160 : term183.
Proof. exact (proj1 (@lem1261134)). Qed.
Lemma lem1261161 (m : nat) : term184 m.
Proof. exact (@lem1261160 m). Qed.
Lemma lem1261162 (m : nat) : (term184 m) = ((term185 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term184 m)). Qed.
Lemma lem1261176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1261177 (x : nat) : (x = x) = True.
Proof. exact (@lem1261176 nat x). Qed.
Lemma lem1261178 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1261177 (NUMERAL 0)). Qed.
Lemma lem1261179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1261180 : term186 = (~ True).
Proof. exact (MK_COMB (@lem1261179) (@lem1261178)). Qed.
Lemma lem1261182 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1261183 : term186 = False.
Proof. exact (TRANS (@lem1261180) (@lem1261182)). Qed.
Lemma lem1261184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261185 : term187 = (imp False).
Proof. exact (MK_COMB (@lem1261184) (@lem1261183)). Qed.
Lemma lem1261187 (m : nat) : (term185 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1261162 m) (@lem1261161 m)). Qed.
Lemma lem1261188 (B : nat) : (term185 B) = (NUMERAL 0).
Proof. exact (@lem1261187 B). Qed.
Lemma lem1261189 (B : nat) : (Peano.le B) = (Peano.le B).
Proof. exact (eq_refl (Peano.le B)). Qed.
Lemma lem1261190 (B : nat) : (term188 B) = (term189 B).
Proof. exact (MK_COMB (@lem1261189 B) (@lem1261188 B)). Qed.
Lemma lem1261191 (B : nat) : (term159 B) = (term190 B).
Proof. exact (MK_COMB (@lem1261185) (@lem1261190 B)). Qed.
Lemma lem1261193 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1261194 (B : nat) : (term190 B) = True.
Proof. exact (@lem1261193 (term189 B)). Qed.
Lemma lem1261195 (B : nat) : (term159 B) = True.
Proof. exact (TRANS (@lem1261191 B) (@lem1261194 B)). Qed.
Lemma lem1261196 (B : nat) : True = (term159 B).
Proof. exact (SYM (@lem1261195 B)). Qed.
Lemma lem1261197 (B : nat) : term159 B.
Proof. exact (EQ_MP (@lem1261196 B) (@lem0)). Qed.
Lemma lem1261198 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1261199 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1261200 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1261199 m) (@lem1261198 m)). Qed.
Lemma lem1261201 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1261200 m n). Qed.
Lemma lem1261202 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1261203 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1261202 m n) (@lem1261201 m n)). Qed.
Lemma lem1261204 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1261206 : term182.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1261207 : term191.
Proof. exact (proj2 (@lem1261206)). Qed.
Lemma lem1261208 : term192.
Proof. exact (proj2 (@lem1261207)). Qed.
Lemma lem1261209 : term193.
Proof. exact (proj2 (@lem1261208)). Qed.
Lemma lem1261210 : term194.
Proof. exact (proj2 (@lem1261209)). Qed.
Lemma lem1261211 (m : nat) : term195 m.
Proof. exact (@lem1261210 m). Qed.
Lemma lem1261212 (m : nat) : (term195 m) = (term196 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem1261213 (m : nat) : term196 m.
Proof. exact (EQ_MP (@lem1261212 m) (@lem1261211 m)). Qed.
Lemma lem1261214 (m : nat) (n : nat) : term197 m n.
Proof. exact (@lem1261213 m n). Qed.
Lemma lem1261215 (m : nat) (n : nat) : (term197 m n) = ((term198 m n) = (term199 m n)).
Proof. exact (eq_refl (term197 m n)). Qed.
Lemma lem1261252 (m : nat) (n : nat) : (term198 m n) = (term199 m n).
Proof. exact (EQ_MP (@lem1261215 m n) (@lem1261214 m n)). Qed.
Lemma lem1261253 (B : nat) (n : nat) : (term198 B n) = (term199 B n).
Proof. exact (@lem1261252 B n). Qed.
Lemma lem1261254 (B : nat) : (Peano.le B) = (Peano.le B).
Proof. exact (eq_refl (Peano.le B)). Qed.
Lemma lem1261255 (B : nat) (n : nat) : (term200 B n) = (term201 B n).
Proof. exact (MK_COMB (@lem1261254 B) (@lem1261253 B n)). Qed.
Lemma lem1261257 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1261204 m n) (@lem1261203 m n)). Qed.
Lemma lem1261258 (B : nat) (n : nat) : (term201 B n) = True.
Proof. exact (@lem1261257 B (Nat.mul B n)). Qed.
Lemma lem1261259 (B : nat) (n : nat) : (term200 B n) = True.
Proof. exact (TRANS (@lem1261255 B n) (@lem1261258 B n)). Qed.
Lemma lem1261260 (n : nat) : (term202 n) = (term202 n).
Proof. exact (eq_refl (term202 n)). Qed.
Lemma lem1261261 (B : nat) (n : nat) : (term167 B n) = (term203 n).
Proof. exact (MK_COMB (@lem1261260 n) (@lem1261259 B n)). Qed.
Lemma lem1261263 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1261264 (n : nat) : (term203 n) = True.
Proof. exact (@lem1261263 (term204 n)). Qed.
Lemma lem1261265 (B : nat) (n : nat) : (term167 B n) = True.
Proof. exact (TRANS (@lem1261261 B n) (@lem1261264 n)). Qed.
Lemma lem1261266 (B : nat) (n : nat) : True = (term167 B n).
Proof. exact (SYM (@lem1261265 B n)). Qed.
Lemma lem1261267 (B : nat) (n : nat) : term167 B n.
Proof. exact (EQ_MP (@lem1261266 B n) (@lem0)). Qed.
Lemma lem1261268 (B : nat) (n : nat) : term169 B n.
Proof. exact (fun h0 : term163 B n => @lem1261267 B n). Qed.
Lemma lem1261273 (B : nat) : term173 B.
Proof. exact (fun n : nat => @lem1261268 B n). Qed.
Lemma lem1261274 (B : nat) : term175 B.
Proof. exact (conj (@lem1261197 B) (@lem1261273 B)). Qed.
Lemma lem1261275 (B : nat) : term180 B.
Proof. exact (@lem1261124 B (@lem1261274 B)). Qed.
Lemma lem1261276 (B : nat) (n : nat) : term162 B n.
Proof. exact (@lem1261275 B n). Qed.
Lemma lem1261277 (B : nat) (n : nat) : (term162 B n) = (term163 B n).
Proof. exact (eq_refl (term162 B n)). Qed.
Lemma lem1261278 (B : nat) (n : nat) : term163 B n.
Proof. exact (EQ_MP (@lem1261277 B n) (@lem1261276 B n)). Qed.
Lemma lem1261279 (B : nat) (n : nat) (h1 : term59 n) : term154 B n.
Proof. exact (@lem1261278 B n (@lem1260726 n h1)). Qed.
Lemma lem1261280 (B : nat) (P : nat -> nat) (n : nat) (h1 : term59 n) : term152 B P n.
Proof. exact (EQ_MP (@lem1261101 B P n) (@lem1261279 B n h1)). Qed.
Lemma lem1261281 (B : nat) (P : nat -> nat) (n : nat) (h1 : term59 n) : term205 B P n.
Proof. exact (ex_intro (term206 B P n) (Nat.mul B n) (@lem1261280 B P n h1)). Qed.
Lemma lem1261282 (B : nat) (P : nat -> nat) (n : nat) (h1 : term59 n) : term147 B P n.
Proof. exact (@lem1261089 B P n (@lem1261281 B P n h1)). Qed.
Lemma lem1261283 (A : nat) (B : nat) (P : nat -> nat) (n : nat) (h1 : term59 n) : term144 A B P n.
Proof. exact (EQ_MP (@lem1261086 A B P n) (@lem1261282 B P n h1)). Qed.
Lemma lem1261284 (A : nat) (B : nat) (P : nat -> nat) (n : nat) (h1 : term59 n) : term137 A B n P.
Proof. exact (EQ_MP (@lem1261074 A B n P) (@lem1261283 A B P n h1)). Qed.
Lemma lem1261285 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : term134 P A n B.
Proof. exact (EQ_MP (@lem1261056 P A n B) (@lem1261284 A B P n h1)). Qed.
Lemma lem1261286 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term59 n) : term127 n P A B.
Proof. exact (EQ_MP (@lem1261050 n P A B) (@lem1261285 P A B n h1)). Qed.
Lemma lem1261287 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term76 P A B) (h2 : term59 n) : term128 n P A B.
Proof. exact (EQ_MP (@lem1261038 n P A B h1) (@lem1261286 P A B n h2)). Qed.
Lemma lem1261288 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term76 P A B) (h2 : term59 n) : term207 n P A B.
Proof. exact (ex_intro (term208 n P A B) (term209 A n B) (@lem1261287 P A B n h1 h2)). Qed.
Lemma lem1261289 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term76 P A B) (h2 : term59 n) : term66 n P A B.
Proof. exact (@lem1261007 n P A B (@lem1261288 P A B n h1 h2)). Qed.
Lemma lem1261290 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) (h2 : term59 n) (h3 : (term66 n P A B) = (term108 n P A B)) : term108 n P A B.
Proof. exact (EQ_MP (@lem1261004 n P A B h3) (@lem1261289 P A B n h1 h2)). Qed.
Lemma lem1261291 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term76 P A B) (h2 : term59 n) : term117 n P A B.
Proof. exact (fun h0 : (term66 n P A B) = (term108 n P A B) => @lem1261290 n P A B h1 h2 h0). Qed.
Lemma lem1261292 (P : nat -> nat) (A : nat) (B : nat) (n : nat) (h1 : term76 P A B) (h2 : term59 n) : term112 n P A B.
Proof. exact (EQ_MP (@lem1260989 P A B n h2) (@lem1261291 P A B n h1 h2)). Qed.
Lemma lem1261293 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term112 n P A B.
Proof. exact (or_elim (@lem1260724 n) (fun h0 : n = (NUMERAL 0) => @lem1260926 P A B n h0) (fun h0 : term59 n => @lem1261292 P A B n h1 h0)). Qed.
Lemma lem1261294 (n : nat) (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term108 n P A B.
Proof. exact (@lem1261293 n P A B h1 (@lem1260735 n P A B)). Qed.
Lemma lem1261299 (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term210 P A B.
Proof. exact (fun n : nat => @lem1261294 n P A B h1). Qed.
Lemma lem1261300 (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term72 P.
Proof. exact (ex_intro (term211 P) (term65 P A B) (@lem1261299 P A B h1)). Qed.
Lemma lem1261301 (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : (term76 P A B) = (term72 P).
Proof. exact (prop_ext (fun h2 : term76 P A B => @lem1261300 P A B h1) (fun h2 : term72 P => @lem1260770 P A B h1)). Qed.
Lemma lem1261302 (P : nat -> nat) (A : nat) (B : nat) (h1 : term76 P A B) : term72 P.
Proof. exact (EQ_MP (@lem1261301 P A B h1) (@lem1260770 P A B h1)). Qed.
Lemma lem1261303 (P : nat -> nat) (A : nat) (h1 : term75 P A) : term72 P.
Proof. exact (ex_elim (@lem1260769 P A h1) (fun B : nat => fun h0 : term93 P A B => @lem1261302 P A B h0)). Qed.
Lemma lem1261304 (P : nat -> nat) (h1 : term74 P) : term72 P.
Proof. exact (ex_elim (@lem1260768 P h1) (fun A : nat => fun h0 : term94 P A => @lem1261303 P A h0)). Qed.
Lemma lem1261305 (P : nat -> nat) : term212 P.
Proof. exact (fun h0 : term74 P => @lem1261304 P h0). Qed.
Lemma lem1261306 (P : nat -> nat) (B : nat) (h1 : term73 P B) : (term73 P B) = (term74 P).
Proof. exact (prop_ext (fun h2 : term73 P B => @lem1260823 P B h1) (fun h2 : term74 P => @lem1260767 P B h1)). Qed.
Lemma lem1261307 (P : nat -> nat) (B : nat) (h1 : term73 P B) : term74 P.
Proof. exact (EQ_MP (@lem1261306 P B h1) (@lem1260767 P B h1)). Qed.
Lemma lem1261308 (P : nat -> nat) (h1 : term72 P) : term74 P.
Proof. exact (ex_elim (@lem1260766 P h1) (fun B : nat => fun h0 : term211 P B => @lem1261307 P B h0)). Qed.
Lemma lem1261309 (P : nat -> nat) : term213 P.
Proof. exact (fun h0 : term72 P => @lem1261308 P h0). Qed.
Lemma lem1261310 (P : nat -> nat) : term214 P.
Proof. exact (conj (@lem1261309 P) (@lem1261305 P)). Qed.
Lemma lem1261311 (P : nat -> nat) : (term214 P) = ((term72 P) = (term74 P)).
Proof. exact (@lem32 (term72 P) (term74 P)). Qed.
Lemma lem1261312 (P : nat -> nat) : (term72 P) = (term74 P).
Proof. exact (EQ_MP (@lem1261311 P) (@lem1261310 P)). Qed.
Lemma lem1261317 : term215.
Proof. exact (fun P : nat -> nat => @lem1261312 P). Qed.
