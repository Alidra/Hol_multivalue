Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOUNDS_IGNORE_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import LE_TRANS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1834_spec.
Require Import thm1843_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem1261659 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1261660 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1261661 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1261660 m) (@lem1261659 m)). Qed.
Lemma lem1261662 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1261661 m n). Qed.
Lemma lem1261663 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1261664 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1261663 m n) (@lem1261662 m n)). Qed.
Lemma lem1261665 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1261667 (m : nat) : term4 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1261668 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1261669 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1261668 m) (@lem1261667 m)). Qed.
Lemma lem1261670 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1261669 m n). Qed.
Lemma lem1261671 (n : nat) (m : nat) : (term6 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1261673 (m : nat) : term7 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1261674 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1261675 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1261674 m) (@lem1261673 m)). Qed.
Lemma lem1261676 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1261675 m n). Qed.
Lemma lem1261677 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1261678 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1261677 m n) (@lem1261676 m n)). Qed.
Lemma lem1261679 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1261678 m n p). Qed.
Lemma lem1261680 (m : nat) (n : nat) (p : nat) : (term11 m n p) = ((term12 m n p) = (term13 m n p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1261684 (n : nat) (m : nat) (h1 : (term14 m n) = (Peano.lt n m)) : (term14 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem1261685 (n : nat) (m : nat) (h1 : (term14 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term14 m n).
Proof. exact (SYM (@lem1261684 n m h1)). Qed.
Lemma lem1261686 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term14 m n)) : (Peano.lt n m) = (term14 m n).
Proof. exact (h1). Qed.
Lemma lem1261687 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term14 m n)) : (term14 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem1261686 m n h1)). Qed.
Lemma lem1261688 (m : nat) (n : nat) : ((term14 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term14 m n)).
Proof. exact (prop_ext (fun h1 : (term14 m n) = (Peano.lt n m) => @lem1261685 n m h1) (fun h1 : (Peano.lt n m) = (term14 m n) => @lem1261687 m n h1)). Qed.
Lemma lem1261689 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem1261688 m n)). Qed.
Lemma lem1261690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261691 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem1261690) (@lem1261689 m)). Qed.
Lemma lem1261692 : term19 = term20.
Proof. exact (fun_ext (fun m : nat => @lem1261691 m)). Qed.
Lemma lem1261693 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261694 : term21 = term22.
Proof. exact (MK_COMB (@lem1261693) (@lem1261692)). Qed.
Lemma lem1261695 : term22.
Proof. exact (EQ_MP (@lem1261694) (@lem97961)). Qed.
Lemma lem1261696 : term23.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem1261697 (m : nat) : term24 m.
Proof. exact (@lem1261696 m). Qed.
Lemma lem1261698 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1261699 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1261698 m) (@lem1261697 m)). Qed.
Lemma lem1261700 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1261699 m n). Qed.
Lemma lem1261701 (m : nat) (n : nat) : (term26 m n) = ((term27 m n) = (term28 m n)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1261707 (m : nat) : term29 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1261708 (m : nat) : (term29 m) = (term17 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1261709 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem1261708 m) (@lem1261707 m)). Qed.
Lemma lem1261710 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1261709 m n). Qed.
Lemma lem1261711 (n : nat) (m : nat) : (term30 m n) = ((term14 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1261713 (m : nat) : term7 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1261714 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1261715 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1261714 m) (@lem1261713 m)). Qed.
Lemma lem1261716 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1261715 m n). Qed.
Lemma lem1261717 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1261718 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1261717 m n) (@lem1261716 m n)). Qed.
Lemma lem1261719 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1261718 m n p). Qed.
Lemma lem1261720 (m : nat) (n : nat) (p : nat) : (term11 m n p) = ((term12 m n p) = (term13 m n p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1261722 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1261723 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1261724 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1261723 m) (@lem1261722 m)). Qed.
Lemma lem1261725 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1261724 m n). Qed.
Lemma lem1261726 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1261727 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1261726 m n) (@lem1261725 m n)). Qed.
Lemma lem1261728 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1261730 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1261731 (m : nat) (h1 : term31) : term32 m.
Proof. exact (@lem1261730 h1 m). Qed.
Lemma lem1261732 (m : nat) : (term32 m) = (term33 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1261733 (m : nat) (h1 : term31) : term33 m.
Proof. exact (EQ_MP (@lem1261732 m) (@lem1261731 m h1)). Qed.
Lemma lem1261734 (m : nat) (n : nat) (h1 : term31) : term34 m n.
Proof. exact (@lem1261733 m h1 n). Qed.
Lemma lem1261735 (n : nat) (m : nat) : (term34 m n) = (term35 n m).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1261736 (n : nat) (m : nat) (h1 : term31) : term35 n m.
Proof. exact (EQ_MP (@lem1261735 n m) (@lem1261734 m n h1)). Qed.
Lemma lem1261737 (n : nat) (m : nat) (p : nat) (h1 : term31) : term36 n m p.
Proof. exact (@lem1261736 n m h1 p). Qed.
Lemma lem1261738 (n : nat) (m : nat) (p : nat) : (term36 n m p) = (term37 n m p).
Proof. exact (eq_refl (term36 n m p)). Qed.
Lemma lem1261739 (n : nat) (m : nat) (p : nat) (h1 : term31) : term37 n m p.
Proof. exact (EQ_MP (@lem1261738 n m p) (@lem1261737 n m p h1)). Qed.
Lemma lem1261740 (m : nat) (n : nat) (p : nat) (h1 : term38 m n p) : term38 m n p.
Proof. exact (h1). Qed.
Lemma lem1261741 (m : nat) (n : nat) (p : nat) (h1 : term31) (h2 : term38 m n p) : Peano.le m p.
Proof. exact (@lem1261739 n m p h1 (@lem1261740 m n p h2)). Qed.
Lemma lem1261742 (m : nat) (n : nat) (p : nat) (h1 : term38 m n p) : term39 m p.
Proof. exact (fun h0 : term31 => @lem1261741 m n p h0 h1). Qed.
Lemma lem1261743 (m : nat) (p : nat) (h1 : term40 m p) : term40 m p.
Proof. exact (h1). Qed.
Lemma lem1261744 (m : nat) (p : nat) (h1 : term40 m p) : term39 m p.
Proof. exact (ex_elim (@lem1261743 m p h1) (fun n : nat => fun h0 : term41 m p n => @lem1261742 m n p h0)). Qed.
Lemma lem1261745 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1261746 (m : nat) (p : nat) (h1 : term31) (h2 : term40 m p) : Peano.le m p.
Proof. exact (@lem1261744 m p h2 (@lem1261745 h1)). Qed.
Lemma lem1261747 (m : nat) (p : nat) (h1 : term31) : term42 m p.
Proof. exact (fun h0 : term40 m p => @lem1261746 m p h1 h0). Qed.
Lemma lem1261748 (m : nat) (h1 : term31) : term43 m.
Proof. exact (fun p : nat => @lem1261747 m p h1). Qed.
Lemma lem1261749 (h1 : term31) : term44.
Proof. exact (fun m : nat => @lem1261748 m h1). Qed.
Lemma lem1261750 : term45.
Proof. exact (fun h0 : term31 => @lem1261749 h0). Qed.
Lemma lem1261751 : term44.
Proof. exact (@lem1261750 (@lem93743)). Qed.
Lemma lem1261752 (m : nat) : term46 m.
Proof. exact (@lem1261751 m). Qed.
Lemma lem1261753 (m : nat) : (term46 m) = (term43 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1261754 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1261753 m) (@lem1261752 m)). Qed.
Lemma lem1261755 (m : nat) (p : nat) : term47 m p.
Proof. exact (@lem1261754 m p). Qed.
Lemma lem1261756 (m : nat) (p : nat) : (term47 m p) = (term42 m p).
Proof. exact (eq_refl (term47 m p)). Qed.
Lemma lem1261758 (N : nat) (i : nat) : term48 N i.
Proof. exact (@lem9784 (term49 N i)). Qed.
Lemma lem1261759 (N : nat) (i : nat) : (term48 N i) = (term50 N i).
Proof. exact (eq_refl (term48 N i)). Qed.
Lemma lem1261760 (N : nat) (i : nat) : term50 N i.
Proof. exact (EQ_MP (@lem1261759 N i) (@lem1261758 N i)). Qed.
Lemma lem1261761 (N : nat) (i : nat) (h1 : term49 N i) : term49 N i.
Proof. exact (h1). Qed.
Lemma lem1261762 (N : nat) (i : nat) (h1 : term51 N i) : term51 N i.
Proof. exact (h1). Qed.
Lemma lem1261763 (n : nat) : term52 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1261764 (n : nat) : (term52 n) = (term53 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1261765 (n : nat) : term53 n.
Proof. exact (EQ_MP (@lem1261764 n) (@lem1261763 n)). Qed.
Lemma lem1261766 (n : nat) : (term53 n) = ((term53 n) = True).
Proof. exact (@lem7 (term53 n)). Qed.
Lemma lem1261768 (P : nat -> nat) (Q : nat -> nat) (h1 : term54 P Q) : term54 P Q.
Proof. exact (h1). Qed.
Lemma lem1261769 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term55 P Q B.
Proof. exact (h1). Qed.
Lemma lem1261770 (P : nat -> nat) (Q : nat -> nat) (h1 : term56 P Q) : term56 P Q.
Proof. exact (h1). Qed.
Lemma lem1261771 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term57 P Q B) : term57 P Q B.
Proof. exact (h1). Qed.
Lemma lem1261772 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : term58 N P Q B.
Proof. exact (h1). Qed.
Lemma lem1261773 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term59 P Q B i.
Proof. exact (@lem1261769 P Q B h1 i). Qed.
Lemma lem1261774 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term59 P Q B i) = (term60 P Q i B).
Proof. exact (eq_refl (term59 P Q B i)). Qed.
Lemma lem1261775 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term60 P Q i B.
Proof. exact (EQ_MP (@lem1261774 P Q i B) (@lem1261773 i P Q B h1)). Qed.
Lemma lem1261776 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term60 P Q i B) = ((term60 P Q i B) = True).
Proof. exact (@lem7 (term60 P Q i B)). Qed.
Lemma lem1261789 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term60 P Q i B) = True.
Proof. exact (EQ_MP (@lem1261776 P Q i B) (@lem1261775 i P Q B h1)). Qed.
Lemma lem1261790 (N : nat) (i : nat) : (term61 N i) = (term61 N i).
Proof. exact (eq_refl (term61 N i)). Qed.
Lemma lem1261791 (N : nat) (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term62 N P Q i B) = (term63 N i).
Proof. exact (MK_COMB (@lem1261790 N i) (@lem1261789 i P Q B h1)). Qed.
Lemma lem1261793 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1261794 (N : nat) (i : nat) : (term63 N i) = True.
Proof. exact (@lem1261793 (Peano.le N i)). Qed.
Lemma lem1261795 (N : nat) (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term62 N P Q i B) = True.
Proof. exact (TRANS (@lem1261791 N i P Q B h1) (@lem1261794 N i)). Qed.
Lemma lem1261796 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term64 N P Q B) = term65.
Proof. exact (fun_ext (fun i : nat => @lem1261795 N i P Q B h1)). Qed.
Lemma lem1261797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261798 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term58 N P Q B) = term66.
Proof. exact (MK_COMB (@lem1261797) (@lem1261796 N P Q B h1)). Qed.
Lemma lem1261800 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1261801 (t : Prop) : (term68 t) = t.
Proof. exact (@lem1261800 nat t). Qed.
Lemma lem1261802 : term66 = True.
Proof. exact (@lem1261801 True). Qed.
Lemma lem1261803 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term58 N P Q B) = True.
Proof. exact (TRANS (@lem1261798 N P Q B h1) (@lem1261802)). Qed.
Lemma lem1261804 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term69 P Q B) = term65.
Proof. exact (fun_ext (fun N : nat => @lem1261803 N P Q B h1)). Qed.
Lemma lem1261805 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1261806 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term57 P Q B) = term70.
Proof. exact (MK_COMB (@lem1261805) (@lem1261804 P Q B h1)). Qed.
Lemma lem1261808 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1261809 (t : Prop) : (term72 t) = t.
Proof. exact (@lem1261808 nat t). Qed.
Lemma lem1261810 : term70 = True.
Proof. exact (@lem1261809 True). Qed.
Lemma lem1261811 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term57 P Q B) = True.
Proof. exact (TRANS (@lem1261806 P Q B h1) (@lem1261810)). Qed.
Lemma lem1261812 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : True = (term57 P Q B).
Proof. exact (SYM (@lem1261811 P Q B h1)). Qed.
Lemma lem1261813 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term57 P Q B.
Proof. exact (EQ_MP (@lem1261812 P Q B h1) (@lem0)). Qed.
Lemma lem1261814 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term56 P Q.
Proof. exact (ex_intro (term73 P Q) B (@lem1261813 P Q B h1)). Qed.
Lemma lem1261816 (P : nat -> Prop) : term74 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1261817 (P : nat -> nat) (Q : nat -> nat) : term75 P Q.
Proof. exact (@lem1261816 (term76 P Q)). Qed.
Lemma lem1261818 (P : nat -> nat) (Q : nat -> nat) : (term77 P Q) = (term78 P Q).
Proof. exact (eq_refl (term77 P Q)). Qed.
Lemma lem1261819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1261820 (P : nat -> nat) (Q : nat -> nat) : (term79 P Q) = (term80 P Q).
Proof. exact (MK_COMB (@lem1261819) (@lem1261818 P Q)). Qed.
Lemma lem1261821 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term81 P Q N) = (term82 N P Q).
Proof. exact (eq_refl (term81 P Q N)). Qed.
Lemma lem1261822 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261823 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term83 P Q N) = (term84 N P Q).
Proof. exact (MK_COMB (@lem1261822) (@lem1261821 N P Q)). Qed.
Lemma lem1261824 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term85 P Q N) = (term86 N P Q).
Proof. exact (eq_refl (term85 P Q N)). Qed.
Lemma lem1261825 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term87 P Q N) = (term88 N P Q).
Proof. exact (MK_COMB (@lem1261823 N P Q) (@lem1261824 N P Q)). Qed.
Lemma lem1261826 (P : nat -> nat) (Q : nat -> nat) : (term89 P Q) = (term90 P Q).
Proof. exact (fun_ext (fun N : nat => @lem1261825 N P Q)). Qed.
Lemma lem1261827 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261828 (P : nat -> nat) (Q : nat -> nat) : (term91 P Q) = (term92 P Q).
Proof. exact (MK_COMB (@lem1261827) (@lem1261826 P Q)). Qed.
Lemma lem1261829 (P : nat -> nat) (Q : nat -> nat) : (term93 P Q) = (term94 P Q).
Proof. exact (MK_COMB (@lem1261820 P Q) (@lem1261828 P Q)). Qed.
Lemma lem1261830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261831 (P : nat -> nat) (Q : nat -> nat) : (term95 P Q) = (term96 P Q).
Proof. exact (MK_COMB (@lem1261830) (@lem1261829 P Q)). Qed.
Lemma lem1261832 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term81 P Q N) = (term82 N P Q).
Proof. exact (eq_refl (term81 P Q N)). Qed.
Lemma lem1261833 (P : nat -> nat) (Q : nat -> nat) : (term97 P Q) = (term76 P Q).
Proof. exact (fun_ext (fun N : nat => @lem1261832 N P Q)). Qed.
Lemma lem1261834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261835 (P : nat -> nat) (Q : nat -> nat) : (term98 P Q) = (term99 P Q).
Proof. exact (MK_COMB (@lem1261834) (@lem1261833 P Q)). Qed.
Lemma lem1261836 (P : nat -> nat) (Q : nat -> nat) : (term75 P Q) = (term100 P Q).
Proof. exact (MK_COMB (@lem1261831 P Q) (@lem1261835 P Q)). Qed.
Lemma lem1261837 (P : nat -> nat) (Q : nat -> nat) : term100 P Q.
Proof. exact (EQ_MP (@lem1261836 P Q) (@lem1261817 P Q)). Qed.
Lemma lem1261838 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term82 N P Q.
Proof. exact (h1). Qed.
Lemma lem1261852 (n : nat) : (term53 n) = True.
Proof. exact (EQ_MP (@lem1261766 n) (@lem1261765 n)). Qed.
Lemma lem1261853 (i : nat) : (term53 i) = True.
Proof. exact (@lem1261852 i). Qed.
Lemma lem1261854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261855 (i : nat) : (term101 i) = (imp True).
Proof. exact (MK_COMB (@lem1261854) (@lem1261853 i)). Qed.
Lemma lem1261856 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term60 P Q i B) = (term60 P Q i B).
Proof. exact (eq_refl (term60 P Q i B)). Qed.
Lemma lem1261857 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term102 P Q i B) = (term103 P Q i B).
Proof. exact (MK_COMB (@lem1261855 i) (@lem1261856 P Q i B)). Qed.
Lemma lem1261859 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1261860 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term103 P Q i B) = (term60 P Q i B).
Proof. exact (@lem1261859 (term60 P Q i B)). Qed.
Lemma lem1261861 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term102 P Q i B) = (term60 P Q i B).
Proof. exact (TRANS (@lem1261857 P Q i B) (@lem1261860 P Q i B)). Qed.
Lemma lem1261862 (P : nat -> nat) (Q : nat -> nat) (B : nat) : (term104 P Q B) = (term105 P Q B).
Proof. exact (fun_ext (fun i : nat => @lem1261861 P Q i B)). Qed.
Lemma lem1261863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261864 (P : nat -> nat) (Q : nat -> nat) (B : nat) : (term106 P Q B) = (term55 P Q B).
Proof. exact (MK_COMB (@lem1261863) (@lem1261862 P Q B)). Qed.
Lemma lem1261869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1261870 (P : nat -> nat) (Q : nat -> nat) (B : nat) : (term107 P Q B) = (term108 P Q B).
Proof. exact (MK_COMB (@lem1261869) (@lem1261864 P Q B)). Qed.
Lemma lem1261879 (P : nat -> nat) (Q : nat -> nat) : (term54 P Q) = (term54 P Q).
Proof. exact (eq_refl (term54 P Q)). Qed.
Lemma lem1261880 (B : nat) (P : nat -> nat) (Q : nat -> nat) : (term109 B P Q) = (term110 B P Q).
Proof. exact (MK_COMB (@lem1261870 P Q B) (@lem1261879 P Q)). Qed.
Lemma lem1261883 (P : nat -> nat) (Q : nat -> nat) : (term111 P Q) = (term112 P Q).
Proof. exact (fun_ext (fun B : nat => @lem1261880 B P Q)). Qed.
Lemma lem1261884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261885 (P : nat -> nat) (Q : nat -> nat) : (term78 P Q) = (term113 P Q).
Proof. exact (MK_COMB (@lem1261884) (@lem1261883 P Q)). Qed.
Lemma lem1261890 (P : nat -> nat) (Q : nat -> nat) : (term113 P Q) = (term78 P Q).
Proof. exact (SYM (@lem1261885 P Q)). Qed.
Lemma lem1261891 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term55 P Q B.
Proof. exact (h1). Qed.
Lemma lem1261892 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term59 P Q B i.
Proof. exact (@lem1261891 P Q B h1 i). Qed.
Lemma lem1261893 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term59 P Q B i) = (term60 P Q i B).
Proof. exact (eq_refl (term59 P Q B i)). Qed.
Lemma lem1261894 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term60 P Q i B.
Proof. exact (EQ_MP (@lem1261893 P Q i B) (@lem1261892 i P Q B h1)). Qed.
Lemma lem1261895 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term60 P Q i B) = ((term60 P Q i B) = True).
Proof. exact (@lem7 (term60 P Q i B)). Qed.
Lemma lem1261902 (i : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term60 P Q i B) = True.
Proof. exact (EQ_MP (@lem1261895 P Q i B) (@lem1261894 i P Q B h1)). Qed.
Lemma lem1261903 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term105 P Q B) = term65.
Proof. exact (fun_ext (fun i : nat => @lem1261902 i P Q B h1)). Qed.
Lemma lem1261904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1261905 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term55 P Q B) = term66.
Proof. exact (MK_COMB (@lem1261904) (@lem1261903 P Q B h1)). Qed.
Lemma lem1261907 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1261908 (t : Prop) : (term68 t) = t.
Proof. exact (@lem1261907 nat t). Qed.
Lemma lem1261909 : term66 = True.
Proof. exact (@lem1261908 True). Qed.
Lemma lem1261910 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term55 P Q B) = True.
Proof. exact (TRANS (@lem1261905 P Q B h1) (@lem1261909)). Qed.
Lemma lem1261911 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : True = (term55 P Q B).
Proof. exact (SYM (@lem1261910 P Q B h1)). Qed.
Lemma lem1261912 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term55 P Q B.
Proof. exact (EQ_MP (@lem1261911 P Q B h1) (@lem0)). Qed.
Lemma lem1261913 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term54 P Q.
Proof. exact (ex_intro (term114 P Q) B (@lem1261912 P Q B h1)). Qed.
Lemma lem1261914 (B : nat) (P : nat -> nat) (Q : nat -> nat) : term110 B P Q.
Proof. exact (fun h0 : term55 P Q B => @lem1261913 P Q B h0). Qed.
Lemma lem1261919 (P : nat -> nat) (Q : nat -> nat) : term113 P Q.
Proof. exact (fun B : nat => @lem1261914 B P Q). Qed.
Lemma lem1261920 (P : nat -> nat) (Q : nat -> nat) : term78 P Q.
Proof. exact (EQ_MP (@lem1261890 P Q) (@lem1261919 P Q)). Qed.
Lemma lem1261921 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term115 N P Q B.
Proof. exact (h1). Qed.
Lemma lem1261940 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term82 N P Q.
Proof. exact (h1). Qed.
Lemma lem1261941 (B : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term116 N P Q B.
Proof. exact (@lem1261940 N P Q h1 B). Qed.
Lemma lem1261942 (N : nat) (B : nat) (P : nat -> nat) (Q : nat -> nat) : (term116 N P Q B) = (term117 N B P Q).
Proof. exact (eq_refl (term116 N P Q B)). Qed.
Lemma lem1261943 (B : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term117 N B P Q.
Proof. exact (EQ_MP (@lem1261942 N B P Q) (@lem1261941 B N P Q h1)). Qed.
Lemma lem1261944 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : term58 N P Q B.
Proof. exact (h1). Qed.
Lemma lem1261945 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term82 N P Q) (h2 : term58 N P Q B) : term54 P Q.
Proof. exact (@lem1261943 B N P Q h1 (@lem1261944 N P Q B h2)). Qed.
Lemma lem1261946 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : term118 N P Q.
Proof. exact (fun h0 : term82 N P Q => @lem1261945 N P Q B h0 h1). Qed.
Lemma lem1261947 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term119 N P Q) : term119 N P Q.
Proof. exact (h1). Qed.
Lemma lem1261948 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term119 N P Q) : term118 N P Q.
Proof. exact (ex_elim (@lem1261947 N P Q h1) (fun B : nat => fun h0 : term120 N P Q B => @lem1261946 N P Q B h0)). Qed.
Lemma lem1261949 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term82 N P Q.
Proof. exact (h1). Qed.
Lemma lem1261950 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) (h2 : term119 N P Q) : term54 P Q.
Proof. exact (@lem1261948 N P Q h2 (@lem1261949 N P Q h1)). Qed.
Lemma lem1261951 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term121 N P Q.
Proof. exact (fun h0 : term119 N P Q => @lem1261950 N P Q h1 h0). Qed.
Lemma lem1261952 (N : nat) (P : nat -> nat) (Q : nat -> nat) : term122 N P Q.
Proof. exact (fun h0 : term82 N P Q => @lem1261951 N P Q h0). Qed.
Lemma lem1261955 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term121 N P Q.
Proof. exact (@lem1261952 N P Q (@lem1261838 N P Q h1)). Qed.
Lemma lem1261956 (N : nat) (i : nat) (h1 : Peano.le N i) : Peano.le N i.
Proof. exact (h1). Qed.
Lemma lem1261958 (m : nat) (p : nat) : term42 m p.
Proof. exact (EQ_MP (@lem1261756 m p) (@lem1261755 m p)). Qed.
Lemma lem1261959 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : term123 Q i B P N.
Proof. exact (@lem1261958 (P i) (term124 Q i B P N)). Qed.
Lemma lem1261967 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem1261720 m n p) (@lem1261719 m n p)). Qed.
Lemma lem1261968 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term124 Q i B P N) = (term125 Q i B P N).
Proof. exact (@lem1261967 (Q i) B (P N)). Qed.
Lemma lem1261969 (Q : nat -> nat) (i : nat) (B : nat) : (term126 Q i B) = (term126 Q i B).
Proof. exact (eq_refl (term126 Q i B)). Qed.
Lemma lem1261970 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term127 Q i B P N) = (term128 Q i B P N).
Proof. exact (MK_COMB (@lem1261969 Q i B) (@lem1261968 Q i B P N)). Qed.
Lemma lem1261972 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1261728 m n) (@lem1261727 m n)). Qed.
Lemma lem1261973 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term128 Q i B P N) = True.
Proof. exact (@lem1261972 (term129 Q i B) (P N)). Qed.
Lemma lem1261974 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term127 Q i B P N) = True.
Proof. exact (TRANS (@lem1261970 Q i B P N) (@lem1261973 Q i B P N)). Qed.
Lemma lem1261975 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term130 P Q i B) = (term130 P Q i B).
Proof. exact (eq_refl (term130 P Q i B)). Qed.
Lemma lem1261976 (N : nat) (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term131 Q i B P N) = (term132 P Q i B).
Proof. exact (MK_COMB (@lem1261975 P Q i B) (@lem1261974 Q i B P N)). Qed.
Lemma lem1261978 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1261979 (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term132 P Q i B) = (term60 P Q i B).
Proof. exact (@lem1261978 (term60 P Q i B)). Qed.
Lemma lem1261982 (N : nat) (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term131 Q i B P N) = (term60 P Q i B).
Proof. exact (TRANS (@lem1261976 N P Q i B) (@lem1261979 P Q i B)). Qed.
Lemma lem1261983 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term60 P Q i B) = (term131 Q i B P N).
Proof. exact (SYM (@lem1261982 N P Q i B)). Qed.
Lemma lem1261984 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term115 N P Q B.
Proof. exact (h1). Qed.
Lemma lem1261985 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term133 N P Q B i.
Proof. exact (@lem1261984 N P Q B h1 i). Qed.
Lemma lem1261986 (N : nat) (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term133 N P Q B i) = (term134 N P Q i B).
Proof. exact (eq_refl (term133 N P Q B i)). Qed.
Lemma lem1261987 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term134 N P Q i B.
Proof. exact (EQ_MP (@lem1261986 N P Q i B) (@lem1261985 i N P Q B h1)). Qed.
Lemma lem1261988 (N : nat) (i : nat) (h1 : term49 N i) : term49 N i.
Proof. exact (h1). Qed.
Lemma lem1261989 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term60 P Q i B.
Proof. exact (@lem1261987 i N P Q B h1 (@lem1261988 N i h2)). Qed.
Lemma lem1261990 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term49 N i) : term135 N P Q i B.
Proof. exact (fun h0 : term115 N P Q B => @lem1261989 P Q B N i h0 h1). Qed.
Lemma lem1261991 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term115 N P Q B.
Proof. exact (h1). Qed.
Lemma lem1261992 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term60 P Q i B.
Proof. exact (@lem1261990 P Q B N i h2 (@lem1261991 N P Q B h1)). Qed.
Lemma lem1261993 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term134 N P Q i B.
Proof. exact (fun h0 : term49 N i => @lem1261992 P Q B N i h1 h0). Qed.
Lemma lem1261994 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term115 N P Q B.
Proof. exact (fun i : nat => @lem1261993 i N P Q B h1). Qed.
Lemma lem1261995 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) : term136 N P Q B.
Proof. exact (fun h0 : term115 N P Q B => @lem1261994 N P Q B h0). Qed.
Lemma lem1261996 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term115 N P Q B.
Proof. exact (@lem1261995 N P Q B (@lem1261921 N P Q B h1)). Qed.
Lemma lem1261997 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term133 N P Q B i.
Proof. exact (@lem1261996 N P Q B h1 i). Qed.
Lemma lem1261998 (N : nat) (P : nat -> nat) (Q : nat -> nat) (i : nat) (B : nat) : (term133 N P Q B i) = (term134 N P Q i B).
Proof. exact (eq_refl (term133 N P Q B i)). Qed.
Lemma lem1262001 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term134 N P Q i B.
Proof. exact (EQ_MP (@lem1261998 N P Q i B) (@lem1261997 i N P Q B h1)). Qed.
Lemma lem1262014 (N : nat) (i : nat) : (term49 N i) = ((term49 N i) = True).
Proof. exact (@lem7 (term49 N i)). Qed.
Lemma lem1262017 (N : nat) (i : nat) (h1 : term49 N i) : (term49 N i) = True.
Proof. exact (EQ_MP (@lem1262014 N i) (@lem1261761 N i h1)). Qed.
Lemma lem1262018 (N : nat) (i : nat) (h1 : term49 N i) : True = (term49 N i).
Proof. exact (SYM (@lem1262017 N i h1)). Qed.
Lemma lem1262019 (N : nat) (i : nat) (h1 : term49 N i) : term49 N i.
Proof. exact (EQ_MP (@lem1262018 N i h1) (@lem0)). Qed.
Lemma lem1262020 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term60 P Q i B.
Proof. exact (@lem1262001 i N P Q B h1 (@lem1262019 N i h2)). Qed.
Lemma lem1262021 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term131 Q i B P N.
Proof. exact (EQ_MP (@lem1261983 Q i B P N) (@lem1262020 P Q B N i h1 h2)). Qed.
Lemma lem1262022 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term137 Q i B P N.
Proof. exact (ex_intro (term138 Q i B P N) (term129 Q i B) (@lem1262021 P Q B N i h1 h2)). Qed.
Lemma lem1262023 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : term49 N i) : term139 Q i B P N.
Proof. exact (@lem1261959 Q i B P N (@lem1262022 P Q B N i h1 h2)). Qed.
Lemma lem1262027 (n : nat) (m : nat) : (term14 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1261711 n m) (@lem1261710 m n)). Qed.
Lemma lem1262028 (i : nat) (N : nat) : (term51 N i) = (term27 i N).
Proof. exact (@lem1262027 i (S N)). Qed.
Lemma lem1262030 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (EQ_MP (@lem1261701 m n) (@lem1261700 m n)). Qed.
Lemma lem1262031 (i : nat) (N : nat) : (term27 i N) = (term28 i N).
Proof. exact (@lem1262030 i N). Qed.
Lemma lem1262034 (i : nat) (N : nat) : (term51 N i) = (term28 i N).
Proof. exact (TRANS (@lem1262028 i N) (@lem1262031 i N)). Qed.
Lemma lem1262037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1262038 (i : nat) (N : nat) : (term140 N i) = (term141 i N).
Proof. exact (MK_COMB (@lem1262037) (@lem1262034 i N)). Qed.
Lemma lem1262039 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term139 Q i B P N) = (term139 Q i B P N).
Proof. exact (eq_refl (term139 Q i B P N)). Qed.
Lemma lem1262040 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term142 Q i B P N) = (term143 Q i B P N).
Proof. exact (MK_COMB (@lem1262038 i N) (@lem1262039 Q i B P N)). Qed.
Lemma lem1262043 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term143 Q i B P N) = (term142 Q i B P N).
Proof. exact (SYM (@lem1262040 Q i B P N)). Qed.
Lemma lem1262044 (m : nat) : term144 m.
Proof. exact (@lem1261695 m). Qed.
Lemma lem1262045 (m : nat) : (term144 m) = (term18 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem1262046 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1262045 m) (@lem1262044 m)). Qed.
Lemma lem1262047 (m : nat) (n : nat) : term145 m n.
Proof. exact (@lem1262046 m n). Qed.
Lemma lem1262048 (m : nat) (n : nat) : (term145 m n) = ((Peano.lt n m) = (term14 m n)).
Proof. exact (eq_refl (term145 m n)). Qed.
Lemma lem1262060 (N : nat) (i : nat) : (Peano.le N i) = ((Peano.le N i) = True).
Proof. exact (@lem7 (Peano.le N i)). Qed.
Lemma lem1262069 (m : nat) (n : nat) : (Peano.lt n m) = (term14 m n).
Proof. exact (EQ_MP (@lem1262048 m n) (@lem1262047 m n)). Qed.
Lemma lem1262070 (N : nat) (i : nat) : (Peano.lt i N) = (term14 N i).
Proof. exact (@lem1262069 N i). Qed.
Lemma lem1262072 (N : nat) (i : nat) (h1 : Peano.le N i) : (Peano.le N i) = True.
Proof. exact (EQ_MP (@lem1262060 N i) (@lem1261956 N i h1)). Qed.
Lemma lem1262073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1262074 (N : nat) (i : nat) (h1 : Peano.le N i) : (term14 N i) = (~ True).
Proof. exact (MK_COMB (@lem1262073) (@lem1262072 N i h1)). Qed.
Lemma lem1262076 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1262077 (N : nat) (i : nat) (h1 : Peano.le N i) : (term14 N i) = False.
Proof. exact (TRANS (@lem1262074 N i h1) (@lem1262076)). Qed.
Lemma lem1262078 (N : nat) (i : nat) (h1 : Peano.le N i) : (Peano.lt i N) = False.
Proof. exact (TRANS (@lem1262070 N i) (@lem1262077 N i h1)). Qed.
Lemma lem1262079 (i : nat) (N : nat) : (term146 i N) = (term146 i N).
Proof. exact (eq_refl (term146 i N)). Qed.
Lemma lem1262080 (N : nat) (i : nat) (h1 : Peano.le N i) : (term28 i N) = (term147 i N).
Proof. exact (MK_COMB (@lem1262079 i N) (@lem1262078 N i h1)). Qed.
Lemma lem1262082 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1262083 (i : nat) (N : nat) : (term147 i N) = (i = N).
Proof. exact (@lem1262082 (i = N)). Qed.
Lemma lem1262086 (N : nat) (i : nat) (h1 : Peano.le N i) : (term28 i N) = (i = N).
Proof. exact (TRANS (@lem1262080 N i h1) (@lem1262083 i N)). Qed.
Lemma lem1262087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1262088 (N : nat) (i : nat) (h1 : Peano.le N i) : (term141 i N) = (term148 i N).
Proof. exact (MK_COMB (@lem1262087) (@lem1262086 N i h1)). Qed.
Lemma lem1262089 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term139 Q i B P N) = (term139 Q i B P N).
Proof. exact (eq_refl (term139 Q i B P N)). Qed.
Lemma lem1262090 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) (h1 : Peano.le N i) : (term143 Q i B P N) = (term149 Q i B P N).
Proof. exact (MK_COMB (@lem1262088 N i h1) (@lem1262089 Q i B P N)). Qed.
Lemma lem1262095 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) (h1 : Peano.le N i) : (term149 Q i B P N) = (term143 Q i B P N).
Proof. exact (SYM (@lem1262090 Q B P N i h1)). Qed.
Lemma lem1262096 (i : nat) (N : nat) (h1 : i = N) : i = N.
Proof. exact (h1). Qed.
Lemma lem1262097 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term150 Q B P N) = (term150 Q B P N).
Proof. exact (eq_refl (term150 Q B P N)). Qed.
Lemma lem1262098 (Q : nat -> nat) (B : nat) (P : nat -> nat) (i : nat) (N : nat) (h1 : i = N) : (term151 Q B P N i) = (term152 Q B P N).
Proof. exact (MK_COMB (@lem1262097 Q B P N) (@lem1262096 i N h1)). Qed.
Lemma lem1262099 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term152 Q B P N) = (term153 Q B P N).
Proof. exact (eq_refl (term152 Q B P N)). Qed.
Lemma lem1262100 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) : (term154 Q B P N i) = (term154 Q B P N i).
Proof. exact (eq_refl (term154 Q B P N i)). Qed.
Lemma lem1262101 (i : nat) (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : ((term151 Q B P N i) = (term152 Q B P N)) = ((term151 Q B P N i) = (term153 Q B P N)).
Proof. exact (MK_COMB (@lem1262100 Q B P N i) (@lem1262099 Q B P N)). Qed.
Lemma lem1262102 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term151 Q B P N i) = (term139 Q i B P N).
Proof. exact (eq_refl (term151 Q B P N i)). Qed.
Lemma lem1262103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1262104 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : (term154 Q B P N i) = (term155 Q i B P N).
Proof. exact (MK_COMB (@lem1262103) (@lem1262102 Q i B P N)). Qed.
Lemma lem1262105 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term153 Q B P N) = (term153 Q B P N).
Proof. exact (eq_refl (term153 Q B P N)). Qed.
Lemma lem1262106 (i : nat) (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : ((term151 Q B P N i) = (term153 Q B P N)) = ((term139 Q i B P N) = (term153 Q B P N)).
Proof. exact (MK_COMB (@lem1262104 Q i B P N) (@lem1262105 Q B P N)). Qed.
Lemma lem1262107 (i : nat) (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : ((term151 Q B P N i) = (term152 Q B P N)) = ((term139 Q i B P N) = (term153 Q B P N)).
Proof. exact (TRANS (@lem1262101 i Q B P N) (@lem1262106 i Q B P N)). Qed.
Lemma lem1262108 (Q : nat -> nat) (B : nat) (P : nat -> nat) (i : nat) (N : nat) (h1 : i = N) : (term139 Q i B P N) = (term153 Q B P N).
Proof. exact (EQ_MP (@lem1262107 i Q B P N) (@lem1262098 Q B P i N h1)). Qed.
Lemma lem1262109 (Q : nat -> nat) (B : nat) (P : nat -> nat) (i : nat) (N : nat) (h1 : i = N) : (term153 Q B P N) = (term139 Q i B P N).
Proof. exact (SYM (@lem1262108 Q B P i N h1)). Qed.
Lemma lem1262111 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem1261680 m n p) (@lem1261679 m n p)). Qed.
Lemma lem1262112 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term156 Q B P N) = (term157 Q B P N).
Proof. exact (@lem1262111 (Q N) B (P N)). Qed.
Lemma lem1262113 (P : nat -> nat) (N : nat) : (term158 P N) = (term158 P N).
Proof. exact (eq_refl (term158 P N)). Qed.
Lemma lem1262114 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term153 Q B P N) = (term159 Q B P N).
Proof. exact (MK_COMB (@lem1262113 P N) (@lem1262112 Q B P N)). Qed.
Lemma lem1262115 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term159 Q B P N) = (term153 Q B P N).
Proof. exact (SYM (@lem1262114 Q B P N)). Qed.
Lemma lem1262117 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1261671 n m) (@lem1261670 m n)). Qed.
Lemma lem1262118 (P : nat -> nat) (Q : nat -> nat) (N : nat) (B : nat) : (term157 Q B P N) = (term160 P Q N B).
Proof. exact (@lem1262117 (P N) (term129 Q N B)). Qed.
Lemma lem1262119 (P : nat -> nat) (N : nat) : (term158 P N) = (term158 P N).
Proof. exact (eq_refl (term158 P N)). Qed.
Lemma lem1262120 (P : nat -> nat) (Q : nat -> nat) (N : nat) (B : nat) : (term159 Q B P N) = (term161 P Q N B).
Proof. exact (MK_COMB (@lem1262119 P N) (@lem1262118 P Q N B)). Qed.
Lemma lem1262121 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : (term161 P Q N B) = (term159 Q B P N).
Proof. exact (SYM (@lem1262120 P Q N B)). Qed.
Lemma lem1262123 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1261665 m n) (@lem1261664 m n)). Qed.
Lemma lem1262124 (P : nat -> nat) (Q : nat -> nat) (N : nat) (B : nat) : (term161 P Q N B) = True.
Proof. exact (@lem1262123 (P N) (term129 Q N B)). Qed.
Lemma lem1262125 (P : nat -> nat) (Q : nat -> nat) (N : nat) (B : nat) : True = (term161 P Q N B).
Proof. exact (SYM (@lem1262124 P Q N B)). Qed.
Lemma lem1262126 (P : nat -> nat) (Q : nat -> nat) (N : nat) (B : nat) : term161 P Q N B.
Proof. exact (EQ_MP (@lem1262125 P Q N B) (@lem0)). Qed.
Lemma lem1262127 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : term159 Q B P N.
Proof. exact (EQ_MP (@lem1262121 Q B P N) (@lem1262126 P Q N B)). Qed.
Lemma lem1262128 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) : term153 Q B P N.
Proof. exact (EQ_MP (@lem1262115 Q B P N) (@lem1262127 Q B P N)). Qed.
Lemma lem1262129 (Q : nat -> nat) (B : nat) (P : nat -> nat) (i : nat) (N : nat) (h1 : i = N) : term139 Q i B P N.
Proof. exact (EQ_MP (@lem1262109 Q B P i N h1) (@lem1262128 Q B P N)). Qed.
Lemma lem1262130 (Q : nat -> nat) (i : nat) (B : nat) (P : nat -> nat) (N : nat) : term149 Q i B P N.
Proof. exact (fun h0 : i = N => @lem1262129 Q B P i N h0). Qed.
Lemma lem1262131 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) (h1 : Peano.le N i) : term143 Q i B P N.
Proof. exact (EQ_MP (@lem1262095 Q B P N i h1) (@lem1262130 Q i B P N)). Qed.
Lemma lem1262132 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) (h1 : Peano.le N i) : term142 Q i B P N.
Proof. exact (EQ_MP (@lem1262043 Q i B P N) (@lem1262131 Q B P N i h1)). Qed.
Lemma lem1262133 (Q : nat -> nat) (B : nat) (P : nat -> nat) (N : nat) (i : nat) (h1 : term51 N i) (h2 : Peano.le N i) : term139 Q i B P N.
Proof. exact (@lem1262132 Q B P N i h2 (@lem1261762 N i h1)). Qed.
Lemma lem1262134 (P : nat -> nat) (Q : nat -> nat) (B : nat) (N : nat) (i : nat) (h1 : term115 N P Q B) (h2 : Peano.le N i) : term139 Q i B P N.
Proof. exact (or_elim (@lem1261760 N i) (fun h0 : term49 N i => @lem1262023 P Q B N i h1 h0) (fun h0 : term51 N i => @lem1262133 Q B P N i h0 h2)). Qed.
Lemma lem1262135 (i : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term162 Q i B P N.
Proof. exact (fun h0 : Peano.le N i => @lem1262134 P Q B N i h1 h0). Qed.
Lemma lem1262140 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term163 Q B P N.
Proof. exact (fun i : nat => @lem1262135 i N P Q B h1). Qed.
Lemma lem1262141 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term115 N P Q B) : term119 N P Q.
Proof. exact (ex_intro (term120 N P Q) (term164 B P N) (@lem1262140 N P Q B h1)). Qed.
Lemma lem1262142 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term82 N P Q) (h2 : term115 N P Q B) : term54 P Q.
Proof. exact (@lem1261955 N P Q h1 (@lem1262141 N P Q B h2)). Qed.
Lemma lem1262143 (B : nat) (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term165 N B P Q.
Proof. exact (fun h0 : term115 N P Q B => @lem1262142 N P Q B h1 h0). Qed.
Lemma lem1262148 (N : nat) (P : nat -> nat) (Q : nat -> nat) (h1 : term82 N P Q) : term86 N P Q.
Proof. exact (fun B : nat => @lem1262143 B N P Q h1). Qed.
Lemma lem1262149 (N : nat) (P : nat -> nat) (Q : nat -> nat) : term88 N P Q.
Proof. exact (fun h0 : term82 N P Q => @lem1262148 N P Q h0). Qed.
Lemma lem1262154 (P : nat -> nat) (Q : nat -> nat) : term92 P Q.
Proof. exact (fun N : nat => @lem1262149 N P Q). Qed.
Lemma lem1262155 (P : nat -> nat) (Q : nat -> nat) : term94 P Q.
Proof. exact (conj (@lem1261920 P Q) (@lem1262154 P Q)). Qed.
Lemma lem1262156 (P : nat -> nat) (Q : nat -> nat) : term99 P Q.
Proof. exact (@lem1261837 P Q (@lem1262155 P Q)). Qed.
Lemma lem1262157 (P : nat -> nat) (Q : nat -> nat) (N : nat) : term81 P Q N.
Proof. exact (@lem1262156 P Q N). Qed.
Lemma lem1262158 (N : nat) (P : nat -> nat) (Q : nat -> nat) : (term81 P Q N) = (term82 N P Q).
Proof. exact (eq_refl (term81 P Q N)). Qed.
Lemma lem1262159 (N : nat) (P : nat -> nat) (Q : nat -> nat) : term82 N P Q.
Proof. exact (EQ_MP (@lem1262158 N P Q) (@lem1262157 P Q N)). Qed.
Lemma lem1262160 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) : term116 N P Q B.
Proof. exact (@lem1262159 N P Q B). Qed.
Lemma lem1262161 (N : nat) (B : nat) (P : nat -> nat) (Q : nat -> nat) : (term116 N P Q B) = (term117 N B P Q).
Proof. exact (eq_refl (term116 N P Q B)). Qed.
Lemma lem1262162 (N : nat) (B : nat) (P : nat -> nat) (Q : nat -> nat) : term117 N B P Q.
Proof. exact (EQ_MP (@lem1262161 N B P Q) (@lem1262160 N P Q B)). Qed.
Lemma lem1262163 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : term54 P Q.
Proof. exact (@lem1262162 N B P Q (@lem1261772 N P Q B h1)). Qed.
Lemma lem1262164 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : (term58 N P Q B) = (term54 P Q).
Proof. exact (prop_ext (fun h2 : term58 N P Q B => @lem1262163 N P Q B h1) (fun h2 : term54 P Q => @lem1261772 N P Q B h1)). Qed.
Lemma lem1262165 (N : nat) (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term58 N P Q B) : term54 P Q.
Proof. exact (EQ_MP (@lem1262164 N P Q B h1) (@lem1261772 N P Q B h1)). Qed.
Lemma lem1262166 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term57 P Q B) : term54 P Q.
Proof. exact (ex_elim (@lem1261771 P Q B h1) (fun N : nat => fun h0 : term69 P Q B N => @lem1262165 N P Q B h0)). Qed.
Lemma lem1262167 (P : nat -> nat) (Q : nat -> nat) (h1 : term56 P Q) : term54 P Q.
Proof. exact (ex_elim (@lem1261770 P Q h1) (fun B : nat => fun h0 : term73 P Q B => @lem1262166 P Q B h0)). Qed.
Lemma lem1262168 (P : nat -> nat) (Q : nat -> nat) : term166 P Q.
Proof. exact (fun h0 : term56 P Q => @lem1262167 P Q h0). Qed.
Lemma lem1262169 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : (term55 P Q B) = (term56 P Q).
Proof. exact (prop_ext (fun h2 : term55 P Q B => @lem1261814 P Q B h1) (fun h2 : term56 P Q => @lem1261769 P Q B h1)). Qed.
Lemma lem1262170 (P : nat -> nat) (Q : nat -> nat) (B : nat) (h1 : term55 P Q B) : term56 P Q.
Proof. exact (EQ_MP (@lem1262169 P Q B h1) (@lem1261769 P Q B h1)). Qed.
Lemma lem1262171 (P : nat -> nat) (Q : nat -> nat) (h1 : term54 P Q) : term56 P Q.
Proof. exact (ex_elim (@lem1261768 P Q h1) (fun B : nat => fun h0 : term114 P Q B => @lem1262170 P Q B h0)). Qed.
Lemma lem1262172 (P : nat -> nat) (Q : nat -> nat) : term167 P Q.
Proof. exact (fun h0 : term54 P Q => @lem1262171 P Q h0). Qed.
Lemma lem1262173 (P : nat -> nat) (Q : nat -> nat) : term168 P Q.
Proof. exact (conj (@lem1262172 P Q) (@lem1262168 P Q)). Qed.
Lemma lem1262174 (P : nat -> nat) (Q : nat -> nat) : (term168 P Q) = ((term54 P Q) = (term56 P Q)).
Proof. exact (@lem32 (term54 P Q) (term56 P Q)). Qed.
Lemma lem1262175 (P : nat -> nat) (Q : nat -> nat) : (term54 P Q) = (term56 P Q).
Proof. exact (EQ_MP (@lem1262174 P Q) (@lem1262173 P Q)). Qed.
Lemma lem1262180 (P : nat -> nat) : term169 P.
Proof. exact (fun Q : nat -> nat => @lem1262175 P Q). Qed.
Lemma lem1262185 : term170.
Proof. exact (fun P : nat -> nat => @lem1262180 P). Qed.
