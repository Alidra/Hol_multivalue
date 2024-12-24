Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_LE_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_ADD_spec.
Require Import LE_REFL_spec.
Require Import MOD_ZERO_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem210693 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem210694 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem210695 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem210694 m) (@lem210693 m)). Qed.
Lemma lem210696 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem210695 m n). Qed.
Lemma lem210697 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem210698 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem210697 m n) (@lem210696 m n)). Qed.
Lemma lem210699 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem210701 (m : nat) : term4 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem210702 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem210703 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem210702 m) (@lem210701 m)). Qed.
Lemma lem210704 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem210703 m n). Qed.
Lemma lem210705 (n : nat) (m : nat) : (term6 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem210707 (n : nat) : term7 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem210708 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem210709 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem210708 n) (@lem210707 n)). Qed.
Lemma lem210711 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem210712 (n : nat) : term10 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem210713 (n : nat) : (term10 n) = (Peano.le n n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem210714 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem210713 n) (@lem210712 n)). Qed.
Lemma lem210715 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem210717 (n : nat) : term11 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem210718 (n : nat) : (term11 n) = ((term12 n) = n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem210723 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem210724 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem210725 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term12 m).
Proof. exact (MK_COMB (@lem210724 m) (@lem210723 n h1)). Qed.
Lemma lem210727 (n : nat) : (term12 n) = n.
Proof. exact (EQ_MP (@lem210718 n) (@lem210717 n)). Qed.
Lemma lem210728 (m : nat) : (term12 m) = m.
Proof. exact (@lem210727 m). Qed.
Lemma lem210729 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem210725 m n h1) (@lem210728 m)). Qed.
Lemma lem210730 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem210731 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term13 m n) = (Peano.le m).
Proof. exact (MK_COMB (@lem210730) (@lem210729 m n h1)). Qed.
Lemma lem210732 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem210733 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term14 n m) = (Peano.le m m).
Proof. exact (MK_COMB (@lem210731 m n h1) (@lem210732 m)). Qed.
Lemma lem210735 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem210715 n) (@lem210714 n)). Qed.
Lemma lem210736 (m : nat) : (Peano.le m m) = True.
Proof. exact (@lem210735 m). Qed.
Lemma lem210737 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term14 n m) = True.
Proof. exact (TRANS (@lem210733 m n h1) (@lem210736 m)). Qed.
Lemma lem210738 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term14 n m).
Proof. exact (SYM (@lem210737 m n h1)). Qed.
Lemma lem210739 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term14 n m.
Proof. exact (EQ_MP (@lem210738 m n h1) (@lem0)). Qed.
Lemma lem210765 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem210766 (m : nat) (h1 : term15) : term16 m.
Proof. exact (@lem210765 h1 m). Qed.
Lemma lem210767 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem210768 (m : nat) (h1 : term15) : term17 m.
Proof. exact (EQ_MP (@lem210767 m) (@lem210766 m h1)). Qed.
Lemma lem210769 (m : nat) (n : nat) (h1 : term15) : term18 m n.
Proof. exact (@lem210768 m h1 n). Qed.
Lemma lem210770 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem210771 (m : nat) (n : nat) (h1 : term15) : term19 m n.
Proof. exact (EQ_MP (@lem210770 m n) (@lem210769 m n h1)). Qed.
Lemma lem210772 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem210773 (m : nat) (n : nat) (h1 : term15) (h2 : term9 n) : term20 m n.
Proof. exact (@lem210771 m n h1 (@lem210772 n h2)). Qed.
Lemma lem210774 (n : nat) (h1 : term15) (h2 : term9 n) : term21 n.
Proof. exact (fun m : nat => @lem210773 m n h1 h2). Qed.
Lemma lem210775 (n : nat) (h1 : term15) : term22 n.
Proof. exact (fun h0 : term9 n => @lem210774 n h1 h0). Qed.
Lemma lem210776 (h1 : term15) : term23.
Proof. exact (fun n : nat => @lem210775 n h1). Qed.
Lemma lem210777 : term24.
Proof. exact (fun h0 : term15 => @lem210776 h0). Qed.
Lemma lem210778 : term23.
Proof. exact (@lem210777 (@lem157261)). Qed.
Lemma lem210779 (n : nat) : term25 n.
Proof. exact (@lem210778 n). Qed.
Lemma lem210780 (n : nat) : (term25 n) = (term22 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem210783 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem210780 n) (@lem210779 n)). Qed.
Lemma lem210784 (n : nat) (h1 : term9 n) : term21 n.
Proof. exact (@lem210783 n (@lem210711 n h1)). Qed.
Lemma lem210785 (m : nat) (n : nat) (h1 : term9 n) : term26 n m.
Proof. exact (@lem210784 n h1 m). Qed.
Lemma lem210786 (m : nat) (n : nat) : (term26 n m) = (term20 m n).
Proof. exact (eq_refl (term26 n m)). Qed.
Lemma lem210787 (m : nat) (n : nat) (h1 : term9 n) : term20 m n.
Proof. exact (EQ_MP (@lem210786 m n) (@lem210785 m n h1)). Qed.
Lemma lem210793 (m : nat) (n : nat) (h1 : term9 n) : m = (term27 m n).
Proof. exact (proj1 (@lem210787 m n h1)). Qed.
Lemma lem210794 (m : nat) (n : nat) : (term13 m n) = (term13 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem210795 (m : nat) (n : nat) (h1 : term9 n) : (term14 n m) = (term28 m n).
Proof. exact (MK_COMB (@lem210794 m n) (@lem210793 m n h1)). Qed.
Lemma lem210796 (m : nat) (n : nat) (h1 : term9 n) : (term28 m n) = (term14 n m).
Proof. exact (SYM (@lem210795 m n h1)). Qed.
Lemma lem210798 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem210705 n m) (@lem210704 m n)). Qed.
Lemma lem210799 (m : nat) (n : nat) : (term27 m n) = (term29 m n).
Proof. exact (@lem210798 (Nat.modulo m n) (term30 m n)). Qed.
Lemma lem210800 (m : nat) (n : nat) : (term13 m n) = (term13 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem210801 (m : nat) (n : nat) : (term28 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem210800 m n) (@lem210799 m n)). Qed.
Lemma lem210802 (m : nat) (n : nat) : (term31 m n) = (term28 m n).
Proof. exact (SYM (@lem210801 m n)). Qed.
Lemma lem210804 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem210699 m n) (@lem210698 m n)). Qed.
Lemma lem210805 (m : nat) (n : nat) : (term31 m n) = True.
Proof. exact (@lem210804 (Nat.modulo m n) (term30 m n)). Qed.
Lemma lem210806 (m : nat) (n : nat) : True = (term31 m n).
Proof. exact (SYM (@lem210805 m n)). Qed.
Lemma lem210807 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem210806 m n) (@lem0)). Qed.
Lemma lem210808 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem210802 m n) (@lem210807 m n)). Qed.
Lemma lem210810 (m : nat) (n : nat) (h1 : term9 n) : term14 n m.
Proof. exact (EQ_MP (@lem210796 m n h1) (@lem210808 m n)). Qed.
Lemma lem210811 (n : nat) (m : nat) : term14 n m.
Proof. exact (or_elim (@lem210709 n) (fun h0 : n = (NUMERAL 0) => @lem210739 m n h0) (fun h0 : term9 n => @lem210810 m n h0)). Qed.
Lemma lem210816 (m : nat) : term32 m.
Proof. exact (fun n : nat => @lem210811 n m). Qed.
Lemma lem210821 : term33.
Proof. exact (fun m : nat => @lem210816 m). Qed.
