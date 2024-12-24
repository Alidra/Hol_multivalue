Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515916_term_abbrevs.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem515694 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem515695 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem515710 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem515695 n) (@lem515694 n)). Qed.
Lemma lem515711 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem515710 m). Qed.
Lemma lem515712 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem515713 (m : nat) : (term1 m) = (Nat.pow m).
Proof. exact (MK_COMB (@lem515712) (@lem515711 m)). Qed.
Lemma lem515715 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem515695 n) (@lem515694 n)). Qed.
Lemma lem515716 (m : nat) (n : nat) : (term2 m n) = (Nat.pow m n).
Proof. exact (MK_COMB (@lem515713 m) (@lem515715 n)). Qed.
Lemma lem515717 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515718 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem515717) (@lem515716 m n)). Qed.
Lemma lem515720 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem515695 n) (@lem515694 n)). Qed.
Lemma lem515721 (m : nat) (n : nat) : (term5 m n) = (Nat.pow m n).
Proof. exact (@lem515720 (Nat.pow m n)). Qed.
Lemma lem515722 (m : nat) (n : nat) : ((term2 m n) = (term5 m n)) = ((Nat.pow m n) = (Nat.pow m n)).
Proof. exact (MK_COMB (@lem515718 m n) (@lem515721 m n)). Qed.
Lemma lem515724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515725 (x : nat) : (x = x) = True.
Proof. exact (@lem515724 nat x). Qed.
Lemma lem515726 (m : nat) (n : nat) : ((Nat.pow m n) = (Nat.pow m n)) = True.
Proof. exact (@lem515725 (Nat.pow m n)). Qed.
Lemma lem515727 (m : nat) (n : nat) : ((term2 m n) = (term5 m n)) = True.
Proof. exact (TRANS (@lem515722 m n) (@lem515726 m n)). Qed.
Lemma lem515728 (m : nat) : (term6 m) = term7.
Proof. exact (fun_ext (fun n : nat => @lem515727 m n)). Qed.
Lemma lem515729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515730 (m : nat) : (term8 m) = term9.
Proof. exact (MK_COMB (@lem515729) (@lem515728 m)). Qed.
Lemma lem515732 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515733 (t : Prop) : (term11 t) = t.
Proof. exact (@lem515732 nat t). Qed.
Lemma lem515734 : term9 = True.
Proof. exact (@lem515733 True). Qed.
Lemma lem515735 (m : nat) : (term8 m) = True.
Proof. exact (TRANS (@lem515730 m) (@lem515734)). Qed.
Lemma lem515736 : term12 = term7.
Proof. exact (fun_ext (fun m : nat => @lem515735 m)). Qed.
Lemma lem515737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515738 : term13 = term9.
Proof. exact (MK_COMB (@lem515737) (@lem515736)). Qed.
Lemma lem515740 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515741 (t : Prop) : (term11 t) = t.
Proof. exact (@lem515740 nat t). Qed.
Lemma lem515742 : term9 = True.
Proof. exact (@lem515741 True). Qed.
Lemma lem515743 : term13 = True.
Proof. exact (TRANS (@lem515738) (@lem515742)). Qed.
Lemma lem515744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515745 : term14 = (and True).
Proof. exact (MK_COMB (@lem515744) (@lem515743)). Qed.
Lemma lem515828 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem515829 : term16 = term17.
Proof. exact (MK_COMB (@lem515745) (@lem515828)). Qed.
Lemma lem515831 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515832 : term17 = term15.
Proof. exact (@lem515831 term15). Qed.
Lemma lem515915 : term16 = term15.
Proof. exact (TRANS (@lem515829) (@lem515832)). Qed.
Lemma lem515916 : term15 = term16.
Proof. exact (SYM (@lem515915)). Qed.
