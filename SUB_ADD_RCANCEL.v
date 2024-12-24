Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_ADD_RCANCEL_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import SUB_ADD_LCANCEL_spec.
Lemma lem136700 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem136701 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136702 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136701 m) (@lem136700 m)). Qed.
Lemma lem136703 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136702 m n). Qed.
Lemma lem136704 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136721 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136704 n m) (@lem136703 m n)). Qed.
Lemma lem136722 (p : nat) (m : nat) : (Nat.add m p) = (Nat.add p m).
Proof. exact (@lem136721 p m). Qed.
Lemma lem136723 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136724 (p : nat) (m : nat) : (term3 m p) = (term3 p m).
Proof. exact (MK_COMB (@lem136723) (@lem136722 p m)). Qed.
Lemma lem136726 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136704 n m) (@lem136703 m n)). Qed.
Lemma lem136727 (p : nat) (n : nat) : (Nat.add n p) = (Nat.add p n).
Proof. exact (@lem136726 p n). Qed.
Lemma lem136728 (m : nat) (p : nat) (n : nat) : (term4 m n p) = (term5 m p n).
Proof. exact (MK_COMB (@lem136724 p m) (@lem136727 p n)). Qed.
Lemma lem136729 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136730 (m : nat) (p : nat) (n : nat) : (term6 m n p) = (term7 m p n).
Proof. exact (MK_COMB (@lem136729) (@lem136728 m p n)). Qed.
Lemma lem136731 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (eq_refl (Nat.sub m n)). Qed.
Lemma lem136732 (p : nat) (m : nat) (n : nat) : ((term4 m n p) = (Nat.sub m n)) = ((term5 m p n) = (Nat.sub m n)).
Proof. exact (MK_COMB (@lem136730 m p n) (@lem136731 m n)). Qed.
Lemma lem136733 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (fun_ext (fun p : nat => @lem136732 p m n)). Qed.
Lemma lem136734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136735 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem136734) (@lem136733 m n)). Qed.
Lemma lem136736 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem136735 m n)). Qed.
Lemma lem136737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136738 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem136737) (@lem136736 m)). Qed.
Lemma lem136739 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem136738 m)). Qed.
Lemma lem136740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136741 : term18 = term19.
Proof. exact (MK_COMB (@lem136740) (@lem136739)). Qed.
Lemma lem136742 : term19 = term18.
Proof. exact (SYM (@lem136741)). Qed.
Lemma lem136743 (m : nat) : term20 m.
Proof. exact (@lem136699 m). Qed.
Lemma lem136744 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem136745 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem136744 m) (@lem136743 m)). Qed.
Lemma lem136746 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem136745 m n). Qed.
Lemma lem136747 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem136748 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem136747 m n) (@lem136746 m n)). Qed.
Lemma lem136749 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem136748 m n p). Qed.
Lemma lem136750 (m : nat) (n : nat) (p : nat) : (term24 m n p) = ((term5 n m p) = (Nat.sub n p)).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem136753 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (Nat.sub n p).
Proof. exact (EQ_MP (@lem136750 m n p) (@lem136749 m n p)). Qed.
Lemma lem136754 (p : nat) (m : nat) (n : nat) : (term5 m p n) = (Nat.sub m n).
Proof. exact (@lem136753 p m n). Qed.
Lemma lem136759 (m : nat) (n : nat) : term11 m n.
Proof. exact (fun p : nat => @lem136754 p m n). Qed.
Lemma lem136764 (m : nat) : term15 m.
Proof. exact (fun n : nat => @lem136759 m n). Qed.
Lemma lem136769 : term19.
Proof. exact (fun m : nat => @lem136764 m). Qed.
Lemma lem136770 : term18.
Proof. exact (EQ_MP (@lem136742) (@lem136769)). Qed.
