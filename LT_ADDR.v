Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ADDR_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import LT_ADD_spec.
Lemma lem100723 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem100724 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem100725 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem100724 m) (@lem100723 m)). Qed.
Lemma lem100726 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem100725 m n). Qed.
Lemma lem100727 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem100740 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem100727 n m) (@lem100726 m n)). Qed.
Lemma lem100741 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem100742 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (MK_COMB (@lem100741 n) (@lem100740 n m)). Qed.
Lemma lem100743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100744 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem100743) (@lem100742 n m)). Qed.
Lemma lem100745 (m : nat) : (term7 m) = (term7 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem100746 (n : nat) (m : nat) : ((term3 m n) = (term7 m)) = ((term4 n m) = (term7 m)).
Proof. exact (MK_COMB (@lem100744 n m) (@lem100745 m)). Qed.
Lemma lem100747 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem100746 n m)). Qed.
Lemma lem100748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100749 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem100748) (@lem100747 m)). Qed.
Lemma lem100750 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem100749 m)). Qed.
Lemma lem100751 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100752 : term14 = term15.
Proof. exact (MK_COMB (@lem100751) (@lem100750)). Qed.
Lemma lem100753 : term15 = term14.
Proof. exact (SYM (@lem100752)). Qed.
Lemma lem100754 (m : nat) : term16 m.
Proof. exact (@lem100722 m). Qed.
Lemma lem100755 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem100756 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem100755 m) (@lem100754 m)). Qed.
Lemma lem100757 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem100756 m n). Qed.
Lemma lem100758 (m : nat) (n : nat) : (term18 m n) = ((term4 m n) = (term7 n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem100761 (m : nat) (n : nat) : (term4 m n) = (term7 n).
Proof. exact (EQ_MP (@lem100758 m n) (@lem100757 m n)). Qed.
Lemma lem100762 (n : nat) (m : nat) : (term4 n m) = (term7 m).
Proof. exact (@lem100761 n m). Qed.
Lemma lem100767 (m : nat) : term11 m.
Proof. exact (fun n : nat => @lem100762 n m). Qed.
Lemma lem100772 : term15.
Proof. exact (fun m : nat => @lem100767 m). Qed.
Lemma lem100773 : term14.
Proof. exact (EQ_MP (@lem100753) (@lem100772)). Qed.
