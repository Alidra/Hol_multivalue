Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_EXISTS_term_abbrevs.
Require Import EVEN_DOUBLE_spec.
Require Import EVEN_EXISTS_LEMMA_spec.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem128769 (n : nat) : term0 n.
Proof. exact (@lem128384 n). Qed.
Lemma lem128770 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem128771 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem128770 n) (@lem128769 n)). Qed.
Lemma lem128772 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem128774 (n : nat) : term2 n.
Proof. exact (@lem128768 n). Qed.
Lemma lem128775 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem128776 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem128775 n) (@lem128774 n)). Qed.
Lemma lem128777 (n : nat) : term4 n.
Proof. exact (proj1 (@lem128776 n)). Qed.
Lemma lem128778 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem128779 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128780 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term4 n) : term5 n.
Proof. exact (@lem128778 n h2 (@lem128779 n h1)). Qed.
Lemma lem128781 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term6 n.
Proof. exact (fun h0 : term4 n => @lem128780 n h1 h0). Qed.
Lemma lem128782 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem128783 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term4 n) : term5 n.
Proof. exact (@lem128781 n h1 (@lem128782 n h2)). Qed.
Lemma lem128784 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem128783 n h0 h1). Qed.
Lemma lem128785 (n : nat) : term7 n.
Proof. exact (fun h0 : term4 n => @lem128784 n h0). Qed.
Lemma lem128787 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128788 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem128790 (n : nat) : term4 n.
Proof. exact (@lem128785 n (@lem128777 n)). Qed.
Lemma lem128791 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128794 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem128791 n) (@lem128787 n h1)). Qed.
Lemma lem128795 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : True = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem128794 n h1)). Qed.
Lemma lem128796 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem128795 n h1) (@lem0)). Qed.
Lemma lem128797 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term5 n.
Proof. exact (@lem128790 n (@lem128796 n h1)). Qed.
Lemma lem128798 (n : nat) (m : nat) (h1 : n = (term8 m)) : n = (term8 m).
Proof. exact (h1). Qed.
Lemma lem128799 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem128800 (n : nat) (m : nat) (h1 : n = (term8 m)) : (term10 n) = (term11 m).
Proof. exact (MK_COMB (@lem128799) (@lem128798 n m h1)). Qed.
Lemma lem128801 (m : nat) : (term11 m) = (term1 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem128802 (n : nat) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem128803 (n : nat) (m : nat) : ((term10 n) = (term11 m)) = ((term10 n) = (term1 m)).
Proof. exact (MK_COMB (@lem128802 n) (@lem128801 m)). Qed.
Lemma lem128804 (n : nat) : (term10 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem128805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem128806 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem128805) (@lem128804 n)). Qed.
Lemma lem128807 (m : nat) : (term1 m) = (term1 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem128808 (n : nat) (m : nat) : ((term10 n) = (term1 m)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term1 m)).
Proof. exact (MK_COMB (@lem128806 n) (@lem128807 m)). Qed.
Lemma lem128809 (n : nat) (m : nat) : ((term10 n) = (term11 m)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term1 m)).
Proof. exact (TRANS (@lem128803 n m) (@lem128808 n m)). Qed.
Lemma lem128810 (n : nat) (m : nat) (h1 : n = (term8 m)) : (Coq.Arith.PeanoNat.Nat.Even n) = (term1 m).
Proof. exact (EQ_MP (@lem128809 n m) (@lem128800 n m h1)). Qed.
Lemma lem128811 (n : nat) (m : nat) (h1 : n = (term8 m)) : (term1 m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem128810 n m h1)). Qed.
Lemma lem128813 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem128772 n) (@lem128771 n)). Qed.
Lemma lem128814 (m : nat) : (term1 m) = True.
Proof. exact (@lem128813 m). Qed.
Lemma lem128815 (m : nat) : True = (term1 m).
Proof. exact (SYM (@lem128814 m)). Qed.
Lemma lem128816 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem128815 m) (@lem0)). Qed.
Lemma lem128817 (n : nat) (m : nat) (h1 : n = (term8 m)) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem128811 n m h1) (@lem128816 m)). Qed.
Lemma lem128818 (n : nat) (h1 : term5 n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (ex_elim (@lem128788 n h1) (fun m : nat => fun h0 : term14 n m => @lem128817 n m h0)). Qed.
Lemma lem128819 (n : nat) : term15 n.
Proof. exact (fun h0 : term5 n => @lem128818 n h0). Qed.
Lemma lem128820 (n : nat) : term4 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem128797 n h0). Qed.
Lemma lem128821 (n : nat) : term16 n.
Proof. exact (conj (@lem128820 n) (@lem128819 n)). Qed.
Lemma lem128822 (n : nat) : (term16 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term5 n)).
Proof. exact (@lem32 (Coq.Arith.PeanoNat.Nat.Even n) (term5 n)). Qed.
Lemma lem128823 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term5 n).
Proof. exact (EQ_MP (@lem128822 n) (@lem128821 n)). Qed.
Lemma lem128828 : term17.
Proof. exact (fun n : nat => @lem128823 n). Qed.
