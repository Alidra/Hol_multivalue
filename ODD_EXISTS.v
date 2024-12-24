Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_EXISTS_term_abbrevs.
Require Import EVEN_EXISTS_LEMMA_spec.
Require Import NOT_EVEN_spec.
Require Import ODD_DOUBLE_spec.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem128829 (n : nat) : term0 n.
Proof. exact (@lem128433 n). Qed.
Lemma lem128830 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem128831 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem128830 n) (@lem128829 n)). Qed.
Lemma lem128832 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem128834 (n : nat) : term2 n.
Proof. exact (@lem128768 n). Qed.
Lemma lem128835 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem128836 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem128835 n) (@lem128834 n)). Qed.
Lemma lem128837 (n : nat) : term4 n.
Proof. exact (proj2 (@lem128836 n)). Qed.
Lemma lem128838 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem128839 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem128840 (n : nat) (h1 : term5 n) (h2 : term4 n) : term6 n.
Proof. exact (@lem128838 n h2 (@lem128839 n h1)). Qed.
Lemma lem128841 (n : nat) (h1 : term5 n) : term7 n.
Proof. exact (fun h0 : term4 n => @lem128840 n h1 h0). Qed.
Lemma lem128842 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem128843 (n : nat) (h1 : term5 n) (h2 : term4 n) : term6 n.
Proof. exact (@lem128841 n h1 (@lem128842 n h2)). Qed.
Lemma lem128844 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (fun h0 : term5 n => @lem128843 n h0 h1). Qed.
Lemma lem128845 (n : nat) : term8 n.
Proof. exact (fun h0 : term4 n => @lem128844 n h0). Qed.
Lemma lem128847 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem128848 (n : nat) (h1 : term6 n) : term6 n.
Proof. exact (h1). Qed.
Lemma lem128850 (n : nat) : term4 n.
Proof. exact (@lem128845 n (@lem128837 n)). Qed.
Lemma lem128851 (n : nat) : term9 n.
Proof. exact (@lem124715 n). Qed.
Lemma lem128852 (n : nat) : (term9 n) = ((term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem128854 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem128857 (n : nat) : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (EQ_MP (@lem128852 n) (@lem128851 n)). Qed.
Lemma lem128859 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem128854 n) (@lem128847 n h1)). Qed.
Lemma lem128860 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term5 n) = True.
Proof. exact (TRANS (@lem128857 n) (@lem128859 n h1)). Qed.
Lemma lem128861 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : True = (term5 n).
Proof. exact (SYM (@lem128860 n h1)). Qed.
Lemma lem128862 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : term5 n.
Proof. exact (EQ_MP (@lem128861 n h1) (@lem0)). Qed.
Lemma lem128863 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : term6 n.
Proof. exact (@lem128850 n (@lem128862 n h1)). Qed.
Lemma lem128864 (n : nat) (m : nat) (h1 : n = (term10 m)) : n = (term10 m).
Proof. exact (h1). Qed.
Lemma lem128865 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem128866 (n : nat) (m : nat) (h1 : n = (term10 m)) : (term12 n) = (term13 m).
Proof. exact (MK_COMB (@lem128865) (@lem128864 n m h1)). Qed.
Lemma lem128867 (m : nat) : (term13 m) = (term1 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem128868 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem128869 (n : nat) (m : nat) : ((term12 n) = (term13 m)) = ((term12 n) = (term1 m)).
Proof. exact (MK_COMB (@lem128868 n) (@lem128867 m)). Qed.
Lemma lem128870 (n : nat) : (term12 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem128871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem128872 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem128871) (@lem128870 n)). Qed.
Lemma lem128873 (m : nat) : (term1 m) = (term1 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem128874 (n : nat) (m : nat) : ((term12 n) = (term1 m)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term1 m)).
Proof. exact (MK_COMB (@lem128872 n) (@lem128873 m)). Qed.
Lemma lem128875 (n : nat) (m : nat) : ((term12 n) = (term13 m)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term1 m)).
Proof. exact (TRANS (@lem128869 n m) (@lem128874 n m)). Qed.
Lemma lem128876 (n : nat) (m : nat) (h1 : n = (term10 m)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term1 m).
Proof. exact (EQ_MP (@lem128875 n m) (@lem128866 n m h1)). Qed.
Lemma lem128877 (n : nat) (m : nat) (h1 : n = (term10 m)) : (term1 m) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem128876 n m h1)). Qed.
Lemma lem128879 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem128832 n) (@lem128831 n)). Qed.
Lemma lem128880 (m : nat) : (term1 m) = True.
Proof. exact (@lem128879 m). Qed.
Lemma lem128881 (m : nat) : True = (term1 m).
Proof. exact (SYM (@lem128880 m)). Qed.
Lemma lem128882 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem128881 m) (@lem0)). Qed.
Lemma lem128883 (n : nat) (m : nat) (h1 : n = (term10 m)) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem128877 n m h1) (@lem128882 m)). Qed.
Lemma lem128884 (n : nat) (h1 : term6 n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (ex_elim (@lem128848 n h1) (fun m : nat => fun h0 : term16 n m => @lem128883 n m h0)). Qed.
Lemma lem128885 (n : nat) : term17 n.
Proof. exact (fun h0 : term6 n => @lem128884 n h0). Qed.
Lemma lem128886 (n : nat) : term18 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem128863 n h0). Qed.
Lemma lem128887 (n : nat) : term19 n.
Proof. exact (conj (@lem128886 n) (@lem128885 n)). Qed.
Lemma lem128888 (n : nat) : (term19 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term6 n)).
Proof. exact (@lem32 (Coq.Arith.PeanoNat.Nat.Odd n) (term6 n)). Qed.
Lemma lem128889 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term6 n).
Proof. exact (EQ_MP (@lem128888 n) (@lem128887 n)). Qed.
Lemma lem128894 : term20.
Proof. exact (fun n : nat => @lem128889 n). Qed.
