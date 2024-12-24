Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_ADD_term_abbrevs.
Require Import REAL_POW_ADD_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307741 (x : int) : term0 x.
Proof. exact (@lem1596102 (real_of_int x)). Qed.
Lemma lem2307742 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307743 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2307742 x) (@lem2307741 x)). Qed.
Lemma lem2307744 (x : int) (m : nat) : term2 x m.
Proof. exact (@lem2307743 x m). Qed.
Lemma lem2307745 (m : nat) (x : int) : (term2 x m) = (term3 m x).
Proof. exact (eq_refl (term2 x m)). Qed.
Lemma lem2307746 (m : nat) (x : int) : term3 m x.
Proof. exact (EQ_MP (@lem2307745 m x) (@lem2307744 x m)). Qed.
Lemma lem2307747 (m : nat) (x : int) (n : nat) : term4 m x n.
Proof. exact (@lem2307746 m x n). Qed.
Lemma lem2307748 (m : nat) (x : int) (n : nat) : (term4 m x n) = ((term5 x m n) = (term6 m x n)).
Proof. exact (eq_refl (term4 m x n)). Qed.
Lemma lem2307749 (m : nat) (x : int) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (EQ_MP (@lem2307748 m x n) (@lem2307747 m x n)). Qed.
Lemma lem2307751 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307752 (x : int) (m : nat) (n : nat) : (term5 x m n) = (term9 x m n).
Proof. exact (@lem2307751 x (Nat.add m n)). Qed.
Lemma lem2307753 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307754 (x : int) (m : nat) (n : nat) : (term10 x m n) = (term11 x m n).
Proof. exact (MK_COMB (@lem2307753) (@lem2307752 x m n)). Qed.
Lemma lem2307756 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307757 (x : int) (m : nat) : (term7 x m) = (term8 x m).
Proof. exact (@lem2307756 x m). Qed.
Lemma lem2307758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2307759 (x : int) (m : nat) : (term12 x m) = (term13 x m).
Proof. exact (MK_COMB (@lem2307758) (@lem2307757 x m)). Qed.
Lemma lem2307761 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307762 (m : nat) (x : int) (n : nat) : (term6 m x n) = (term14 m x n).
Proof. exact (MK_COMB (@lem2307759 x m) (@lem2307761 x n)). Qed.
Lemma lem2307764 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2307765 (m : nat) (x : int) (n : nat) : (term14 m x n) = (term17 m x n).
Proof. exact (@lem2307764 (int_pow x m) (int_pow x n)). Qed.
Lemma lem2307766 (m : nat) (x : int) (n : nat) : (term6 m x n) = (term17 m x n).
Proof. exact (TRANS (@lem2307762 m x n) (@lem2307765 m x n)). Qed.
Lemma lem2307767 (m : nat) (x : int) (n : nat) : ((term5 x m n) = (term6 m x n)) = ((term9 x m n) = (term17 m x n)).
Proof. exact (MK_COMB (@lem2307754 x m n) (@lem2307766 m x n)). Qed.
Lemma lem2307769 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307770 (m : nat) (x : int) (n : nat) : ((term9 x m n) = (term17 m x n)) = ((term18 x m n) = (term19 m x n)).
Proof. exact (@lem2307769 (term18 x m n) (term19 m x n)). Qed.
Lemma lem2307771 (m : nat) (x : int) (n : nat) : ((term5 x m n) = (term6 m x n)) = ((term18 x m n) = (term19 m x n)).
Proof. exact (TRANS (@lem2307767 m x n) (@lem2307770 m x n)). Qed.
Lemma lem2307772 (m : nat) (x : int) (n : nat) : (term18 x m n) = (term19 m x n).
Proof. exact (EQ_MP (@lem2307771 m x n) (@lem2307749 m x n)). Qed.
Lemma lem2307773 (m : nat) (x : int) : term20 m x.
Proof. exact (fun n : nat => @lem2307772 m x n). Qed.
Lemma lem2307774 (x : int) : term21 x.
Proof. exact (fun m : nat => @lem2307773 m x). Qed.
Lemma lem2307775 : term22.
Proof. exact (fun x : int => @lem2307774 x). Qed.
