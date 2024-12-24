Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_EQ_term_abbrevs.
Require Import thm1340231_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307123 (m : nat) : term0 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2307124 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307125 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307124 m) (@lem2307123 m)). Qed.
Lemma lem2307126 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307125 m n). Qed.
Lemma lem2307127 (m : nat) (n : nat) : (term2 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307128 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2307127 m n) (@lem2307126 m n)). Qed.
Lemma lem2307130 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307131 (m : nat) : (real_of_num m) = (term3 m).
Proof. exact (@lem2307130 m). Qed.
Lemma lem2307132 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307133 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem2307132) (@lem2307131 m)). Qed.
Lemma lem2307135 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307136 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term3 m) = (term3 n)).
Proof. exact (MK_COMB (@lem2307133 m) (@lem2307135 n)). Qed.
Lemma lem2307138 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307139 (m : nat) (n : nat) : ((term3 m) = (term3 n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (@lem2307138 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307140 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (TRANS (@lem2307136 m n) (@lem2307139 m n)). Qed.
Lemma lem2307141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307142 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2307141) (@lem2307140 m n)). Qed.
Lemma lem2307143 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem2307144 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (MK_COMB (@lem2307142 m n) (@lem2307143 m n)). Qed.
Lemma lem2307145 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2307144 m n) (@lem2307128 m n)). Qed.
Lemma lem2307146 (m : nat) : term8 m.
Proof. exact (fun n : nat => @lem2307145 m n). Qed.
Lemma lem2307147 : term9.
Proof. exact (fun m : nat => @lem2307146 m). Qed.
