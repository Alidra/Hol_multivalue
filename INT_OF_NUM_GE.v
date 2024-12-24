Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_GE_term_abbrevs.
Require Import REAL_OF_NUM_GE_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299930_spec.
Require Import thm2299931_spec.
Lemma lem2307148 (m : nat) : term0 m.
Proof. exact (@lem1483730 m). Qed.
Lemma lem2307149 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307150 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307149 m) (@lem2307148 m)). Qed.
Lemma lem2307151 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307150 m n). Qed.
Lemma lem2307152 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.ge m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307153 (m : nat) (n : nat) : (term3 m n) = (Peano.ge m n).
Proof. exact (EQ_MP (@lem2307152 m n) (@lem2307151 m n)). Qed.
Lemma lem2307155 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307156 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307155 m). Qed.
Lemma lem2307157 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2307158 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem2307157) (@lem2307156 m)). Qed.
Lemma lem2307160 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307161 (m : nat) (n : nat) : (term3 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2307158 m) (@lem2307160 n)). Qed.
Lemma lem2307163 (x : int) (y : int) : (term8 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2307164 (m : nat) (n : nat) : (term7 m n) = (term9 m n).
Proof. exact (@lem2307163 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307165 (m : nat) (n : nat) : (term3 m n) = (term9 m n).
Proof. exact (TRANS (@lem2307161 m n) (@lem2307164 m n)). Qed.
Lemma lem2307166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307167 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem2307166) (@lem2307165 m n)). Qed.
Lemma lem2307168 (m : nat) (n : nat) : (Peano.ge m n) = (Peano.ge m n).
Proof. exact (eq_refl (Peano.ge m n)). Qed.
Lemma lem2307169 (m : nat) (n : nat) : ((term3 m n) = (Peano.ge m n)) = ((term9 m n) = (Peano.ge m n)).
Proof. exact (MK_COMB (@lem2307167 m n) (@lem2307168 m n)). Qed.
Lemma lem2307170 (m : nat) (n : nat) : (term9 m n) = (Peano.ge m n).
Proof. exact (EQ_MP (@lem2307169 m n) (@lem2307153 m n)). Qed.
Lemma lem2307171 (m : nat) : term12 m.
Proof. exact (fun n : nat => @lem2307170 m n). Qed.
Lemma lem2307172 : term13.
Proof. exact (fun m : nat => @lem2307171 m). Qed.
