Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_GT_term_abbrevs.
Require Import REAL_OF_NUM_GT_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Lemma lem2307173 (m : nat) : term0 m.
Proof. exact (@lem1483793 m). Qed.
Lemma lem2307174 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307175 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307174 m) (@lem2307173 m)). Qed.
Lemma lem2307176 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307175 m n). Qed.
Lemma lem2307177 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.gt m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307178 (m : nat) (n : nat) : (term3 m n) = (Peano.gt m n).
Proof. exact (EQ_MP (@lem2307177 m n) (@lem2307176 m n)). Qed.
Lemma lem2307180 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307181 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307180 m). Qed.
Lemma lem2307182 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2307183 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem2307182) (@lem2307181 m)). Qed.
Lemma lem2307185 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307186 (m : nat) (n : nat) : (term3 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2307183 m) (@lem2307185 n)). Qed.
Lemma lem2307188 (x : int) (y : int) : (term8 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2307189 (m : nat) (n : nat) : (term7 m n) = (term9 m n).
Proof. exact (@lem2307188 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307190 (m : nat) (n : nat) : (term3 m n) = (term9 m n).
Proof. exact (TRANS (@lem2307186 m n) (@lem2307189 m n)). Qed.
Lemma lem2307191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307192 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem2307191) (@lem2307190 m n)). Qed.
Lemma lem2307193 (m : nat) (n : nat) : (Peano.gt m n) = (Peano.gt m n).
Proof. exact (eq_refl (Peano.gt m n)). Qed.
Lemma lem2307194 (m : nat) (n : nat) : ((term3 m n) = (Peano.gt m n)) = ((term9 m n) = (Peano.gt m n)).
Proof. exact (MK_COMB (@lem2307192 m n) (@lem2307193 m n)). Qed.
Lemma lem2307195 (m : nat) (n : nat) : (term9 m n) = (Peano.gt m n).
Proof. exact (EQ_MP (@lem2307194 m n) (@lem2307178 m n)). Qed.
Lemma lem2307196 (m : nat) : term12 m.
Proof. exact (fun n : nat => @lem2307195 m n). Qed.
Lemma lem2307197 : term13.
Proof. exact (fun m : nat => @lem2307196 m). Qed.
