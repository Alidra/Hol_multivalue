Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307039_term_abbrevs.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2306819_spec.
Lemma lem2307015 : term0.
Proof. exact (proj1 (@lem2306819)). Qed.
Lemma lem2307016 (m : nat) : term1 m.
Proof. exact (@lem2307015 m). Qed.
Lemma lem2307017 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2307018 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2307017 m) (@lem2307016 m)). Qed.
Lemma lem2307019 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2307018 m n). Qed.
Lemma lem2307020 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2307021 (m : nat) (n : nat) : (term4 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2307020 m n) (@lem2307019 m n)). Qed.
Lemma lem2307023 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307024 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307023 m). Qed.
Lemma lem2307025 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307026 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307025) (@lem2307024 m)). Qed.
Lemma lem2307028 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307029 (m : nat) (n : nat) : (term4 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307026 m) (@lem2307028 n)). Qed.
Lemma lem2307031 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307032 (m : nat) (n : nat) : (term8 m n) = (term10 m n).
Proof. exact (@lem2307031 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307033 (m : nat) (n : nat) : (term4 m n) = (term10 m n).
Proof. exact (TRANS (@lem2307029 m n) (@lem2307032 m n)). Qed.
Lemma lem2307034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307035 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem2307034) (@lem2307033 m n)). Qed.
Lemma lem2307036 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem2307037 (m : nat) (n : nat) : ((term4 m n) = (Peano.le m n)) = ((term10 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem2307035 m n) (@lem2307036 m n)). Qed.
Lemma lem2307038 (m : nat) (n : nat) : (term10 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2307037 m n) (@lem2307021 m n)). Qed.
Lemma lem2307039 (m : nat) : term13 m.
Proof. exact (fun n : nat => @lem2307038 m n). Qed.
