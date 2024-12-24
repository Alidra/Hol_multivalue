Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307066_term_abbrevs.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Require Import thm2306818_spec.
Lemma lem2307042 : term0.
Proof. exact (proj1 (@lem2306818)). Qed.
Lemma lem2307043 (m : nat) : term1 m.
Proof. exact (@lem2307042 m). Qed.
Lemma lem2307044 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2307045 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2307044 m) (@lem2307043 m)). Qed.
Lemma lem2307046 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2307045 m n). Qed.
Lemma lem2307047 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (Peano.gt m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2307048 (m : nat) (n : nat) : (term4 m n) = (Peano.gt m n).
Proof. exact (EQ_MP (@lem2307047 m n) (@lem2307046 m n)). Qed.
Lemma lem2307050 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307051 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307050 m). Qed.
Lemma lem2307052 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2307053 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307052) (@lem2307051 m)). Qed.
Lemma lem2307055 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307056 (m : nat) (n : nat) : (term4 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307053 m) (@lem2307055 n)). Qed.
Lemma lem2307058 (x : int) (y : int) : (term9 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2307059 (m : nat) (n : nat) : (term8 m n) = (term10 m n).
Proof. exact (@lem2307058 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307060 (m : nat) (n : nat) : (term4 m n) = (term10 m n).
Proof. exact (TRANS (@lem2307056 m n) (@lem2307059 m n)). Qed.
Lemma lem2307061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307062 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem2307061) (@lem2307060 m n)). Qed.
Lemma lem2307063 (m : nat) (n : nat) : (Peano.gt m n) = (Peano.gt m n).
Proof. exact (eq_refl (Peano.gt m n)). Qed.
Lemma lem2307064 (m : nat) (n : nat) : ((term4 m n) = (Peano.gt m n)) = ((term10 m n) = (Peano.gt m n)).
Proof. exact (MK_COMB (@lem2307062 m n) (@lem2307063 m n)). Qed.
Lemma lem2307065 (m : nat) (n : nat) : (term10 m n) = (Peano.gt m n).
Proof. exact (EQ_MP (@lem2307064 m n) (@lem2307048 m n)). Qed.
Lemma lem2307066 (m : nat) : term13 m.
Proof. exact (fun n : nat => @lem2307065 m n). Qed.
