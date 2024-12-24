Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_MIN_term_abbrevs.
Require Import REAL_OF_NUM_MIN_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307279 (m : nat) : term0 m.
Proof. exact (@lem1484027 m). Qed.
Lemma lem2307280 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307281 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307280 m) (@lem2307279 m)). Qed.
Lemma lem2307282 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307281 m n). Qed.
Lemma lem2307283 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307284 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2307283 m n) (@lem2307282 m n)). Qed.
Lemma lem2307286 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307287 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307286 m). Qed.
Lemma lem2307288 : real_min = real_min.
Proof. exact (eq_refl real_min). Qed.
Lemma lem2307289 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307288) (@lem2307287 m)). Qed.
Lemma lem2307291 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307292 (m : nat) (n : nat) : (term3 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307289 m) (@lem2307291 n)). Qed.
Lemma lem2307294 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2307295 (m : nat) (n : nat) : (term8 m n) = (term11 m n).
Proof. exact (@lem2307294 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307296 (m : nat) (n : nat) : (term3 m n) = (term11 m n).
Proof. exact (TRANS (@lem2307292 m n) (@lem2307295 m n)). Qed.
Lemma lem2307297 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307298 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2307297) (@lem2307296 m n)). Qed.
Lemma lem2307300 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307301 (m : nat) (n : nat) : (term4 m n) = (term14 m n).
Proof. exact (@lem2307300 (Nat.min m n)). Qed.
Lemma lem2307302 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term11 m n) = (term14 m n)).
Proof. exact (MK_COMB (@lem2307298 m n) (@lem2307301 m n)). Qed.
Lemma lem2307304 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307305 (m : nat) (n : nat) : ((term11 m n) = (term14 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (@lem2307304 (term15 m n) (term16 m n)). Qed.
Lemma lem2307306 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (TRANS (@lem2307302 m n) (@lem2307305 m n)). Qed.
Lemma lem2307307 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2307306 m n) (@lem2307284 m n)). Qed.
Lemma lem2307308 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem2307307 m n). Qed.
Lemma lem2307309 : term18.
Proof. exact (fun m : nat => @lem2307308 m). Qed.
