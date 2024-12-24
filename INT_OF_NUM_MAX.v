Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_MAX_term_abbrevs.
Require Import REAL_OF_NUM_MAX_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307248 (m : nat) : term0 m.
Proof. exact (@lem1483910 m). Qed.
Lemma lem2307249 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307250 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307249 m) (@lem2307248 m)). Qed.
Lemma lem2307251 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307250 m n). Qed.
Lemma lem2307252 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307253 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2307252 m n) (@lem2307251 m n)). Qed.
Lemma lem2307255 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307256 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307255 m). Qed.
Lemma lem2307257 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2307258 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307257) (@lem2307256 m)). Qed.
Lemma lem2307260 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307261 (m : nat) (n : nat) : (term3 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307258 m) (@lem2307260 n)). Qed.
Lemma lem2307263 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2307264 (m : nat) (n : nat) : (term8 m n) = (term11 m n).
Proof. exact (@lem2307263 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307265 (m : nat) (n : nat) : (term3 m n) = (term11 m n).
Proof. exact (TRANS (@lem2307261 m n) (@lem2307264 m n)). Qed.
Lemma lem2307266 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307267 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2307266) (@lem2307265 m n)). Qed.
Lemma lem2307269 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307270 (m : nat) (n : nat) : (term4 m n) = (term14 m n).
Proof. exact (@lem2307269 (Nat.max m n)). Qed.
Lemma lem2307271 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term11 m n) = (term14 m n)).
Proof. exact (MK_COMB (@lem2307267 m n) (@lem2307270 m n)). Qed.
Lemma lem2307273 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307274 (m : nat) (n : nat) : ((term11 m n) = (term14 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (@lem2307273 (term15 m n) (term16 m n)). Qed.
Lemma lem2307275 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (TRANS (@lem2307271 m n) (@lem2307274 m n)). Qed.
Lemma lem2307276 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2307275 m n) (@lem2307253 m n)). Qed.
Lemma lem2307277 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem2307276 m n). Qed.
Lemma lem2307278 : term18.
Proof. exact (fun m : nat => @lem2307277 m). Qed.
