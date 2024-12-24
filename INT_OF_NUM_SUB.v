Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_SUB_term_abbrevs.
Require Import REAL_OF_NUM_SUB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307412 (m : nat) : term0 m.
Proof. exact (@lem1485045 m). Qed.
Lemma lem2307413 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307414 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307413 m) (@lem2307412 m)). Qed.
Lemma lem2307415 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307414 m n). Qed.
Lemma lem2307416 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307417 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem2307416 n m) (@lem2307415 m n)). Qed.
Lemma lem2307419 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307420 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2307421 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem2307420) (@lem2307419 n)). Qed.
Lemma lem2307423 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307424 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307423 m). Qed.
Lemma lem2307425 (n : nat) (m : nat) : (term7 n m) = (term8 n m).
Proof. exact (MK_COMB (@lem2307421 n) (@lem2307424 m)). Qed.
Lemma lem2307427 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2307428 (n : nat) (m : nat) : (term8 n m) = (term11 n m).
Proof. exact (@lem2307427 (int_of_num n) (int_of_num m)). Qed.
Lemma lem2307429 (n : nat) (m : nat) : (term7 n m) = (term11 n m).
Proof. exact (TRANS (@lem2307425 n m) (@lem2307428 n m)). Qed.
Lemma lem2307430 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307431 (n : nat) (m : nat) : (term12 n m) = (term13 n m).
Proof. exact (MK_COMB (@lem2307430) (@lem2307429 n m)). Qed.
Lemma lem2307433 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307434 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (@lem2307433 (Nat.sub n m)). Qed.
Lemma lem2307435 (n : nat) (m : nat) : ((term7 n m) = (term14 n m)) = ((term11 n m) = (term15 n m)).
Proof. exact (MK_COMB (@lem2307431 n m) (@lem2307434 n m)). Qed.
Lemma lem2307437 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307438 (n : nat) (m : nat) : ((term11 n m) = (term15 n m)) = ((term16 n m) = (term17 n m)).
Proof. exact (@lem2307437 (term16 n m) (term17 n m)). Qed.
Lemma lem2307439 (n : nat) (m : nat) : ((term7 n m) = (term14 n m)) = ((term16 n m) = (term17 n m)).
Proof. exact (TRANS (@lem2307435 n m) (@lem2307438 n m)). Qed.
Lemma lem2307440 (m : nat) (n : nat) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2307441 (n : nat) (m : nat) : (term3 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem2307440 m n) (@lem2307439 n m)). Qed.
Lemma lem2307442 (n : nat) (m : nat) : term19 n m.
Proof. exact (EQ_MP (@lem2307441 n m) (@lem2307417 n m)). Qed.
Lemma lem2307443 (m : nat) : term20 m.
Proof. exact (fun n : nat => @lem2307442 n m). Qed.
Lemma lem2307444 : term21.
Proof. exact (fun m : nat => @lem2307443 m). Qed.
