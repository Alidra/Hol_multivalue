Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_SUB_CASES_term_abbrevs.
Require Import REAL_OF_NUM_SUB_CASES_spec.
Require Import thm2299672_spec.
Require Import thm2299871_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307445 (m : nat) : term0 m.
Proof. exact (@lem1485709 m). Qed.
Lemma lem2307446 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307447 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307446 m) (@lem2307445 m)). Qed.
Lemma lem2307448 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307447 m n). Qed.
Lemma lem2307449 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307450 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem2307449 n m) (@lem2307448 m n)). Qed.
Lemma lem2307452 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307453 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307452 m). Qed.
Lemma lem2307454 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2307455 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307454) (@lem2307453 m)). Qed.
Lemma lem2307457 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307458 (m : nat) (n : nat) : (term3 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307455 m) (@lem2307457 n)). Qed.
Lemma lem2307460 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2307461 (m : nat) (n : nat) : (term8 m n) = (term11 m n).
Proof. exact (@lem2307460 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307462 (m : nat) (n : nat) : (term3 m n) = (term11 m n).
Proof. exact (TRANS (@lem2307458 m n) (@lem2307461 m n)). Qed.
Lemma lem2307463 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307464 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2307463) (@lem2307462 m n)). Qed.
Lemma lem2307466 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307467 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (@lem2307466 (Nat.sub m n)). Qed.
Lemma lem2307468 (n : nat) (m : nat) : (term16 n m) = (term16 n m).
Proof. exact (eq_refl (term16 n m)). Qed.
Lemma lem2307469 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem2307468 n m) (@lem2307467 m n)). Qed.
Lemma lem2307471 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307472 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (@lem2307471 (Nat.sub n m)). Qed.
Lemma lem2307473 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2307474 (n : nat) (m : nat) : (term19 n m) = (term20 n m).
Proof. exact (MK_COMB (@lem2307473) (@lem2307472 n m)). Qed.
Lemma lem2307476 (x : int) : (term21 x) = (term22 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2307477 (n : nat) (m : nat) : (term20 n m) = (term23 n m).
Proof. exact (@lem2307476 (term24 n m)). Qed.
Lemma lem2307478 (n : nat) (m : nat) : (term19 n m) = (term23 n m).
Proof. exact (TRANS (@lem2307474 n m) (@lem2307477 n m)). Qed.
Lemma lem2307479 (n : nat) (m : nat) : (term4 n m) = (term25 n m).
Proof. exact (MK_COMB (@lem2307469 m n) (@lem2307478 n m)). Qed.
Lemma lem2307481 (b : Prop) (x : int) (y : int) : (term26 b x y) = (term27 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2307482 (n : nat) (m : nat) : (term25 n m) = (term28 n m).
Proof. exact (@lem2307481 (Peano.le n m) (term24 m n) (term29 n m)). Qed.
Lemma lem2307483 (n : nat) (m : nat) : (term4 n m) = (term28 n m).
Proof. exact (TRANS (@lem2307479 n m) (@lem2307482 n m)). Qed.
Lemma lem2307484 (n : nat) (m : nat) : ((term3 m n) = (term4 n m)) = ((term11 m n) = (term28 n m)).
Proof. exact (MK_COMB (@lem2307464 m n) (@lem2307483 n m)). Qed.
Lemma lem2307486 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307487 (n : nat) (m : nat) : ((term11 m n) = (term28 n m)) = ((term30 m n) = (term31 n m)).
Proof. exact (@lem2307486 (term30 m n) (term31 n m)). Qed.
Lemma lem2307488 (n : nat) (m : nat) : ((term3 m n) = (term4 n m)) = ((term30 m n) = (term31 n m)).
Proof. exact (TRANS (@lem2307484 n m) (@lem2307487 n m)). Qed.
Lemma lem2307489 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (EQ_MP (@lem2307488 n m) (@lem2307450 n m)). Qed.
Lemma lem2307490 (m : nat) : term32 m.
Proof. exact (fun n : nat => @lem2307489 n m). Qed.
Lemma lem2307491 : term33.
Proof. exact (fun m : nat => @lem2307490 m). Qed.
