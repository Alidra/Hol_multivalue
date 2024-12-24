Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_SUC_term_abbrevs.
Require Import REAL_OF_NUM_SUC_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307492 (n : nat) : term0 n.
Proof. exact (@lem1484068 n). Qed.
Lemma lem2307493 (n : nat) : (term0 n) = ((term1 n) = (term2 n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307494 (n : nat) : (term1 n) = (term2 n).
Proof. exact (EQ_MP (@lem2307493 n) (@lem2307492 n)). Qed.
Lemma lem2307496 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307497 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2307498 (n : nat) : (term4 n) = (term5 n).
Proof. exact (MK_COMB (@lem2307497) (@lem2307496 n)). Qed.
Lemma lem2307500 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307501 : term6 = term7.
Proof. exact (@lem2307500 term8). Qed.
Lemma lem2307502 (n : nat) : (term1 n) = (term9 n).
Proof. exact (MK_COMB (@lem2307498 n) (@lem2307501)). Qed.
Lemma lem2307504 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2307505 (n : nat) : (term9 n) = (term12 n).
Proof. exact (@lem2307504 (int_of_num n) term13). Qed.
Lemma lem2307506 (n : nat) : (term1 n) = (term12 n).
Proof. exact (TRANS (@lem2307502 n) (@lem2307505 n)). Qed.
Lemma lem2307507 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307508 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem2307507) (@lem2307506 n)). Qed.
Lemma lem2307510 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307511 (n : nat) : (term2 n) = (term16 n).
Proof. exact (@lem2307510 (S n)). Qed.
Lemma lem2307512 (n : nat) : ((term1 n) = (term2 n)) = ((term12 n) = (term16 n)).
Proof. exact (MK_COMB (@lem2307508 n) (@lem2307511 n)). Qed.
Lemma lem2307514 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307515 (n : nat) : ((term12 n) = (term16 n)) = ((term17 n) = (term18 n)).
Proof. exact (@lem2307514 (term17 n) (term18 n)). Qed.
Lemma lem2307516 (n : nat) : ((term1 n) = (term2 n)) = ((term17 n) = (term18 n)).
Proof. exact (TRANS (@lem2307512 n) (@lem2307515 n)). Qed.
Lemma lem2307517 (n : nat) : (term17 n) = (term18 n).
Proof. exact (EQ_MP (@lem2307516 n) (@lem2307494 n)). Qed.
Lemma lem2307518 : term19.
Proof. exact (fun n : nat => @lem2307517 n). Qed.
