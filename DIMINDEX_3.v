Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_3_term_abbrevs.
Require Import thm7948705_spec.
Require Import thm7948708_spec.
Require Import thm7948709_spec.
Lemma lem7952342 (n : nat) : ((@dimindex unit (@UNIV unit)) = n) = ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = (BIT1 n)).
Proof. exact (@lem7948709 unit n). Qed.
Lemma lem7952343 : ((@dimindex unit (@UNIV unit)) = (BIT1 0)) = ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term0).
Proof. exact (@lem7952342 (BIT1 0)). Qed.
Lemma lem7952344 : (@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term0.
Proof. exact (EQ_MP (@lem7952343) (@lem7948708)). Qed.
Lemma lem7952345 (s : type1347) (n : nat) : ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = n) = ((@dimindex (tybit1 unit) s) = (NUMERAL n)).
Proof. exact (@lem7948705 (tybit1 unit) s n). Qed.
Lemma lem7952346 : ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term0) = ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term1).
Proof. exact (@lem7952345 (@UNIV (tybit1 unit)) term0). Qed.
Lemma lem7952347 : (@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term1.
Proof. exact (EQ_MP (@lem7952346) (@lem7952344)). Qed.
Lemma lem7952348 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7952349 : term2 = term3.
Proof. exact (MK_COMB (@lem7952348) (@lem7952347)). Qed.
Lemma lem7952350 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem7952351 : ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem7952349) (@lem7952350)). Qed.
Lemma lem7952352 : (term1 = term1) = ((@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term1).
Proof. exact (SYM (@lem7952351)). Qed.
Lemma lem7952353 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem7952354 : (@dimindex (tybit1 unit) (@UNIV (tybit1 unit))) = term1.
Proof. exact (EQ_MP (@lem7952352) (@lem7952353)). Qed.
