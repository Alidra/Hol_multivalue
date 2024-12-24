Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_2_term_abbrevs.
Require Import thm7948705_spec.
Require Import thm7948707_spec.
Require Import thm7948708_spec.
Lemma lem7952329 (n : nat) : ((@dimindex unit (@UNIV unit)) = n) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = (BIT0 n)).
Proof. exact (@lem7948707 unit n). Qed.
Lemma lem7952330 : ((@dimindex unit (@UNIV unit)) = (BIT1 0)) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0).
Proof. exact (@lem7952329 (BIT1 0)). Qed.
Lemma lem7952331 : (@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0.
Proof. exact (EQ_MP (@lem7952330) (@lem7948708)). Qed.
Lemma lem7952332 (s : type1341) (n : nat) : ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = n) = ((@dimindex (tybit0 unit) s) = (NUMERAL n)).
Proof. exact (@lem7948705 (tybit0 unit) s n). Qed.
Lemma lem7952333 : ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term1).
Proof. exact (@lem7952332 (@UNIV (tybit0 unit)) term0). Qed.
Lemma lem7952334 : (@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term1.
Proof. exact (EQ_MP (@lem7952333) (@lem7952331)). Qed.
Lemma lem7952335 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7952336 : term2 = term3.
Proof. exact (MK_COMB (@lem7952335) (@lem7952334)). Qed.
Lemma lem7952337 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem7952338 : ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem7952336) (@lem7952337)). Qed.
Lemma lem7952339 : (term1 = term1) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term1).
Proof. exact (SYM (@lem7952338)). Qed.
Lemma lem7952340 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem7952341 : (@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term1.
Proof. exact (EQ_MP (@lem7952339) (@lem7952340)). Qed.
