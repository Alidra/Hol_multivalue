Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_4_term_abbrevs.
Require Import thm7948705_spec.
Require Import thm7948707_spec.
Require Import thm7948708_spec.
Lemma lem7952355 (n : nat) : ((@dimindex unit (@UNIV unit)) = n) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = (BIT0 n)).
Proof. exact (@lem7948707 unit n). Qed.
Lemma lem7952356 : ((@dimindex unit (@UNIV unit)) = (BIT1 0)) = ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0).
Proof. exact (@lem7952355 (BIT1 0)). Qed.
Lemma lem7952357 : (@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0.
Proof. exact (EQ_MP (@lem7952356) (@lem7948708)). Qed.
Lemma lem7952358 (n : nat) : ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = n) = ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = (BIT0 n)).
Proof. exact (@lem7948707 (tybit0 unit) n). Qed.
Lemma lem7952359 : ((@dimindex (tybit0 unit) (@UNIV (tybit0 unit))) = term0) = ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term1).
Proof. exact (@lem7952358 term0). Qed.
Lemma lem7952360 : (@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term1.
Proof. exact (EQ_MP (@lem7952359) (@lem7952357)). Qed.
Lemma lem7952361 (s : type1339) (n : nat) : ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = n) = ((@dimindex (tybit0 (tybit0 unit)) s) = (NUMERAL n)).
Proof. exact (@lem7948705 type1679 s n). Qed.
Lemma lem7952362 : ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term1) = ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term2).
Proof. exact (@lem7952361 (@UNIV (tybit0 (tybit0 unit))) term1). Qed.
Lemma lem7952363 : (@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term2.
Proof. exact (EQ_MP (@lem7952362) (@lem7952360)). Qed.
Lemma lem7952364 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7952365 : term3 = term4.
Proof. exact (MK_COMB (@lem7952364) (@lem7952363)). Qed.
Lemma lem7952366 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7952367 : ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem7952365) (@lem7952366)). Qed.
Lemma lem7952368 : (term2 = term2) = ((@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term2).
Proof. exact (SYM (@lem7952367)). Qed.
Lemma lem7952369 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7952370 : (@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))) = term2.
Proof. exact (EQ_MP (@lem7952368) (@lem7952369)). Qed.
