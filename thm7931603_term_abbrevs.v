Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : type1345 a0 => @HAS_SIZE (tybit0 a0) y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term6 (a0 : Type') := @eq Prop (@HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))).
Definition term5 (a0 : Type') := @HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term3 (a0 : Type') := @HAS_SIZE (tybit0 a0) (@IMAGE (finite_sum a0 a0) (tybit0 a0) (@mktybit0 a0) (@UNIV (finite_sum a0 a0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term1 (a0 : Type') := (fun y0 : type1345 a0 => @HAS_SIZE (tybit0 a0) y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) (@UNIV (tybit0 a0)).
Definition term4 (a0 : Type') := @eq Prop ((fun y0 : type1345 a0 => @HAS_SIZE (tybit0 a0) y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) (@UNIV (tybit0 a0))).
Definition term2 (a0 : Type') := (fun y0 : type1345 a0 => @HAS_SIZE (tybit0 a0) y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) (@IMAGE (finite_sum a0 a0) (tybit0 a0) (@mktybit0 a0) (@UNIV (finite_sum a0 a0))).