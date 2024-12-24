Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1964708 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (sqrt (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) n)) = (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (Nat.div n (NUMERAL (BIT0 (BIT1 0))))).
