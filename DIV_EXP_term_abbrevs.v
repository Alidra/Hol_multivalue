Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
