Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
