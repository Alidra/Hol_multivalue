Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, exists y2 : type1606, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((y0 y1 y3 y4) = (NUMERAL 0)) /\ ((y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (y0 y1 y3 y4) y4) (y2 y3 y4))) /\ (Peano.lt (y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
