Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
