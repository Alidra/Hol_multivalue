Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (a0 -> a1 -> a1) -> a1 -> (a0 -> Prop) -> a1 -> nat -> Prop) (fun y0 : type1266 a0 a1 => forall y1 : type1671, (forall y2 : type1411 a0 a1, forall y3 : a0 -> Prop, forall y4 : a1, forall y5 : a1, (y0 y1 y2 y5 y3 y4 (NUMERAL 0)) = ((y3 = (@EMPTY a0)) /\ (y4 = y5))) /\ (forall y2 : a1, forall y3 : a0 -> Prop, forall y4 : nat, forall y5 : a1, forall y6 : type1411 a0 a1, (y0 y1 y6 y2 y3 y5 (S y4)) = (exists y7 : a0, exists y8 : a1, (@IN a0 y7 y3) /\ ((y0 y1 y6 y2 (@DELETE a0 y3 y7) y8 y4) /\ (y5 = (y6 y7 y8)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).