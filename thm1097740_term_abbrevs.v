Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := @ε ((prod nat (prod nat nat)) -> (a0 -> a1) -> (list a0) -> list a1) (fun y0 : type1297 a0 a1 => forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
