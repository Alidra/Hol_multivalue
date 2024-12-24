Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := @ε ((prod nat (prod nat (prod nat nat))) -> (a0 -> a1 -> Prop) -> (list a0) -> (list a1) -> Prop) (fun y0 : type1285 a0 a1 => forall y1 : type1673, (forall y2 : type1413 a0 a1, forall y3 : list a1, (y0 y1 y2 (@nil a0) y3) = (y3 = (@nil a1))) /\ (forall y2 : a0, forall y3 : type1413 a0 a1, forall y4 : list a0, forall y5 : list a1, (y0 y1 y3 (@cons a0 y2 y4) y5) = (@COND Prop (y5 = (@nil a1)) False ((y3 y2 (@hd a1 y5)) /\ (y0 y1 y3 y4 (@tl a1 y5)))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))).
