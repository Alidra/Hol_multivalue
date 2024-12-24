Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := @ε ((prod nat (prod nat (prod nat nat))) -> (a1 -> a2 -> a0) -> (list a1) -> (list a2) -> list a0) (fun y0 : type1286 a0 a1 a2 => forall y1 : type1673, (forall y2 : type1475 a0 a1 a2, forall y3 : list a2, (y0 y1 y2 (@nil a1) y3) = (@nil a0)) /\ (forall y2 : a1, forall y3 : type1475 a0 a1 a2, forall y4 : list a1, forall y5 : list a2, (y0 y1 y3 (@cons a1 y2 y4) y5) = (@cons a0 (y3 y2 (@hd a2 y5)) (y0 y1 y3 y4 (@tl a2 y5))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))).
