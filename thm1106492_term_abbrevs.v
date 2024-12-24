Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (a0 -> Prop) -> (list a0) -> list a0) (fun y0 : type1267 a0 => forall y1 : type1671, (forall y2 : a0 -> Prop, (y0 y1 y2 (@nil a0)) = (@nil a0)) /\ (forall y2 : a0, forall y3 : a0 -> Prop, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = (@COND (list a0) (y3 y2) (@cons a0 y2 (y0 y1 y3 y4)) (y0 y1 y3 y4)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).
