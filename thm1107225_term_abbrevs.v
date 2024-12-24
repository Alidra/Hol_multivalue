Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a1 -> (list (prod a1 a0)) -> a0) (fun y0 : type1276 a0 a1 => forall y1 : type1672, forall y2 : prod a1 a0, forall y3 : a1, forall y4 : type1641 a0 a1, (y0 y1 y3 (@cons (prod a1 a0) y2 y4)) = (@COND a0 ((@fst a1 a0 y2) = y3) (@snd a1 a0 y2) (y0 y1 y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))).
