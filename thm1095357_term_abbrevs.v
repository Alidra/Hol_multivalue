Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := @ε ((prod nat nat) -> (list a0) -> list a0) (fun y0 : type1320 a0 => forall y1 : prod nat nat, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = y3) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))).
