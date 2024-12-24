Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))).
