Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := @eq real (real_of_num (@CARD a0 x0)).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := real_mul (real_of_num (@CARD a0 x0)) x1.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := real_mul (real_of_num (@CARD a0 x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term28 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (real_of_num (@CARD a0 y0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0)))).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term30 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (real_of_num (@CARD a0 y0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0)))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = True.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := ((@FINITE a0 x0) -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = True) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = ((@FINITE a0 x0) -> True).
Definition term3 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((@FINITE a0 x0) = (@FINITE a0 x0)) -> ((@FINITE a0 x0) -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = x1) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = ((@FINITE a0 x0) -> x1).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((@FINITE a0 x0) = x1) -> (x1 -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0))))) = y0) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0))))) = (x1 -> y0)) x2.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := @sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (@CARD a0 x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0)) x1.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((@FINITE a0 x0) -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = x1) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = ((@FINITE a0 x0) -> x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := @sum a0 x0 (fun y0 : a0 => x1).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : Prop, ((@FINITE a0 x0) = x1) -> (x1 -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0))))) = y0) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y1 : a0 => real_of_num (NUMERAL (BIT1 0))))) = (x1 -> y0).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := real_of_num (@CARD a0 x0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@FINITE a0 x0) = y0) -> (y0 -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y2 : a0 => real_of_num (NUMERAL (BIT1 0))))) = y1) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y2 : a0 => real_of_num (NUMERAL (BIT1 0))))) = (y0 -> y1).
Definition term10 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := (@FINITE a0 x0) -> (@sum a0 x0 (fun y0 : a0 => x1)) = (real_mul (real_of_num (@CARD a0 x0)) x1).
Definition term21 := real_of_num (NUMERAL (BIT1 0)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@FINITE a0 x0) = y0) -> (y0 -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y2 : a0 => real_of_num (NUMERAL (BIT1 0))))) = y1) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y2 : a0 => real_of_num (NUMERAL (BIT1 0))))) = (y0 -> y1)) x1.
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := ((@FINITE a0 x0) = x1) -> (x1 -> ((real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = x2) -> ((@FINITE a0 x0) -> (real_of_num (@CARD a0 x0)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL (BIT1 0))))) = (x1 -> x2).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> True.
Definition term2 (a0 : Type') (x0 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => y0)) = (real_mul (real_of_num (@CARD a0 y1)) y0)) x0.
Definition term31 (a0 : Type') := forall y0 : a0 -> Prop, True.
