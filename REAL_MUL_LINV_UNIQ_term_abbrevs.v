Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term51 (x0 : real) (x1 : real) := (x1 = (real_inv x0)) -> (real_inv x0) = x1.
Definition term37 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ((real_mul x1 x0) = y0) -> (real_inv x0) = x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : real) := @eq real (real_inv x0).
Definition term29 := @eq real (real_inv (real_of_num (NUMERAL 0))).
Definition term3 := real_of_num (NUMERAL 0).
Definition term33 (x0 : real) (x1 : real) := fun y0 : real => ((real_mul x1 x0) = y0) -> (real_inv x0) = x1.
Definition term45 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term6 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term48 (x0 : real) (x1 : real) := (x0 = (real_inv x1)) \/ False.
Definition term9 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term7 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term35 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 x1) = y0) -> (real_inv x1) = x0) (real_mul (real_inv x1) x1).
Definition term49 (x0 : real) (x1 : real) := imp ((real_mul x0 x1) = (real_mul (real_inv x1) x1)).
Definition term27 := real_inv (real_of_num (NUMERAL 0)).
Definition term18 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term15 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term2 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x1 x0) = y0) -> (real_inv x0) = x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term31 (x0 : real) := False -> (real_inv (real_of_num (NUMERAL 0))) = x0.
Definition term11 := forall y0 : nat, (0 = (BIT1 y0)) = False.
Definition term53 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0.
Definition term40 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul x0 y1) = (real_mul y0 y1)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term0 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term1 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term26 (x0 : real) (x1 : real) := imp ((real_mul x0 x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : nat) := (fun y0 : nat => (0 = (BIT1 y0)) = False) x0.
Definition term23 := @eq real (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term42 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul x0 y0) = (real_mul x1 y0)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term13 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term4 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term30 (x0 : real) (x1 : real) := ((real_mul x1 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term47 (x0 : real) (x1 : real) := or (x0 = (real_inv x1)).
Definition term41 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_mul x0 y1) = (real_mul y0 y1)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0))))) x1.
Definition term52 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term46 (x0 : real) (x1 : real) := (x0 = (real_inv x1)) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_mul x1 y0)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0))))) x2.
Definition term24 := real_of_num (NUMERAL (BIT1 0)).
Definition term36 (x0 : real) (x1 : real) := ((real_mul x1 x0) = (real_mul (real_inv x0) x0)) -> (real_inv x0) = x1.
Definition term44 (x0 : real) (x1 : real) (x2 : real) := (x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))).
Definition term21 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term32 (x0 : real) := real_mul (real_inv x0) x0.
Definition term8 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term39 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y2) = (real_mul y1 y2)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0))))) x0.
Definition term10 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term25 := NUMERAL (BIT1 0).
Definition term50 (x0 : real) (x1 : real) := imp (x0 = (real_inv x1)).
Definition term38 (x0 : real) (x1 : real) := @eq Prop (((real_mul x1 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1).
