Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) := forall y0 : real, (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term84 (x0 : real) (x1 : real) := ((x0 = x1) -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = True) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = ((x0 = x1) -> True).
Definition term48 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term25 := real_of_num (NUMERAL 0).
Definition term49 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term10 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term9 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term13 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term11 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term46 (x0 : real) := False /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term83 (x0 : real) (x1 : real) := (x0 = x1) -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = True.
Definition term101 (x0 : real) (x1 : real) (x2 : Prop) := ((x0 = x1) -> (x0 = x1) = x2) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = ((x0 = x1) -> x2).
Definition term86 (x0 : real) (x1 : real) := (x0 = x1) -> True.
Definition term103 (x0 : real) (x1 : real) := ((x0 = x1) -> (x0 = x1) = True) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = ((x0 = x1) -> True).
Definition term54 := real_inv (real_of_num (NUMERAL 0)).
Definition term22 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term19 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term24 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := (x0 = x1) /\ True.
Definition term72 (x0 : real) (x1 : real) := ((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1.
Definition term85 (x0 : real) (x1 : real) := (x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term58 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0)) x1.
Definition term105 (x0 : real) (x1 : real) := (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) /\ ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term15 := forall y0 : nat, (0 = (BIT1 y0)) = False.
Definition term33 (x0 : real) (x1 : real) := @eq Prop ((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 := forall y0 : real, forall y1 : real, ((real_div y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) = ((y0 = y1) /\ ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0)))))).
Definition term8 := forall y0 : real, forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term7 := forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term73 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_div y0 y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term104 (x0 : real) (x1 : real) := ((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1.
Definition term27 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) (x1 : real) := @eq Prop ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term43 (x0 : real) := and ((real_of_num (NUMERAL 0)) = x0).
Definition term70 (x0 : real) (x1 : real) := (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (x0 = x1) = (x0 = x1)) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1).
Definition term39 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term59 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term50 (x0 : real) := True /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term5 := fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term16 (x0 : nat) := (fun y0 : nat => (0 = (BIT1 y0)) = False) x0.
Definition term2 (x0 : real) := fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term30 (x0 : real) (x1 : real) := @eq real (real_div x0 x1).
Definition term40 := @eq real (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term106 := ~ ((@el real) = (real_of_num (NUMERAL 0))).
Definition term107 (x0 : real) := forall y0 : real, ((real_div x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) = ((x0 = y0) /\ ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0)))))).
Definition term17 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term1 (x0 : real) := fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term97 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = x2) -> (x2 -> (x0 = x1) = y0) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = (x2 -> y0)) x3.
Definition term78 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 = x1) = x2) -> (x2 -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y0) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = (x2 -> y0)) x3.
Definition term65 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x2) -> (x2 -> (x0 = x1) = y0) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (x2 -> y0)) x3.
Definition term79 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := ((x0 = x1) = x2) -> (x2 -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x3) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = (x2 -> x3).
Definition term41 := @eq Prop ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 := fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term67 (x0 : real) (x1 : real) (x2 : Prop) := (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = ((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0))))) -> (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (x0 = x1) = x2) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> x2).
Definition term90 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_div y0 y1)) = y0) x0.
Definition term57 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1)) x0.
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term31 (x0 : real) (x1 : real) := @eq real (real_mul x0 (real_inv x1)).
Definition term74 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div x0 x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term96 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = x2) -> (x2 -> (x0 = x1) = y0) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = (x2 -> y0).
Definition term77 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, ((x0 = x1) = x2) -> (x2 -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y0) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = (x2 -> y0).
Definition term64 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x2) -> (x2 -> (x0 = x1) = y0) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (x2 -> y0).
Definition term60 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term51 (x0 : real) (x1 : real) := (x0 = x1) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term36 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term93 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_div x1 x0)) = x1.
Definition term26 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term3 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term38 := real_mul (real_of_num (NUMERAL 0)).
Definition term94 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = y0) -> (y0 -> (x0 = x1) = y1) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = (y0 -> y1).
Definition term75 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, ((x0 = x1) = y0) -> (y0 -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y1) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 -> y1).
Definition term62 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y0) -> (y0 -> (x0 = x1) = y1) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (y0 -> y1).
Definition term61 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term80 (x0 : real) (x1 : real) (x2 : Prop) := ((x0 = x1) = (x0 = x1)) -> ((x0 = x1) -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x2) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = ((x0 = x1) -> x2).
Definition term69 (x0 : real) (x1 : real) := ((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (x0 = x1) = (x0 = x1).
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term98 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = x2) -> (x2 -> (x0 = x1) = x3) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = (x2 -> x3).
Definition term66 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x2) -> (x2 -> (x0 = x1) = x3) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (x2 -> x3).
Definition term71 (x0 : real) (x1 : real) := ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1.
Definition term91 (x0 : real) := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0.
Definition term32 := real_of_num (NUMERAL (BIT1 0)).
Definition term102 (x0 : real) (x1 : real) := (x0 = x1) -> (x0 = x1) = True.
Definition term42 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term37 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term100 (x0 : real) (x1 : real) (x2 : Prop) := (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = (x0 = x1)) -> ((x0 = x1) -> (x0 = x1) = x2) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = ((x0 = x1) -> x2).
Definition term53 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term47 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) /\ False.
Definition term88 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term45 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term92 (x0 : real) (x1 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0) x1.
Definition term82 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term12 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term0 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term35 (x0 : real) (x1 : real) := (x0 = x1) /\ ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term89 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term68 (x0 : real) (x1 : real) (x2 : Prop) := (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (x0 = x1) = x2) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (((real_div x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> x2).
Definition term44 (x0 : real) := and (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term99 (x0 : real) (x1 : real) := @eq real (real_mul x1 (real_div x0 x1)).
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term81 (x0 : real) (x1 : real) (x2 : Prop) := ((x0 = x1) -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = x2) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = ((x0 = x1) -> x2).
Definition term95 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) = y0) -> (y0 -> (x0 = x1) = y1) -> (((real_mul x1 (real_div x0 x1)) = (real_mul x1 (real_of_num (NUMERAL (BIT1 0))))) -> x0 = x1) = (y0 -> y1)) x2.
Definition term76 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = x1) = y0) -> (y0 -> ((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y1) -> ((x0 = x1) -> (real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 -> y1)) x2.
Definition term63 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) = y0) -> (y0 -> (x0 = x1) = y1) -> (((real_mul x0 (real_inv x1)) = (real_of_num (NUMERAL (BIT1 0)))) -> x0 = x1) = (y0 -> y1)) x2.
Definition term87 (x0 : real) (x1 : real) := real_mul x1 (real_div x0 x1).
Definition term14 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term56 := NUMERAL (BIT1 0).
