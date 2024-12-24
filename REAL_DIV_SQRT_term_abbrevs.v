Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term100 := (((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0)))))) /\ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))))) -> (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))).
Definition term3 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term105 := (~ ((real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))))) -> (real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))).
Definition term72 := ~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0)))))).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> ((real_div x0 y0) = x1) = (x0 = (real_mul x1 y0))) x2.
Definition term118 := (~ False) -> False.
Definition term32 := imp (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))).
Definition term40 (x0 : real) := (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term58 := fun y0 : real => ~ ((real_div y0 (sqrt y0)) = (sqrt y0)).
Definition term99 := ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0)))))) /\ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))).
Definition term4 := forall y0 : real, (real_mul y0 y0) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term91 (x0 : Prop) := ~ (~ x0).
Definition term11 := real_of_num (NUMERAL 0).
Definition term127 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ((real_div x0 y0) = x1) = (x0 = (real_mul x1 y0)).
Definition term46 := forall y0 : real, ((real_of_num (NUMERAL 0)) = y0) -> (~ ((real_div y0 (sqrt y0)) = (sqrt y0))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, forall y2 : real, (real_div y1 y2) = (real_mul y1 (real_inv y2))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term45 := forall y0 : real, ((real_of_num (NUMERAL 0)) = y0) -> (~ ((real_div y0 (sqrt y0)) = (sqrt y0))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, forall y2 : real, (real_div y1 y2) = (real_mul y1 (real_inv y2))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term59 (x0 : real) := (fun y0 : real => ~ ((real_div y0 (sqrt y0)) = (sqrt y0))) x0.
Definition term90 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term62 (x0 : real) := @eq Prop ((fun y0 : real => ~ ((real_div y0 (sqrt y0)) = (sqrt y0))) x0).
Definition term54 := forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) x0.
Definition term12 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term67 := (~ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_of_num (NUMERAL 0)).
Definition term22 (x0 : Prop) := (~ x0) -> False.
Definition term96 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term139 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term101 := (~ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))))) -> (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))).
Definition term73 := (~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))))) -> (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))).
Definition term84 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term26 (x0 : real) := (((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term41 (x0 : real) := imp ((real_of_num (NUMERAL 0)) = x0).
Definition term108 := (~ ((sqrt (real_of_num (NUMERAL 0))) = (sqrt (real_of_num (NUMERAL 0))))) -> (sqrt (real_of_num (NUMERAL 0))) = (sqrt (real_of_num (NUMERAL 0))).
Definition term34 := (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term69 (x0 : Prop) := (~ x0) -> x0.
Definition term23 (x0 : real) := (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> False.
Definition term57 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term10 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0).
Definition term14 (x0 : real) := real_div x0 (sqrt x0).
Definition term86 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term88 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term125 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> ((real_div x0 y1) = y0) = (x0 = (real_mul y0 y1)).
Definition term51 := forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term70 := real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))).
Definition term83 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term137 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_le x0 x1.
Definition term15 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_div x0 (sqrt x0)) = (sqrt x0).
Definition term80 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term131 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)) = True.
Definition term64 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term68 := ~ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_of_num (NUMERAL 0))).
Definition term50 := fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term63 (x0 : real) := @eq Prop (~ ((real_div x0 (sqrt x0)) = (sqrt x0))).
Definition term38 (x0 : real) := imp (~ ((real_div x0 (sqrt x0)) = (sqrt x0))).
Definition term102 := ~ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))).
Definition term74 := ~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))).
Definition term30 := ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term77 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term110 := ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((sqrt (real_of_num (NUMERAL 0))) = (sqrt (real_of_num (NUMERAL 0)))).
Definition term76 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term87 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term20 := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)) -> (real_div y0 (sqrt y0)) = (sqrt y0).
Definition term116 := (~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (sqrt (real_of_num (NUMERAL 0))))) -> (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (sqrt (real_of_num (NUMERAL 0))).
Definition term107 := (~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> (sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term66 := real_inv (sqrt (real_of_num (NUMERAL 0))).
Definition term114 := ((real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))) /\ ((real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0)))).
Definition term48 (x0 : real) := fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term140 (x0 : real) (x1 : real) := (real_lt x0 x1) -> (real_le x0 x1) = True.
Definition term18 := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)) -> (real_div y0 (sqrt y0)) = (sqrt y0).
Definition term33 := (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term53 := fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) x0.
Definition term56 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) x0.
Definition term135 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_le x0 y0.
Definition term27 (x0 : real) := ((((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term9 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term103 := ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))).
Definition term28 (x0 : real) := ((((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term115 := (((real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))) /\ ((real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0))))) -> (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (sqrt (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)).
Definition term136 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) -> real_le x0 y0) x1.
Definition term95 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term120 (x0 : real) := (fun y0 : real => (real_mul y0 y0) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term55 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term81 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term79 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term111 := (((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((sqrt (real_of_num (NUMERAL 0))) = (sqrt (real_of_num (NUMERAL 0))))) -> (real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0))).
Definition term49 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term126 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> ((real_div x0 y1) = y0) = (x0 = (real_mul y0 y1))) x1.
Definition term31 := sqrt (real_of_num (NUMERAL 0)).
Definition term93 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term121 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) x0.
Definition term1 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term65 := real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0)))).
Definition term21 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term16 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)) -> (real_div x0 (sqrt x0)) = (sqrt x0).
Definition term141 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) x0) = True.
Definition term130 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)) -> ((real_div x0 (sqrt x0)) = (sqrt x0)) = (x0 = (real_mul (sqrt x0) (sqrt x0))).
Definition term119 (x0 : real) := (fun y0 : real => ((real_of_num (NUMERAL 0)) = y0) -> (~ ((real_div y0 (sqrt y0)) = (sqrt y0))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, forall y2 : real, (real_div y1 y2) = (real_mul y1 (real_inv y2))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) x0.
Definition term133 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term19 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_div y0 (sqrt y0)) = (sqrt y0).
Definition term117 := ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (sqrt (real_of_num (NUMERAL 0)))) -> False.
Definition term109 := ~ ((sqrt (real_of_num (NUMERAL 0))) = (sqrt (real_of_num (NUMERAL 0)))).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term89 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term8 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0))) x1.
Definition term94 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term42 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) -> (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term52 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term61 := ~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (sqrt (real_of_num (NUMERAL 0)))).
Definition term122 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term132 (x0 : real) := real_mul (sqrt x0) (sqrt x0).
Definition term35 := imp (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))).
Definition term24 (x0 : real) := ~ ((real_div x0 (sqrt x0)) = (sqrt x0)).
Definition term39 (x0 : real) := (~ ((real_div x0 (sqrt x0)) = (sqrt x0))) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term2 := fun y0 : real => (real_mul y0 y0) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term17 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_div y0 (sqrt y0)) = (sqrt y0).
Definition term37 := (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term97 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term60 := (fun y0 : real => ~ ((real_div y0 (sqrt y0)) = (sqrt y0))) (real_of_num (NUMERAL 0)).
Definition term47 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term71 := (~ ((real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))))) -> (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))).
Definition term6 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term29 := ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term104 := (((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_of_num (NUMERAL 0)) (real_inv (sqrt (real_of_num (NUMERAL 0))))) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))))) -> (real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0)))).
Definition term75 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x2) -> ((real_div x0 x2) = x1) = (x0 = (real_mul x1 x2)).
Definition term123 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term92 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term78 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term124 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> ((real_div y0 y2) = y1) = (y0 = (real_mul y1 y2))) x0.
Definition term36 := (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term106 := ~ ((real_of_num (NUMERAL 0)) = (real_div (real_of_num (NUMERAL 0)) (sqrt (real_of_num (NUMERAL 0))))).
Definition term112 := (~ ((real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0))))) -> (real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0))).
Definition term44 := fun y0 : real => ((real_of_num (NUMERAL 0)) = y0) -> (~ ((real_div y0 (sqrt y0)) = (sqrt y0))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, forall y2 : real, (real_div y1 y2) = (real_mul y1 (real_inv y2))) -> ~ ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term43 := fun y0 : real => ((real_of_num (NUMERAL 0)) = y0) -> (~ ((real_div y0 (sqrt y0)) = (sqrt y0))) -> (forall y1 : real, (real_mul (real_of_num (NUMERAL 0)) y1) = (real_of_num (NUMERAL 0))) -> (forall y1 : real, forall y2 : real, (real_div y1 y2) = (real_mul y1 (real_inv y2))) -> ((sqrt (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term113 := ~ ((real_of_num (NUMERAL 0)) = (sqrt (real_of_num (NUMERAL 0)))).
