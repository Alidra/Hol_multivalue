Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term57 (x0 : real) (x1 : real) := ~ ((real_mul x1 (real_neg x0)) = (real_mul (real_neg x0) x1)).
Definition term29 (x0 : real -> Prop) := ~ (all x0).
Definition term101 := (~ False) -> False.
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))).
Definition term38 (x0 : real) := exists y0 : real, ~ ((real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))).
Definition term95 (x0 : real) (x1 : real) := (~ ((real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1)))) -> (real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1)).
Definition term74 (x0 : Prop) := ~ (~ x0).
Definition term53 (x0 : real) (x1 : real) := (~ ((real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1)))) -> (real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1)).
Definition term94 (x0 : real) (x1 : real) := ((real_mul x1 x0) = (real_mul x0 x1)) -> (real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1)).
Definition term46 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term84 (x0 : real) (x1 : real) := (~ ((real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1))) -> (real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term56 (x0 : real) (x1 : real) := (~ ((real_mul x1 (real_neg x0)) = (real_mul (real_neg x0) x1))) -> (real_mul x1 (real_neg x0)) = (real_mul (real_neg x0) x1).
Definition term26 (x0 : real) := fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term51 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((real_neg x0) = (real_neg x1)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term79 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term31 (x0 : real) := ~ (forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))).
Definition term17 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term48 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term34 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1).
Definition term67 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term54 (x0 : real) (x1 : real) := ~ ((real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1))).
Definition term89 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((real_neg x0) = (real_neg x1))).
Definition term19 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term55 (x0 : Prop) := (~ x0) -> x0.
Definition term98 (x0 : real) (x1 : real) := (((real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1)) /\ ((real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1)))) -> (real_mul (real_neg x0) x1) = (real_neg (real_mul x0 x1)).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term69 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term71 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term49 (x0 : real) (x1 : real) := (x0 = x1) -> (real_neg x0) = (real_neg x1).
Definition term21 (x0 : real) := fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term24 := forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)).
Definition term10 := forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term1 := forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term44 := exists y0 : real, exists y1 : real, ~ ((real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))).
Definition term86 (x0 : real) (x1 : real) := (~ ((real_mul x1 x0) = (real_mul x0 x1))) -> (real_mul x1 x0) = (real_mul x0 x1).
Definition term12 := (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term63 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term20 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term90 (x0 : real) (x1 : real) := @eq Prop (((real_neg x0) = (real_neg x1)) \/ (~ (x0 = x1))).
Definition term39 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul (real_neg y1) y2) = (real_neg (real_mul y1 y2))) y0).
Definition term32 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_neg x0) y1) = (real_neg (real_mul x0 y1))) y0).
Definition term42 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul (real_neg y1) y2) = (real_neg (real_mul y1 y2))) y0).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term8 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term60 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term3 := ~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))).
Definition term35 (x0 : real) (x1 : real) := ~ ((real_mul (real_neg x0) x1) = (real_neg (real_mul x0 x1))).
Definition term59 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term70 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term41 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0).
Definition term22 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term18 := fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term30 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term47 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term45 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term40 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term88 (x0 : real) (x1 : real) := ((real_neg x0) = (real_neg x1)) \/ (~ (x0 = x1)).
Definition term25 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term2 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> False.
Definition term78 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term97 (x0 : real) (x1 : real) := ((real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1)) /\ ((real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1))).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term76 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term27 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term91 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (real_neg x0) = (real_neg x1).
Definition term43 := fun y0 : real => exists y1 : real, ~ ((real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))).
Definition term16 (x0 : real) := fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0).
Definition term83 (x0 : real) (x1 : real) := (((real_mul x1 (real_neg x0)) = (real_neg (real_mul x1 x0))) /\ ((real_mul x1 (real_neg x0)) = (real_mul (real_neg x0) x1))) -> (real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1).
Definition term81 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term72 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term100 (x0 : real) (x1 : real) := ((real_mul (real_neg x0) x1) = (real_neg (real_mul x0 x1))) -> False.
Definition term77 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term13 := (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term50 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term37 (x0 : real) := fun y0 : real => ~ ((real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))).
Definition term36 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_neg x0) y1) = (real_neg (real_mul x0 y1))) y0).
Definition term82 (x0 : real) (x1 : real) := ((real_mul x1 (real_neg x0)) = (real_neg (real_mul x1 x0))) /\ ((real_mul x1 (real_neg x0)) = (real_mul (real_neg x0) x1)).
Definition term85 (x0 : real) (x1 : real) := ~ ((real_neg (real_mul x1 x0)) = (real_mul (real_neg x0) x1)).
Definition term99 (x0 : real) (x1 : real) := (~ ((real_mul (real_neg x0) x1) = (real_neg (real_mul x0 x1)))) -> (real_mul (real_neg x0) x1) = (real_neg (real_mul x0 x1)).
Definition term80 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term87 (x0 : real) (x1 : real) := ~ ((real_mul x1 x0) = (real_mul x0 x1)).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term75 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term61 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term96 (x0 : real) (x1 : real) := ~ ((real_neg (real_mul x1 x0)) = (real_neg (real_mul x0 x1))).
Definition term4 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term93 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term14 := imp (~ (forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)))).
Definition term28 := fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)).
Definition term23 := fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)).
Definition term92 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
