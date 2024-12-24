Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : real -> Prop) := ~ (all x0).
Definition term119 := (~ False) -> False.
Definition term48 := fun y0 : real => (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term61 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term81 (x0 : Prop) := ~ (~ x0).
Definition term41 (x0 : real) := or (((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term15 := (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term13 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term103 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term67 (x0 : real) := @eq Prop ((fun y0 : real => ~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term80 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (real_inv x0) = (real_inv x1).
Definition term8 := (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term107 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term3 := ~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term65 := (fun y0 : real => ~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : real) := ~ ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 := ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term79 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term17 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term74 (x0 : Prop) := (~ x0) -> x0.
Definition term63 := fun y0 : real => ~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term99 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term101 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term96 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term54 := exists y0 : real, (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term49 := exists y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term12 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term97 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term51 := or (exists y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0).
Definition term94 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term64 (x0 : real) := (fun y0 : real => ~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term10 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term78 (x0 : real) (x1 : real) := @eq Prop (((real_inv x0) = (real_inv x1)) \/ (~ (x0 = x1))).
Definition term24 := exists y0 : real, ~ ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) = (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term4 := (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term85 (x0 : real) := ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term36 := fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term76 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term32 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term56 := (exists y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term20 (x0 : real) := ~ (((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))) = (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term91 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term28 := fun y0 : real => (((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term5 := ((~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term33 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term16 (x0 : real) := real_inv (real_inv x0).
Definition term100 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term118 (x0 : real) := (x0 = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term71 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((real_inv x0) = (real_inv x1)).
Definition term60 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term73 (x0 : real) := (~ ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_inv x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term47 := @eq Prop (exists y0 : real, (((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term46 := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0)).
Definition term114 := (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term77 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((real_inv x0) = (real_inv x1))).
Definition term50 := exists y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term2 := (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term106 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term117 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL (BIT1 0))))) -> x0 = (real_of_num (NUMERAL (BIT1 0))).
Definition term112 (x0 : real) := (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0)) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0.
Definition term88 (x0 : real) := (~ ((real_inv (real_inv x0)) = x0)) -> (real_inv (real_inv x0)) = x0.
Definition term21 (x0 : real) := (((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term95 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term93 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term69 (x0 : real) (x1 : real) := (x0 = x1) -> (real_inv x0) = (real_inv x1).
Definition term7 := (((~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> ((~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term115 (x0 : real) := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0) /\ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term104 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term66 := ~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 := fun y0 : real => ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term116 (x0 : real) := (((real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0) /\ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> x0 = (real_of_num (NUMERAL (BIT1 0))).
Definition term75 (x0 : real) (x1 : real) := ((real_inv x0) = (real_inv x1)) \/ (~ (x0 = x1)).
Definition term19 := fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term34 := exists y0 : real, ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term37 := fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : real) := (fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term44 (x0 : real) := ((fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0) \/ ((fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term43 (x0 : real) := (~ ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (x0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : real) := ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term86 (x0 : real) := (~ ((real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0)))))) -> (real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term113 (x0 : real) := ~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0).
Definition term89 (x0 : real) := ~ ((real_inv (real_inv x0)) = x0).
Definition term109 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term102 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term18 := real_of_num (NUMERAL (BIT1 0)).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term59 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term53 := fun y0 : real => (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term1 := forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term70 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term26 (x0 : real) := ~ ((fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term27 := fun y0 : real => ~ ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) = (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term55 := exists y0 : real, (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term29 := exists y0 : real, (((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term40 (x0 : real) := or ((fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0).
Definition term42 (x0 : real) := (fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term110 (x0 : real) := ((real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0))))) /\ ((real_inv (real_inv x0)) = x0).
Definition term68 (x0 : real) := @eq Prop (~ ((real_inv x0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term90 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term82 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term87 (x0 : real) := ~ ((real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0))))).
Definition term25 (x0 : real) := (fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term92 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term11 := imp ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 := or (exists y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term84 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term111 (x0 : real) := (((real_inv (real_inv x0)) = (real_inv (real_of_num (NUMERAL (BIT1 0))))) /\ ((real_inv (real_inv x0)) = x0)) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = x0.
Definition term35 := (exists y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term14 := imp (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term83 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term6 := (((~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term58 := @eq Prop ((exists y0 : real, ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (~ ((real_inv y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term57 := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0)).
