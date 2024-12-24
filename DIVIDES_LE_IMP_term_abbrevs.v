Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term104 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) /\ (~ (Peano.le x0 x1))) -> x1 = (NUMERAL 0).
Definition term125 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term37 (x0 : nat -> Prop) := ~ (all x0).
Definition term107 := (~ False) -> False.
Definition term84 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ ((x1 = (NUMERAL 0)) \/ (~ (num_divides x0 x1))).
Definition term141 (x0 : nat) := (x0 = x0) /\ ((~ (Peano.le (NUMERAL 0) x0)) /\ (Peano.le x0 x0)).
Definition term117 (x0 : nat) := ~ (num_divides (NUMERAL 0) x0).
Definition term68 (x0 : nat) := fun y0 : nat => num_divides y0 x0.
Definition term152 (x0 : nat) := ((num_divides (NUMERAL 0) x0) /\ (~ (x0 = (NUMERAL 0)))) -> Peano.le (NUMERAL 0) x0.
Definition term18 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) -> (Peano.le x0 y0) \/ (y0 = (NUMERAL 0)).
Definition term98 (x0 : Prop) := ~ (~ x0).
Definition term120 (x0 : nat) := (Peano.le (NUMERAL 0) x0) -> ~ (Peano.le (NUMERAL 0) x0).
Definition term142 (x0 : nat) := ((x0 = x0) /\ ((~ (Peano.le (NUMERAL 0) x0)) /\ (Peano.le x0 x0))) -> ~ (x0 = (NUMERAL 0)).
Definition term71 (x0 : nat) := num_divides (NUMERAL 0) x0.
Definition term41 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((num_divides x0 y0) /\ ((y0 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y0) x1.
Definition term36 (x0 : nat) (x1 : nat) := ~ (((num_divides x0 x1) /\ ((x1 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 x1).
Definition term119 (x0 : nat) := ~ (x0 = x0).
Definition term22 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) /\ ((x1 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 x1.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term20 := fun y0 : nat => Peano.le y0 y0.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => num_divides y0 x0) x1.
Definition term73 (x0 : nat) (x1 : nat) := @eq Prop (num_divides x0 x1).
Definition term52 (x0 : nat) (x1 : nat) := (~ (num_divides x0 x1)) \/ ((Peano.le x0 x1) \/ (x1 = (NUMERAL 0))).
Definition term44 (x0 : nat) := fun y0 : nat => ((num_divides x0 y0) /\ ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) /\ (~ (Peano.le x0 y0)).
Definition term92 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term130 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term11 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term27 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term32 (x0 : nat) (x1 : nat) := and ((num_divides x1 x0) /\ ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0))).
Definition term39 (x0 : nat) := ~ (forall y0 : nat, ((num_divides x0 y0) /\ ((y0 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y0).
Definition term99 (x0 : nat) (x1 : nat) := ~ (~ (num_divides x0 x1)).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))).
Definition term3 := ~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1).
Definition term93 (x0 : nat) (x1 : nat) := (~ ((~ (num_divides x0 x1)) \/ (Peano.le x0 x1))) -> x1 = (NUMERAL 0).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (Peano.le x2 x3).
Definition term76 (x0 : Prop) := (~ x0) -> x0.
Definition term16 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> (Peano.le x0 x1) \/ (x1 = (NUMERAL 0)).
Definition term5 := ((~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term106 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term95 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term123 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term118 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term50 := fun y0 : nat => exists y1 : nat, ((num_divides y0 y1) /\ ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ (~ (Peano.le y0 y1)).
Definition term17 (x0 : nat) := fun y0 : nat => (num_divides x0 y0) -> (Peano.le x0 y0) \/ (y0 = (NUMERAL 0)).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3))).
Definition term30 (x0 : nat) (x1 : nat) := (num_divides x1 x0) /\ ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0))).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x3 = x1))) /\ (~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term122 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term79 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))).
Definition term154 (x0 : nat) := (Peano.le (NUMERAL 0) x0) -> False.
Definition term29 (x0 : nat) (x1 : nat) := (num_divides x1 x0) /\ ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)).
Definition term58 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term25 := fun y0 : nat => forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1.
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term88 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (num_divides x0 x1)).
Definition term153 (x0 : nat) := (~ (Peano.le (NUMERAL 0) x0)) -> Peano.le (NUMERAL 0) x0.
Definition term62 (x0 : nat) := fun y0 : nat => ~ (Peano.le y0 x0).
Definition term61 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term31 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term83 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term96 (x0 : nat) (x1 : nat) := ~ ((~ (num_divides x0 x1)) \/ (Peano.le x0 x1)).
Definition term8 := (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term102 (x0 : nat) (x1 : nat) := imp (~ ((~ (num_divides x0 x1)) \/ (Peano.le x0 x1))).
Definition term105 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term74 (x0 : nat) (x1 : nat) := (~ (num_divides x0 x1)) -> num_divides x0 x1.
Definition term28 (x0 : nat) (x1 : nat) := and (num_divides x0 x1).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term86 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x0 x1) \/ ((x1 = (NUMERAL 0)) \/ (~ (num_divides x0 x1)))).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term151 (x0 : nat) := (num_divides (NUMERAL 0) x0) /\ (~ (x0 = (NUMERAL 0))).
Definition term140 (x0 : nat) := (~ (Peano.le (NUMERAL 0) x0)) /\ (Peano.le x0 x0).
Definition term89 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term55 (x0 : nat) := forall y0 : nat, (~ (num_divides x0 y0)) \/ ((Peano.le x0 y0) \/ (y0 = (NUMERAL 0))).
Definition term94 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term57 := forall y0 : nat, forall y1 : nat, (~ (num_divides y0 y1)) \/ ((Peano.le y0 y1) \/ (y1 = (NUMERAL 0))).
Definition term10 := forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0)).
Definition term1 := forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1.
Definition term53 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (x1 = (NUMERAL 0)).
Definition term13 := (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))).
Definition term6 := (((~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term72 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => num_divides y0 x0) x1).
Definition term12 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term121 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term85 (x0 : nat) (x1 : nat) := @eq Prop ((~ (num_divides x0 x1)) \/ ((Peano.le x0 x1) \/ (x1 = (NUMERAL 0)))).
Definition term90 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((~ (num_divides x0 x1)) \/ (Peano.le x0 x1)).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> False.
Definition term147 (x0 : nat) (x1 : nat) := (num_divides x0 x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term49 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((num_divides y1 y2) /\ ((y2 = (NUMERAL 0)) -> y1 = (NUMERAL 0))) -> Peano.le y1 y2) y0).
Definition term35 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) /\ ((~ (x1 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) /\ (~ (Peano.le x0 x1)).
Definition term34 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) /\ ((x1 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) /\ (~ (Peano.le x0 x1)).
Definition term26 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term148 (x0 : nat) (x1 : nat) := imp (~ ((~ (num_divides x0 x1)) \/ (x1 = (NUMERAL 0)))).
Definition term103 (x0 : nat) (x1 : nat) := imp ((num_divides x0 x1) /\ (~ (Peano.le x0 x1))).
Definition term143 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (Peano.le y0 x0)) x1.
Definition term75 (x0 : nat) (x1 : nat) := ~ (num_divides x0 x1).
Definition term65 (x0 : nat) := ~ (Peano.le (NUMERAL 0) x0).
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term80 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ ((~ (num_divides x0 x1)) \/ (x1 = (NUMERAL 0))).
Definition term129 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term100 (x0 : nat) (x1 : nat) := and (~ (~ (num_divides x0 x1))).
Definition term149 (x0 : nat) (x1 : nat) := imp ((num_divides x0 x1) /\ (~ (x1 = (NUMERAL 0)))).
Definition term24 (x0 : nat) := forall y0 : nat, ((num_divides x0 y0) /\ ((y0 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y0.
Definition term77 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x0 x1).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = x0) /\ ((~ (Peano.le x3 x0)) /\ (Peano.le x2 x1))) -> ~ (x2 = x3).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term82 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (~ (num_divides x0 x1)).
Definition term108 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term66 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (Peano.le y0 x0)) x1).
Definition term23 (x0 : nat) := fun y0 : nat => ((num_divides x0 y0) /\ ((y0 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y0.
Definition term48 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1) x0).
Definition term116 (x0 : nat) := (~ (num_divides (NUMERAL 0) x0)) -> num_divides (NUMERAL 0) x0.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x1 = x0)) \/ ((Peano.le x3 x0) \/ (~ (Peano.le x2 x1))))) -> ~ (x2 = x3).
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (num_divides y0 y1)) \/ ((Peano.le y0 y1) \/ (y1 = (NUMERAL 0)))) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1) x0.
Definition term144 (x0 : nat) (x1 : nat) := (~ ((~ (num_divides x0 x1)) \/ (x1 = (NUMERAL 0)))) -> Peano.le x0 x1.
Definition term133 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term145 (x0 : nat) (x1 : nat) := ~ ((~ (num_divides x0 x1)) \/ (x1 = (NUMERAL 0))).
Definition term87 (x0 : nat) (x1 : nat) := (~ (num_divides x0 x1)) \/ (Peano.le x0 x1).
Definition term33 (x0 : nat) (x1 : nat) := and ((num_divides x1 x0) /\ ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)))).
Definition term81 (x0 : nat) (x1 : nat) := (~ (num_divides x0 x1)) \/ (x1 = (NUMERAL 0)).
Definition term46 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((num_divides y1 y2) /\ ((y2 = (NUMERAL 0)) -> y1 = (NUMERAL 0))) -> Peano.le y1 y2) y0).
Definition term40 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((num_divides x0 y1) /\ ((y1 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y1) y0).
Definition term21 := forall y0 : nat, Peano.le y0 y0.
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3)).
Definition term112 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term67 (x0 : nat) (x1 : nat) := @eq Prop (~ (Peano.le x0 x1)).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (~ (~ (Peano.le x2 x3))).
Definition term101 (x0 : nat) (x1 : nat) := (num_divides x0 x1) /\ (~ (Peano.le x0 x1)).
Definition term51 := exists y0 : nat, exists y1 : nat, ((num_divides y0 y1) /\ ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ (~ (Peano.le y0 y1)).
Definition term43 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((num_divides x0 y1) /\ ((y1 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y1) y0).
Definition term42 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => ((num_divides x0 y0) /\ ((y0 = (NUMERAL 0)) -> x0 = (NUMERAL 0))) -> Peano.le x0 y0) x1).
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (num_divides x0 y0)) \/ ((Peano.le x0 y0) \/ (y0 = (NUMERAL 0)))) x1.
Definition term128 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term97 (x0 : nat) (x1 : nat) := (~ (~ (num_divides x0 x1))) /\ (~ (Peano.le x0 x1)).
Definition term54 (x0 : nat) := fun y0 : nat => (~ (num_divides x0 y0)) \/ ((Peano.le x0 y0) \/ (y0 = (NUMERAL 0))).
Definition term146 (x0 : nat) (x1 : nat) := (~ (~ (num_divides x0 x1))) /\ (~ (x1 = (NUMERAL 0))).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term4 := (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) -> False.
Definition term38 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term70 (x0 : nat) := (fun y0 : nat => num_divides y0 x0) (NUMERAL 0).
Definition term134 (x0 : nat) (x1 : nat) := and (~ (Peano.le x0 x1)).
Definition term64 (x0 : nat) := (fun y0 : nat => ~ (Peano.le y0 x0)) (NUMERAL 0).
Definition term56 := fun y0 : nat => forall y1 : nat, (~ (num_divides y0 y1)) \/ ((Peano.le y0 y1) \/ (y1 = (NUMERAL 0))).
Definition term19 := fun y0 : nat => forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0)).
Definition term91 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((Peano.le x0 x1) \/ (~ (num_divides x0 x1))).
Definition term14 := imp (~ (forall y0 : nat, forall y1 : nat, ((num_divides y0 y1) /\ ((y1 = (NUMERAL 0)) -> y0 = (NUMERAL 0))) -> Peano.le y0 y1)).
Definition term78 (x0 : Prop) := x0 -> ~ x0.
Definition term45 (x0 : nat) := exists y0 : nat, ((num_divides x0 y0) /\ ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) /\ (~ (Peano.le x0 y0)).
Definition term150 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) /\ (~ (x1 = (NUMERAL 0)))) -> Peano.le x0 x1.
