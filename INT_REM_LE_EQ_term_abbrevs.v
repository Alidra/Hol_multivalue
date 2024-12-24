Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term121 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term92 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1).
Definition term86 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem y0 y1) y0) -> int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le y2 y3) /\ (int_le y3 y4)) -> int_le y2 y4) -> ~ (forall y2 : int, forall y3 : int, (~ (y3 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y2 y3)).
Definition term85 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem y0 y1) y0) -> int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le y2 y3) /\ (int_le y3 y4)) -> int_le y2 y4) -> (forall y2 : int, forall y3 : int, (~ (y3 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y2 y3)) -> False.
Definition term33 := fun y0 : int => forall y1 : int, (rem y0 y1) = (rem y0 (int_abs y1)).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le (Nat.modulo x0 y0) x0.
Definition term142 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ (~ (int_le x1 x2)).
Definition term124 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1)) x1.
Definition term109 (x0 : int) (x1 : int) := forall y0 : int, ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term163 := (~ False) -> False.
Definition term84 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x0 y0) x0) -> int_le (int_of_num (NUMERAL 0)) x0)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y1 y2) /\ (int_le y2 y3)) -> int_le y1 y3) -> ~ (forall y1 : int, forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)).
Definition term83 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x0 y0) x0) -> int_le (int_of_num (NUMERAL 0)) x0)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y1 y2) /\ (int_le y2 y3)) -> int_le y1 y3) -> (forall y1 : int, forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)) -> False.
Definition term90 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term68 (x0 : int) (x1 : int) := (((~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term112 := fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term98 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term28 (x0 : int) := fun y0 : int => (rem x0 (int_abs y0)) = (rem x0 y0).
Definition term47 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term81 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x0 y0) x0) -> int_le (int_of_num (NUMERAL 0)) x0)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y1 y2) /\ (int_le y2 y3)) -> int_le y1 y3) -> (forall y1 : int, forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)) -> False.
Definition term103 (x0 : int) (x1 : int) (x2 : int) := or (~ ((int_le x0 x1) /\ (int_le x1 x2))).
Definition term201 (x0 : nat) := forall y0 : nat, int_le (rem (int_of_num y0) (int_of_num x0)) (int_of_num y0).
Definition term168 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term182 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (rem y0 (int_of_num x0)) y0.
Definition term175 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (rem y0 (int_abs x0)) y0.
Definition term153 (x0 : Prop) := ~ (~ x0).
Definition term141 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x2)) \/ (int_le x1 x2).
Definition term60 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term29 (x0 : int) := fun y0 : int => (rem x0 y0) = (rem x0 (int_abs y0)).
Definition term179 := @eq Prop (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> int_le (rem y2 y1) y2) (int_abs y0)).
Definition term140 (x0 : int) (x1 : int) := ~ (int_le (rem x1 x0) x1).
Definition term46 := int_of_num (NUMERAL 0).
Definition term152 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le x0 x1))) /\ (~ (~ (int_le x1 x2))).
Definition term209 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term25 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 (int_abs y1)) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term212 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (rem y0 (int_abs x0)) y0) x1.
Definition term206 (x0 : nat) (x1 : nat) := int_le (int_of_num (Nat.modulo x1 x0)) (int_of_num x1).
Definition term211 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_abs y0)) y1) x0.
Definition term164 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem y0 y1) y0) -> int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le y2 y3) /\ (int_le y3 y4)) -> int_le y2 y4) -> (forall y2 : int, forall y3 : int, (~ (y3 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y2 y3)) -> False) x0.
Definition term126 (x0 : int) := (fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) x0.
Definition term36 (x0 : int) := (fun y0 : int => forall y1 : int, (rem y0 y1) = (rem y0 (int_abs y1))) x0.
Definition term41 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term136 (x0 : int) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term133 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term62 (x0 : Prop) := (~ x0) -> False.
Definition term157 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term76 (x0 : int) (x1 : int) := imp (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)).
Definition term89 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term123 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2)) x0.
Definition term11 (x0 : nat) := forall y0 : nat, (int_le (int_of_num x0) (int_of_num y0)) = (Peano.le x0 y0).
Definition term199 (x0 : nat) := fun y0 : nat => (fun y1 : int => int_le (rem y1 (int_of_num x0)) y1) (int_of_num y0).
Definition term115 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term200 (x0 : nat) := fun y0 : nat => int_le (rem (int_of_num y0) (int_of_num x0)) (int_of_num y0).
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term27 (x0 : int) (x1 : int) := rem x0 (int_abs x1).
Definition term55 := @eq int (int_of_num (NUMERAL 0)).
Definition term166 (x0 : int) (x1 : int) := int_le (rem x0 (int_abs x1)).
Definition term181 (x0 : nat) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 y0) y1) (int_of_num x0).
Definition term138 (x0 : Prop) := (~ x0) -> x0.
Definition term93 (x0 : int) (x1 : int) (x2 : int) := ((int_le x1 x0) /\ (int_le x0 x2)) -> int_le x1 x2.
Definition term129 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term94 (x0 : int) (x1 : int) := fun y0 : int => ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term188 (x0 : nat) := fun y0 : int => int_le (rem y0 (int_of_num x0)) y0.
Definition term150 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term80 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term160 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) (rem x1 x0)) /\ (int_le (rem x1 x0) x1)) -> int_le (int_of_num (NUMERAL 0)) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.modulo y0 y1) y0) x0.
Definition term130 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term146 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2))).
Definition term30 (x0 : int) := forall y0 : int, (rem x0 (int_abs y0)) = (rem x0 y0).
Definition term147 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term74 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term77 (x0 : int) (x1 : int) := (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term43 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term143 (x0 : int) (x1 : int) := or (~ (int_le x0 x1)).
Definition term63 (x0 : int) (x1 : int) := (int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1.
Definition term100 (x0 : int) (x1 : int) := (int_le (rem x1 x0) x1) /\ (~ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term213 (x0 : int) (x1 : int) := ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1) /\ ((int_le (int_of_num (NUMERAL 0)) x1) -> int_le (rem x1 x0) x1).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x1 x0) x1.
Definition term196 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (rem y0 (int_of_num x0)) y0).
Definition term195 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (rem y1 (int_of_num x0)) y1) y0).
Definition term70 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term24 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term23 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term19 := forall y0 : int -> Prop, (forall y1 : int, y0 (int_abs y1)) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term18 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, y0 (int_abs y1)).
Definition term7 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_of_num x1).
Definition term69 (x0 : int) (x1 : int) := (((~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_le (int_of_num x0) (int_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term38 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term119 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0)).
Definition term22 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term21 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term17 := fun y0 : int -> Prop => (forall y1 : int, y0 (int_abs y1)) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term16 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, y0 (int_abs y1)).
Definition term149 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term102 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ (~ (int_le x1 x2)).
Definition term203 := forall y0 : nat, forall y1 : nat, int_le (rem (int_of_num y1) (int_of_num y0)) (int_of_num y1).
Definition term185 := forall y0 : nat, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_of_num y0)) y1.
Definition term9 := forall y0 : nat, forall y1 : nat, (int_le (int_of_num y0) (int_of_num y1)) = (Peano.le y0 y1).
Definition term53 (x0 : int) (x1 : int) := int_le (rem x1 x0) x1.
Definition term180 := @eq Prop (forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_abs y0)) y1).
Definition term189 (x0 : nat) (x1 : int) := (fun y0 : int => int_le (rem y0 (int_of_num x0)) y0) x1.
Definition term197 (x0 : nat) (x1 : nat) := (fun y0 : int => int_le (rem y0 (int_of_num x0)) y0) (int_of_num x1).
Definition term174 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 y0) y1) (int_abs x0).
Definition term145 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term20 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term8 (x0 : nat) (x1 : nat) := int_of_num (Nat.modulo x0 x1).
Definition term208 := forall y0 : nat, True.
Definition term78 (x0 : int) (x1 : int) := (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term44 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term190 (x0 : nat) (x1 : int) := int_le (rem x1 (int_of_num x0)) x1.
Definition term215 := forall y0 : int, forall y1 : int, (int_le (rem y0 y1) y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term178 := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_abs y0)) y1.
Definition term122 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term113 := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term111 (x0 : int) := forall y0 : int, forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term99 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term97 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term88 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem y0 y1) y0) -> int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le y2 y3) /\ (int_le y3 y4)) -> int_le y2 y4) -> ~ (forall y2 : int, forall y3 : int, (~ (y3 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y2 y3)).
Definition term87 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem y0 y1) y0) -> int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le y2 y3) /\ (int_le y3 y4)) -> int_le y2 y4) -> (forall y2 : int, forall y3 : int, (~ (y3 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y2 y3)) -> False.
Definition term72 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1).
Definition term35 := forall y0 : int, forall y1 : int, (rem y0 y1) = (rem y0 (int_abs y1)).
Definition term34 := forall y0 : int, forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1).
Definition term184 := fun y0 : nat => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_of_num y0)) y1.
Definition term207 := fun y0 : nat => True.
Definition term171 := forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> int_le (rem y2 y1) y2) (int_abs y0).
Definition term104 (x0 : int) (x1 : int) (x2 : int) := or ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term91 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term137 (x0 : int) (x1 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term106 (x0 : int) (x1 : int) (x2 : int) := ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term177 := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 (int_abs y0)) y1.
Definition term173 := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (rem y1 y0) y1.
Definition term110 (x0 : int) := fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term96 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term32 := fun y0 : int => forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1).
Definition term191 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => int_le (rem y0 (int_of_num x0)) y0) x1.
Definition term176 := fun y0 : int => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> int_le (rem y2 y1) y2) (int_abs y0).
Definition term5 (x0 : nat) := forall y0 : nat, (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0)).
Definition term131 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term183 := fun y0 : nat => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> int_le (rem y2 y1) y2) (int_of_num y0).
Definition term169 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (rem x1 x0) x1.
Definition term39 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term155 (x0 : int) (x1 : int) := and (~ (~ (int_le x0 x1))).
Definition term187 (x0 : nat) := forall y0 : nat, (fun y1 : int => int_le (rem y1 (int_of_num x0)) y1) (int_of_num y0).
Definition term48 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term139 (x0 : int) (x1 : int) := (~ (int_le (rem x1 x0) x1)) -> int_le (rem x1 x0) x1.
Definition term61 (x0 : int) := False \/ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term54 (x0 : int) (x1 : int) := @eq Prop (int_le (rem x1 x0) x1).
Definition term71 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term73 := imp (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2).
Definition term118 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term120 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0)).
Definition term192 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (rem x1 (int_of_num x0)) x1.
Definition term170 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (rem x1 (int_abs x0)) x1.
Definition term158 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term108 (x0 : int) (x1 : int) := fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term95 (x0 : int) (x1 : int) := forall y0 : int, ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term82 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x0 y0) x0) -> int_le (int_of_num (NUMERAL 0)) x0)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y1 y2) /\ (int_le y2 y3)) -> int_le y1 y3) -> ~ (forall y1 : int, forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_le (int_of_num y0) (int_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))) x0.
Definition term156 (x0 : int) (x1 : int) := and (int_le x0 x1).
Definition term79 (x0 : int) := imp (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term204 (x0 : nat) (x1 : nat) := int_le (rem (int_of_num x0) (int_of_num x1)).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))) x1.
Definition term202 := fun y0 : nat => forall y1 : nat, int_le (rem (int_of_num y1) (int_of_num y0)) (int_of_num y1).
Definition term14 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term165 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x0 y0) x0) -> int_le (int_of_num (NUMERAL 0)) x0)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y1 y2) /\ (int_le y2 y3)) -> int_le y1 y3) -> (forall y1 : int, forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)) -> False) x1.
Definition term194 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (rem y0 (int_of_num x0)) y0.
Definition term65 (x0 : int) (x1 : int) := ~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1).
Definition term58 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x1).
Definition term151 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term105 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_le x1 x0) /\ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term67 (x0 : int) (x1 : int) := ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False) -> (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term114 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term198 (x0 : nat) (x1 : nat) := int_le (rem (int_of_num x1) (int_of_num x0)) (int_of_num x1).
Definition term75 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term186 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (rem y1 (int_of_num x0)) y1) y0.
Definition term193 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (rem y1 (int_of_num x0)) y1) y0.
Definition term37 (x0 : int) (x1 : int) := (fun y0 : int => (rem x0 y0) = (rem x0 (int_abs y0))) x1.
Definition term40 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term101 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term162 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> False.
Definition term107 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x1) /\ (int_le x1 x2).
Definition term210 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : int -> Prop) := forall y0 : int, x0 (int_abs y0).
Definition term167 (x0 : int) (x1 : int) := int_le (rem x1 (int_abs x0)) x1.
Definition term51 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term13 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term64 (x0 : int) (x1 : int) := (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> False.
Definition term45 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term50 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term57 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term144 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ ((int_le x0 x2) \/ (~ (int_le x1 x2))).
Definition term49 (x0 : int) := (fun y0 : int => int_le y0 y0) x0.
Definition term31 (x0 : int) := forall y0 : int, (rem x0 y0) = (rem x0 (int_abs y0)).
Definition term172 := forall y0 : nat, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> int_le (rem y2 y1) y2) (int_of_num y0).
Definition term56 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term117 (x0 : int) (x1 : int) := (~ (~ (x1 = (int_of_num (NUMERAL 0))))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term214 (x0 : int) := forall y0 : int, (int_le (rem x0 y0) x0) = ((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term116 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term205 (x0 : nat) (x1 : nat) := int_le (int_of_num (Nat.modulo x0 x1)).
Definition term128 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2)).
Definition term159 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x1 x0)) /\ (int_le (rem x1 x0) x1).
Definition term134 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))).
Definition term161 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term52 (x0 : int) (x1 : int) := int_le (rem x0 x1).
Definition term125 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0)) x2.
Definition term154 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term127 (x0 : int) (x1 : int) := (fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) x1.
Definition term148 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2)))) -> int_le x1 x2.
Definition term132 (x0 : Prop) := x0 -> ~ x0.
Definition term66 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (~ ((int_le (rem x1 x0) x1) -> int_le (int_of_num (NUMERAL 0)) x1)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) -> False.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Nat.modulo x0 y0) x0) x1.
Definition term59 (x0 : int) := True \/ (int_le (int_of_num (NUMERAL 0)) x0).
