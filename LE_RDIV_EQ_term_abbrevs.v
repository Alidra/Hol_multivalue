Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term133 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term218 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) (Nat.add (Nat.mul x1 (Nat.div x0 x1)) x1).
Definition term166 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term53 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term36 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.lt y0 x1).
Definition term246 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.lt x1 x2).
Definition term243 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term204 := (~ False) -> False.
Definition term37 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.lt y0 x1).
Definition term214 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term12 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term187 (x0 : Prop) := ~ (~ x0).
Definition term261 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt y1 y2))) x0.
Definition term250 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.lt (Nat.modulo y1 y0) y0)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False) x0.
Definition term205 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.le (Nat.mul y0 y2) (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False) x0.
Definition term65 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term45 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.lt y1 y2)) x0.
Definition term129 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x1 x0) (Nat.add x1 x2).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.le x1 x2))).
Definition term58 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term41 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1.
Definition term135 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term157 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0))).
Definition term232 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term108 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term2 := fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term88 (x0 : Prop) := (~ x0) -> False.
Definition term141 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term136 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ (Peano.le x0 (Nat.div x1 x2)).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x2.
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x2.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> False.
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (x1 = x2)).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term161 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term220 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term3 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term257 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = (Peano.le x0 y0).
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.lt x1 y0).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term52 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term227 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term247 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term158 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term190 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term245 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term56 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term39 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.lt y1 y0)) -> Peano.lt x0 y0.
Definition term226 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term199 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = (Nat.add (Nat.mul (Nat.div x2 x0) x0) (Nat.modulo x2 x0))) /\ (Peano.le (Nat.mul x0 x1) x2).
Definition term97 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term15 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.le x0 x1))))) -> Peano.le x2 x3.
Definition term225 (x0 : nat) (x1 : nat) := imp (~ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term124 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term231 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term107 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term210 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term152 (x0 : Prop) := (~ x0) -> x0.
Definition term140 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term128 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term105 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term184 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term155 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term72 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (Nat.div y0 y1)) y0) x0.
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 (Nat.div x1 x2)) -> Peano.le x0 (Nat.div x1 x2).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term209 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x0 x1) x2).
Definition term156 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term213 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term164 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term263 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1))) x1.
Definition term251 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.lt (Nat.modulo y0 x0) x0)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x1.
Definition term206 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x1.
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.lt y0 y1)) x1.
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term61 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term126 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term260 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0)) x0.
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3))).
Definition term211 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1).
Definition term208 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x0 x1) x2)) -> Peano.le (Nat.mul x0 x1) x2.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul x2 x0) = (Nat.mul x2 x0)) /\ ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) /\ (Peano.le (Nat.mul x2 x0) x1))) -> Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term14 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term167 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term170 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term219 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> False.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x2 x0) (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0)))).
Definition term96 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.le x1 x2).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0) x2.
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0))) x2.
Definition term234 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term233 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term110 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term109 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 y0) x0) -> (~ (Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term38 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.lt y0 x1)) -> Peano.lt x0 x1.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.div x2 x0)) -> Peano.le (Nat.mul x0 x1) x2.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term125 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x0 x1) y0) /\ (Peano.le y0 x2).
Definition term281 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 (Nat.div x1 x2)) -> Peano.le (Nat.mul x2 x0) x1) /\ ((Peano.le (Nat.mul x2 x0) x1) -> Peano.le x0 (Nat.div x1 x2)).
Definition term120 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term79 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.mul x2 x0) (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))))) -> Peano.le x0 (Nat.div x1 x2).
Definition term183 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term285 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1).
Definition term284 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term262 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1)).
Definition term242 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.lt (Nat.modulo y1 y0) y0)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term241 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.lt (Nat.modulo y1 y0) y0)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term238 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.lt (Nat.modulo y0 x0) x0)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term237 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.lt (Nat.modulo y0 x0) x0)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term138 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term131 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term118 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.le (Nat.mul y0 y2) (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term117 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.le (Nat.mul y0 y2) (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term114 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term113 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term98 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term66 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term57 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term46 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term44 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term40 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1.
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1.
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term6 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.lt y0 y1).
Definition term159 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term269 (x0 : nat) (x1 : nat) := Nat.add (Nat.div x0 x1) (NUMERAL (BIT1 0)).
Definition term258 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = (Peano.le x0 y0)) x1.
Definition term244 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0)).
Definition term259 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term119 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x2 x0) y0) /\ (Peano.lt y0 (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0)))))) -> Peano.lt (Nat.mul x2 x0) (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0)))).
Definition term0 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term75 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 (Nat.div x1 x0)) x1.
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term151 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (Nat.mul x0 x1)).
Definition term73 (x0 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (Nat.div x0 y0)) x0.
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.le x1 x2)).
Definition term264 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0)).
Definition term68 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))).
Definition term87 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.add (Nat.div x0 x1) (NUMERAL (BIT1 0))).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.mul x2 x0) (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.mul x0 x1) x2).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term84 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term18 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (Peano.lt x0 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0)))).
Definition term153 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x2 x0) y0) /\ (Peano.lt y0 (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))))).
Definition term189 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term13 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term150 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (Nat.mul x0 x1))) -> (Nat.mul x0 x1) = (Nat.mul x0 x1).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0.
Definition term270 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term142 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term35 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.le x0 x1))) -> Peano.le x2 x3.
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x0 x1) = (Nat.mul x0 x1)) /\ ((x2 = (Nat.add (Nat.mul (Nat.div x2 x0) x0) (Nat.modulo x2 x0))) /\ (Peano.le (Nat.mul x0 x1) x2)).
Definition term16 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = (NUMERAL 0)) \/ (Peano.le x0 (Nat.div x1 x2)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term256 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = (Peano.le y0 y1)) x0.
Definition term139 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.lt y2 y1)) -> Peano.lt y0 y1) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3)).
Definition term282 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term193 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term217 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) (Nat.mul x1 (Nat.add (Nat.div x0 x1) (NUMERAL (BIT1 0)))).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) -> Peano.le x0 (Nat.div x1 x2).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term132 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.lt x0 x2)) -> Peano.lt x1 x2.
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.le x1 x2))).
Definition term271 (x0 : nat) (x1 : nat) := S (Nat.div x0 x1).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term216 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) x1.
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)) (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))))).
Definition term160 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term55 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x1 x0) (Nat.mul x1 (Nat.div x2 x1))) /\ (Peano.le (Nat.mul x1 (Nat.div x2 x1)) x2).
Definition term212 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term146 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term76 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term134 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.lt (Nat.modulo x1 x2) x2)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (Peano.le (Nat.mul x2 x0) x1) -> (~ (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term54 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 x0) (Nat.mul x2 (Nat.div x1 x2)).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term74 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Nat.mul y0 (Nat.div x0 y0)) x0) x1.
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 x1) y0) /\ (Peano.le y0 x2).
Definition term4 := forall y0 : nat, (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term127 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term249 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> False.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.lt x1 y0)) x2.
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le x0 (Nat.div x1 x2)).
Definition term1 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x2 x0) (Nat.mul x2 (Nat.div x1 x2))).
Definition term123 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) -> False.
Definition term188 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2).
Definition term283 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term121 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term172 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (S (Nat.div x1 x2)).
Definition term11 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x2 x0) y0) /\ (Peano.lt y0 (Nat.mul x2 (Nat.add (Nat.div x1 x2) (NUMERAL (BIT1 0))))).
Definition term236 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.lt (Nat.modulo y0 x0) x0)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term235 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.lt (Nat.modulo y0 x0) x0)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term137 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term130 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term122 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term112 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term111 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x0 y1) y0) -> (~ (Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term215 := NUMERAL (BIT1 0).
Definition term154 (x0 : Prop) := x0 -> ~ x0.
Definition term240 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.lt (Nat.modulo y1 y0) y0)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term239 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.lt (Nat.modulo y1 y0) y0)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term116 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.le (Nat.mul y0 y2) (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term115 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.mul y0 y2) y1) -> (~ (Peano.le (Nat.mul y0 y2) (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.lt y1 y0)) -> Peano.lt x0 y0) x1.
Definition term248 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x0 x1) y0) /\ (Peano.le y0 x2)) -> Peano.le (Nat.mul x0 x1) x2.