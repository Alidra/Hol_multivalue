Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term333 := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)).
Definition term181 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x1 x0) = (Nat.mul x0 x1))) -> (Nat.mul x1 x0) = (Nat.mul x0 x1).
Definition term321 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1.
Definition term186 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 (Nat.mul x1 x2)) x0) = (Nat.mul x1 x2).
Definition term34 (x0 : Prop) := imp ((True -> x0) /\ True).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x0 = (Nat.mul x2 x1)) = x4) -> (x4 -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = x5) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = (x4 -> x5).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x1 = (Nat.mul x2 x0)) = x4) -> (x4 -> ((Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = x5) -> ((x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = (x4 -> x5).
Definition term84 (x0 : nat -> Prop) := ~ (all x0).
Definition term234 := (~ False) -> False.
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (num_divides y0 x1) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))) x2.
Definition term66 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides y0 x0) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul (Nat.div x0 y0) x1).
Definition term123 (x0 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))).
Definition term110 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))).
Definition term122 (x0 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))) x0).
Definition term257 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0).
Definition term315 := @eq nat (NUMERAL 0).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term61 (x0 : nat) (x1 : nat) := forall y0 : nat, (num_divides y0 x1) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0)).
Definition term301 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term175 (x0 : Prop) := ~ (~ x0).
Definition term296 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2))) x0.
Definition term157 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) x0.
Definition term102 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))) x0.
Definition term322 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 x1) x0) = x1.
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul (Nat.mul x2 x0) x1) x2.
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0))) x2.
Definition term47 := (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term255 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term312 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL 0) (Nat.mul x0 x1).
Definition term151 (x0 : nat) := fun y0 : nat => exists y1 : nat, (forall y2 : nat, forall y3 : nat, forall y4 : nat, (~ (num_divides y4 y2)) \/ ((Nat.div (Nat.mul y2 y3) y4) = (Nat.mul (Nat.div y2 y4) y3))) /\ ((num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))).
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ ((fun y0 : nat => (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))))) x2).
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term44 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.div x0 x2) = (Nat.div x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2)) /\ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.mul x0 (Nat.div x1 x2)))) -> (Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2)).
Definition term49 := (((~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term178 (x0 : nat) (x1 : nat) := imp (num_divides x0 x1).
Definition term184 (x0 : nat) := ~ (x0 = x0).
Definition term112 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.div x1 x2).
Definition term43 (x0 : Prop) := (~ x0) -> False.
Definition term334 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))).
Definition term314 := Nat.div (NUMERAL 0) (NUMERAL 0).
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term39 (x0 : Prop) (x1 : Prop) := (((x0 -> x1) /\ x0) -> x0 /\ x1) -> ((x0 -> x1) /\ x0) -> x0 /\ x1.
Definition term96 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (num_divides y1 y0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))) x1).
Definition term40 := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2)).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.mul x1 x2)).
Definition term302 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term299 (x0 : nat) := (fun y0 : nat => (Nat.div (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term150 (x0 : nat) (x1 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))))).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) /\ ((Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2))) -> (Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul (Nat.mul x0 x1) x2).
Definition term173 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul x0 (Nat.mul x1 x2)).
Definition term201 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (num_divides x1 x0)) \/ ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2))).
Definition term276 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x0 x1).
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul x2 (Nat.mul x0 x1)) x2.
Definition term86 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, (num_divides y0 x1) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))).
Definition term176 (x0 : nat) (x1 : nat) := ~ (~ (num_divides x0 x1)).
Definition term100 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))).
Definition term93 (x0 : nat) := ~ (forall y0 : nat, forall y1 : nat, (num_divides y1 y0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))).
Definition term52 := ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (num_divides y0 x0)) \/ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul (Nat.div x0 y0) x1))) x2.
Definition term111 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (num_divides x1 x0)) \/ ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2))).
Definition term54 := imp (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))).
Definition term320 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0.
Definition term169 (x0 : Prop) := (~ x0) -> x0.
Definition term75 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (num_divides y0 x0)) \/ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul (Nat.div x0 y0) x1)).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term284 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2.
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term300 (x0 : nat) := Nat.div (NUMERAL 0) x0.
Definition term38 (x0 : Prop) (x1 : Prop) := (((x0 -> x1) /\ x0) -> x0 /\ x1) -> x0 /\ x1.
Definition term196 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (num_divides x1 x0))) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term91 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0)))).
Definition term183 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term98 (x0 : nat) := fun y0 : nat => exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1)))).
Definition term330 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.mul x2 x1)) -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = True.
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term56 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term258 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term136 (x0 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0).
Definition term124 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((num_divides x1 x0) = y0) -> (y0 -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = y1) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = (y0 -> y1)) x3.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div x0 x1) x2.
Definition term138 (x0 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ (exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))).
Definition term126 := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ (exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))).
Definition term275 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 x1).
Definition term130 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0.
Definition term118 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0.
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul (Nat.mul x1 y0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 y0) x1) x2).
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term189 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term297 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1))) x1.
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (num_divides y1 x0)) \/ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul (Nat.div x0 y1) y0))) x1.
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y1 y0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))) x1.
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.mul x1 y0)) x2.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x0 x2) = (Nat.div x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term16 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul x0 x1) x2.
Definition term58 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term286 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = (Nat.mul x2 x1)) -> ((Nat.div (Nat.mul x0 x3) x2) = (Nat.mul (Nat.div x0 x2) x3)) = ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3))) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul x0 x3) x2) = (Nat.mul (Nat.div x0 x2) x3)) = ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term281 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x1 x0) x1.
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x0 x2) = (Nat.div x1 x3)) \/ (~ (x2 = x3)).
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.mul (Nat.mul x2 x0) x1) x2).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.mul x0 x1) x2).
Definition term25 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1.
Definition term285 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.mul x2 x1)) -> ((Nat.div (Nat.mul x0 x3) x2) = (Nat.mul (Nat.div x0 x2) x3)) = ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.mul x0 (Nat.div x1 x2))).
Definition term114 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term235 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((fun y0 : nat => x1 = (Nat.mul x2 y0)) x0) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3).
Definition term182 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x1 x0) = (Nat.mul x0 x1)).
Definition term125 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ (exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))))) x2.
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term113 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((num_divides x1 x0) = x3) -> (x3 -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = x4) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = (x3 -> x4).
Definition term67 (x0 : nat) (x1 : nat) := forall y0 : nat, (num_divides y0 x0) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul (Nat.div x0 y0) x1).
Definition term51 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term31 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) False.
Definition term142 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0.
Definition term167 (x0 : nat) (x1 : nat) := (~ (num_divides x0 x1)) -> num_divides x0 x1.
Definition term32 (x0 : Prop) := ((False -> x0) /\ False) -> False /\ x0.
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) /\ ((Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2)).
Definition term243 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term193 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.div x0 x1) = (Nat.div x2 x3).
Definition term26 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) True.
Definition term253 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul x1 y0).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term30 (x0 : Prop) (x1 : Prop) := @eq Prop (((x0 -> x1) /\ x0) -> x0 /\ x1).
Definition term331 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.mul x2 x3)) -> ((Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = True) -> ((x1 = (Nat.mul x2 x3)) -> (Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = ((x1 = (Nat.mul x2 x3)) -> True).
Definition term317 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x3 = (NUMERAL 0)) -> ((Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = True) -> ((x3 = (Nat.mul x1 x0)) -> (Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = ((x3 = (NUMERAL 0)) -> True).
Definition term195 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x1 x0) = (Nat.mul x0 x1)) /\ (x2 = x2).
Definition term129 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))) x1.
Definition term295 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.mul y2 y3)) -> (Nat.div (Nat.mul (Nat.mul y2 y3) y1) y2) = (Nat.mul (Nat.div (Nat.mul y2 y3) y2) y1).
Definition term293 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (x0 = (Nat.mul y1 y2)) -> (Nat.div (Nat.mul (Nat.mul y1 y2) y0) y1) = (Nat.mul (Nat.div (Nat.mul y1 y2) y1) y0).
Definition term291 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (x0 = (Nat.mul y0 y1)) -> (Nat.div (Nat.mul (Nat.mul y0 y1) x1) y0) = (Nat.mul (Nat.div (Nat.mul y0 y1) y0) x1).
Definition term80 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)).
Definition term78 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (num_divides y1 x0)) \/ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul (Nat.div x0 y1) y0)).
Definition term69 (x0 : nat) := forall y0 : nat, forall y1 : nat, (num_divides y1 x0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul (Nat.div x0 y1) y0).
Definition term63 (x0 : nat) := forall y0 : nat, forall y1 : nat, (num_divides y1 y0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1)).
Definition term53 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term42 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)).
Definition term41 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term134 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ ((fun y0 : nat => exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))) x1).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2))) -> False.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (num_divides y0 x1) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))) x2).
Definition term24 (x0 : Prop) := fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0.
Definition term15 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term36 (x0 : Prop) := imp ((False -> x0) /\ False).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((num_divides x2 x1) = (exists y0 : nat, x1 = (Nat.mul x2 y0))) -> ((exists y0 : nat, x1 = (Nat.mul x2 y0)) -> ((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = x3) -> ((num_divides x2 x1) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = ((exists y0 : nat, x1 = (Nat.mul x2 y0)) -> x3).
Definition term283 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div (Nat.mul x1 x0) x1).
Definition term153 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (forall y3 : nat, forall y4 : nat, forall y5 : nat, (~ (num_divides y5 y3)) \/ ((Nat.div (Nat.mul y3 y4) y5) = (Nat.mul (Nat.div y3 y5) y4))) /\ ((num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))).
Definition term105 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.div x0 x1) = (Nat.div x2 x3)))).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((num_divides x2 x1) -> (Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2))).
Definition term135 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))))).
Definition term149 (x0 : nat) (x1 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0))))).
Definition term46 := ~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))).
Definition term29 (x0 : Prop) (x1 : Prop) := ((x0 -> x1) /\ x0) -> x0 /\ x1.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term137 (x0 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ (exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.div x0 x1) = (Nat.div x2 x3).
Definition term249 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term35 (x0 : Prop) := (False -> x0) /\ False.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term92 (x0 : nat) (x1 : nat) := exists y0 : nat, (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0)))).
Definition term313 := Nat.div (NUMERAL 0).
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.div x0 x1) = (Nat.div x2 x3).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.div x0 x1) = (Nat.div x2 x3)).
Definition term28 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1).
Definition term139 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0).
Definition term127 (x0 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0).
Definition term115 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0).
Definition term250 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.mul x2 x3)) -> ((Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = x4) -> ((x1 = (Nat.mul x2 x3)) -> (Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = ((x1 = (Nat.mul x2 x3)) -> x4).
Definition term311 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x3 = (NUMERAL 0)) -> ((Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = x4) -> ((x3 = (Nat.mul x1 x0)) -> (Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = ((x3 = (NUMERAL 0)) -> x4).
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.mul x2 x3)) -> ((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = x4) -> ((x1 = (Nat.mul x2 x3)) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = ((x1 = (Nat.mul x2 x3)) -> x4).
Definition term104 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (num_divides y3 y2) -> (Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))) y0).
Definition term97 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))) y0).
Definition term306 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((x0 = (Nat.mul x2 x1)) = x4) -> (x4 -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = y0) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = (x4 -> y0).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((x1 = (Nat.mul x2 x0)) = x4) -> (x4 -> ((Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = y0) -> ((x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = (x4 -> y0).
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((num_divides x1 x0) = x3) -> (x3 -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = y0) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = (x3 -> y0).
Definition term236 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term57 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term318 (x0 : nat) := (x0 = (NUMERAL 0)) -> True.
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term168 (x0 : nat) (x1 : nat) := ~ (num_divides x0 x1).
Definition term256 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term143 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0.
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term23 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2))) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (Nat.mul x2 x1)) = y0) -> (y0 -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = y1) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = (y0 -> y1).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((x1 = (Nat.mul x2 x0)) = y0) -> (y0 -> ((Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = y1) -> ((x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = (y0 -> y1).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((num_divides x1 x0) = y0) -> (y0 -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = y1) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = (y0 -> y1).
Definition term237 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2)))) -> (Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2)).
Definition term156 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term200 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Nat.div (Nat.mul x2 x0) x1) = (Nat.mul (Nat.div x2 x1) x0)) \/ (~ (num_divides x1 x2))).
Definition term282 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1).
Definition term33 (x0 : Prop) := (True -> x0) /\ True.
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((num_divides x1 x0) = x3) -> (x3 -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = y0) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = (x3 -> y0)) x4.
Definition term60 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides y0 x1) -> (Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0)).
Definition term307 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x0 = (Nat.mul x2 x1)) = x4) -> (x4 -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = y0) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = (x4 -> y0)) x5.
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x1 = (Nat.mul x2 x0)) = x4) -> (x4 -> ((Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = y0) -> ((x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = (x4 -> y0)) x5.
Definition term287 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3).
Definition term108 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))).
Definition term107 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)).
Definition term103 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))) x0).
Definition term208 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2))) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.div x0 x2) = (Nat.div x1 x3)) \/ (~ (x2 = x3))).
Definition term76 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (num_divides y0 x0)) \/ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul (Nat.div x0 y0) x1)).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.mul x0 (Nat.div x1 x2)))) -> (Nat.mul (Nat.div x1 x2) x0) = (Nat.mul x0 (Nat.div x1 x2)).
Definition term319 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0.
Definition term155 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term37 (x0 : Prop) (x1 : Prop) := (x1 -> x0) /\ x1.
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2)) /\ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.mul x0 (Nat.div x1 x2))).
Definition term48 := ((~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul (Nat.mul x1 y0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 y0) x1) x2).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term148 (x0 : nat) (x1 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0).
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.div x0 x1) = (Nat.div x2 x3)).
Definition term101 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (num_divides y3 y2) -> (Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))) y0).
Definition term94 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))) y0).
Definition term87 (x0 : nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (num_divides y1 x1) -> (Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))) y0).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x2 x1) -> (Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2)).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ ((num_divides x2 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2))))).
Definition term27 (x0 : Prop) := ((True -> x0) /\ True) -> True /\ x0.
Definition term162 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term323 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term55 := (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x3 = (Nat.mul x1 x0)) = (x3 = (NUMERAL 0))) -> ((x3 = (NUMERAL 0)) -> ((Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = x4) -> ((x3 = (Nat.mul x1 x0)) -> (Nat.div (Nat.mul (Nat.mul x1 x0) x2) x1) = (Nat.mul (Nat.div (Nat.mul x1 x0) x1) x2)) = ((x3 = (NUMERAL 0)) -> x4).
Definition term329 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div (Nat.mul x2 x0) x1) = (Nat.mul (Nat.div x2 x1) x0)) \/ (~ (num_divides x1 x2)).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.div x0 x1) = (Nat.div x2 x3))).
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.mul x2 x3)) = (x1 = (Nat.mul x2 x3))) -> ((x1 = (Nat.mul x2 x3)) -> ((Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = x4) -> ((x1 = (Nat.mul x2 x3)) -> (Nat.div (Nat.mul (Nat.mul x2 x3) x0) x2) = (Nat.mul (Nat.div (Nat.mul x2 x3) x2) x0)) = ((x1 = (Nat.mul x2 x3)) -> x4).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.mul x2 x3)) = (x1 = (Nat.mul x2 x3))) -> ((x1 = (Nat.mul x2 x3)) -> ((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = x4) -> ((x1 = (Nat.mul x2 x3)) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = ((x1 = (Nat.mul x2 x3)) -> x4).
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term117 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))) x0.
Definition term145 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (num_divides y0 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.div x1 y0)))))).
Definition term144 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0)).
Definition term133 (x0 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1)))))).
Definition term132 (x0 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0)).
Definition term121 := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))))).
Definition term120 := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0)).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term131 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0.
Definition term119 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0.
Definition term154 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (forall y3 : nat, forall y4 : nat, forall y5 : nat, (~ (num_divides y5 y3)) \/ ((Nat.div (Nat.mul y3 y4) y5) = (Nat.mul (Nat.div y3 y5) y4))) /\ ((num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2))))).
Definition term152 (x0 : nat) := exists y0 : nat, exists y1 : nat, (forall y2 : nat, forall y3 : nat, forall y4 : nat, (~ (num_divides y4 y2)) \/ ((Nat.div (Nat.mul y2 y3) y4) = (Nat.mul (Nat.div y2 y4) y3))) /\ ((num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1))))).
Definition term106 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))).
Definition term99 (x0 : nat) := exists y0 : nat, exists y1 : nat, (num_divides y1 y0) /\ (~ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1)))).
Definition term309 := Nat.mul (NUMERAL 0).
Definition term303 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term90 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (num_divides y1 x1) -> (Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))) y0).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => x0 = (Nat.mul x1 y0)) x2).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term45 := (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> False.
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul x1 x0) = (Nat.mul x0 x1)) /\ (x2 = x2)) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.div (Nat.mul x0 x1) x2).
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) := ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = ((Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2))) -> ((num_divides x1 x0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)) = ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term199 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term50 := (((~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> ((~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term22 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term187 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term305 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (Nat.mul x2 x1)) = y0) -> (y0 -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = y1) -> ((x0 = (Nat.mul x2 x1)) -> (Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = (y0 -> y1)) x4.
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x1 = (Nat.mul x2 x0)) = y0) -> (y0 -> ((Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = y1) -> ((x1 = (Nat.mul x2 x0)) -> (Nat.div (Nat.mul x1 x3) x2) = (Nat.mul (Nat.div x1 x2) x3)) = (y0 -> y1)) x4.
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2))) -> (Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2).
Definition term71 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x2 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) x2) = (Nat.mul x0 (Nat.div x1 x2)))).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term85 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2).
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) -> (Nat.div (Nat.mul x0 x2) x1) = (Nat.mul (Nat.div x0 x1) x2)).
Definition term14 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul (Nat.div x1 x2) x0) = (Nat.div (Nat.mul x0 x1) x2)).
Definition term290 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, (x0 = (Nat.mul y0 y1)) -> (Nat.div (Nat.mul (Nat.mul y0 y1) x1) y0) = (Nat.mul (Nat.div (Nat.mul y0 y1) y0) x1).
Definition term77 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (num_divides y1 x0)) \/ ((Nat.div (Nat.mul x0 y0) y1) = (Nat.mul (Nat.div x0 y1) y0)).
Definition term68 (x0 : nat) := fun y0 : nat => forall y1 : nat, (num_divides y1 x0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul (Nat.div x0 y1) y0).
Definition term62 (x0 : nat) := fun y0 : nat => forall y1 : nat, (num_divides y1 y0) -> (Nat.div (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.div y0 y1)).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((exists y0 : nat, x1 = (Nat.mul x2 y0)) -> ((Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = x3) -> ((num_divides x2 x1) -> (Nat.div (Nat.mul x1 x0) x2) = (Nat.mul (Nat.div x1 x2) x0)) = ((exists y0 : nat, x1 = (Nat.mul x2 y0)) -> x3).
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.mul x1 x2)) -> True.
Definition term316 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (NUMERAL 0)) -> ((Nat.div (Nat.mul (Nat.mul x2 x1) x3) x2) = (Nat.mul (Nat.div (Nat.mul x2 x1) x2) x3)) = True.
Definition term294 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.mul y2 y3)) -> (Nat.div (Nat.mul (Nat.mul y2 y3) y1) y2) = (Nat.mul (Nat.div (Nat.mul y2 y3) y2) y1).
Definition term292 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (x0 = (Nat.mul y1 y2)) -> (Nat.div (Nat.mul (Nat.mul y1 y2) y0) y1) = (Nat.mul (Nat.div (Nat.mul y1 y2) y1) y0).
Definition term79 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (num_divides y2 y0)) \/ ((Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)).
Definition term70 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1).
Definition term64 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term109 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y0) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul (Nat.div y0 y2) y1)) /\ (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y2 y1) -> (Nat.div (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.div y1 y2)))).
Definition term177 (x0 : nat) (x1 : nat) := imp (~ (~ (num_divides x0 x1))).
Definition term140 (x0 : nat) (x1 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => (num_divides y1 x1) /\ (~ ((Nat.div (Nat.mul x0 x1) y1) = (Nat.mul x0 (Nat.div x1 y1))))) y0).
Definition term128 (x0 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => exists y2 : nat, (num_divides y2 y1) /\ (~ ((Nat.div (Nat.mul x0 y1) y2) = (Nat.mul x0 (Nat.div y1 y2))))) y0).
Definition term116 := exists y0 : nat, (forall y1 : nat, forall y2 : nat, forall y3 : nat, (~ (num_divides y3 y1)) \/ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul (Nat.div y1 y3) y2))) /\ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (num_divides y3 y2) /\ (~ ((Nat.div (Nat.mul y1 y2) y3) = (Nat.mul y1 (Nat.div y2 y3))))) y0).
