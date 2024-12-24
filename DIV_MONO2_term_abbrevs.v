Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term244 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term251 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term16 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term75 (x0 : nat) (x1 : nat) := (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term300 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))))).
Definition term131 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1)))) /\ ((~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term224 (x0 : nat) := (~ (~ (Peano.le x0 (NUMERAL 0)))) -> x0 = (NUMERAL 0).
Definition term218 (x0 : nat) := ~ (Peano.le x0 (NUMERAL 0)).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term197 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term118 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) /\ (~ (Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)).
Definition term232 := (~ False) -> False.
Definition term228 (x0 : nat) := imp (Peano.le x0 (NUMERAL 0)).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term148 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term189 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term167 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term143 := forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term59 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (Nat.div x1 x0) x0) x1.
Definition term225 (x0 : Prop) := ~ (~ x0).
Definition term308 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (~ (((~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> Peano.le (Nat.mul (Nat.div y0 y1) y1) y0)) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> False) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term175 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term154 := fun y0 : nat => ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term151 (x0 : nat) := (fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0.
Definition term95 (x0 : nat) := fun y0 : nat => Peano.le x0 (Nat.add x0 y0).
Definition term54 (x0 : nat) (x1 : nat) := True /\ (Peano.le (Nat.mul x0 (Nat.div x1 x0)) x1).
Definition term128 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1))).
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.le x1 x2))).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term21 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term170 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term120 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))) /\ ((~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x0 (Nat.div x1 x2)) (Nat.mul x2 (Nat.div x1 x2))).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term248 (x0 : nat) := ~ (x0 = x0).
Definition term277 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.div x1 x2).
Definition term132 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)))) /\ ((~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term60 (x0 : Prop) := (~ x0) -> False.
Definition term190 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term168 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term144 := (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term208 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term284 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False) x2.
Definition term281 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (x1 = x2)).
Definition term282 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term246 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term213 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 y0) x1.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x0 (Nat.div x2 x1)) y0) /\ (Peano.le y0 x2)) -> Peano.le (Nat.mul x0 (Nat.div x2 x1)) x2.
Definition term184 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0.
Definition term179 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0.
Definition term163 := forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term158 := forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term217 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) -> Peano.le x0 (NUMERAL 0).
Definition term283 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term15 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term222 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (~ (Peano.le x0 (NUMERAL 0)))).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term223 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term272 (x0 : nat) (x1 : nat) := ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (x1 = x1)) -> (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1.
Definition term141 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term266 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term19 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.div x1 x2)) (Nat.mul x2 (Nat.div x1 x2)).
Definition term187 := fun y0 : nat => (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term69 := ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.le x0 x1))))) -> Peano.le x2 x3.
Definition term110 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term146 := fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term77 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term219 (x0 : Prop) := (~ x0) -> x0.
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term220 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (Peano.le x0 (NUMERAL 0))).
Definition term72 := ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term80 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term231 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term261 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term96 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term125 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1)).
Definition term247 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term73 := ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term152 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term115 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.mul (Nat.div x1 x0) x0) x1).
Definition term199 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term198 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0)).
Definition term177 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)))).
Definition term176 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0)).
Definition term156 := @eq Prop (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term155 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0)).
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term307 (x0 : nat) (x1 : nat) := (Peano.le (Nat.mul (Nat.div x1 x0) x0) x1) -> False.
Definition term57 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x1 (Nat.div x0 x1)).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term76 (x0 : nat) (x1 : nat) := (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term212 (x0 : nat) := fun y0 : nat => Peano.le x0 y0.
Definition term304 (x0 : nat) (x1 : nat) := ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1)) /\ (((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = x0) /\ (Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term254 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term309 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (((~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) -> Peano.le (Nat.mul (Nat.div x0 y0) y0) x0)) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False) x1.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term129 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1)))).
Definition term100 (x0 : nat) := fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term291 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term25 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term113 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term301 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3))).
Definition term211 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term56 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term149 (x0 : nat) := and ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0).
Definition term153 (x0 : nat) := ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0) /\ ((fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0).
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term166 := and ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term242 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1))) -> (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1).
Definition term279 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term157 := fun y0 : nat => (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term49 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term83 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)).
Definition term82 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False.
Definition term68 := (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.le x1 x2).
Definition term230 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term85 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)).
Definition term84 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> ((~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term74 (x0 : nat) (x1 : nat) := imp (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)).
Definition term182 (x0 : nat) := and (forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))).
Definition term161 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term137 := and (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term107 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))).
Definition term276 (x0 : nat) (x1 : nat) := (~ (Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term111 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term171 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1.
Definition term311 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x0 (Nat.div x2 x1)) y0) /\ (Peano.le y0 x2).
Definition term71 := imp ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term130 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)))).
Definition term183 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0.
Definition term178 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0.
Definition term162 := fun y0 : nat => (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term112 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term243 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1)).
Definition term260 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term316 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y2 = (NUMERAL 0))) /\ (Peano.le y2 y0)) -> Peano.le (Nat.div y1 y0) (Nat.div y1 y2).
Definition term315 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.le y1 x0)) -> Peano.le (Nat.div y0 x0) (Nat.div y0 y1).
Definition term207 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term202 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1))).
Definition term136 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term103 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term93 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (~ (((~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> Peano.le (Nat.mul (Nat.div y0 y1) y1) y0)) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> ~ (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)).
Definition term92 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (~ (((~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> Peano.le (Nat.mul (Nat.div y0 y1) y1) y0)) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> False.
Definition term89 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (((~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) -> Peano.le (Nat.mul (Nat.div x0 y0) y0) x0)) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> ~ (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)).
Definition term88 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (((~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) -> Peano.le (Nat.mul (Nat.div x0 y0) y0) x0)) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False.
Definition term70 := forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term41 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term27 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term20 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term7 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term196 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0).
Definition term273 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1.
Definition term229 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) -> x0 = (NUMERAL 0).
Definition term147 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term61 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1.
Definition term215 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 y0) x1).
Definition term58 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (Nat.div x0 x1) x1).
Definition term3 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term119 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) \/ ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0))) /\ (~ (Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.div x2 x1)) x2.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term313 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le x2 x0)) -> Peano.le (Nat.div x1 x0) (Nat.div x1 x2).
Definition term305 (x0 : nat) (x1 : nat) := (((Nat.mul (Nat.div x1 x0) x0) = (Nat.mul (Nat.div x1 x0) x0)) /\ (((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1) /\ (Peano.le (Nat.mul (Nat.div x1 x0) x0) (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))))) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1.
Definition term52 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 (Nat.div x1 x0)) x1.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term293 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.le x1 x2)).
Definition term101 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term105 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.div x2 x1) (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 (Nat.div x2 x1)) x2).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term214 (x0 : nat) := (fun y0 : nat => Peano.le x0 y0) (NUMERAL 0).
Definition term150 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term55 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term174 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1) /\ ((fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1).
Definition term142 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x0 (Nat.div x2 x1)) (Nat.mul x1 (Nat.div x2 x1))) /\ (Peano.le (Nat.mul x1 (Nat.div x2 x1)) x2).
Definition term306 (x0 : nat) (x1 : nat) := (~ (Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((Nat.div x1 x2) = (NUMERAL 0)).
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term216 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term159 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term138 := (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term108 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term126 (x0 : nat) (x1 : nat) := or (Peano.le x0 (S x1)).
Definition term265 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term145 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term164 := forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.div x1 x0) (Nat.div x1 x2).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term233 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term186 (x0 : nat) := (forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ (forall y0 : nat, (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term165 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.le x0 x1))) -> Peano.le x2 x3.
Definition term204 := and (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))).
Definition term24 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.le x0 x1).
Definition term180 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0))).
Definition term303 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = x0) /\ (Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term99 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term185 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term205 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0.
Definition term200 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0.
Definition term275 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (Nat.div x0 x1) x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term94 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term210 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term195 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term193 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term299 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3)).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term297 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term124 (x0 : nat) (x1 : nat) := (~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)).
Definition term314 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y0 x0)) -> Peano.le (Nat.div x1 x0) (Nat.div x1 y0).
Definition term290 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term285 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term169 (x0 : nat) := fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0))).
Definition term295 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.le x1 x2))).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term173 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term106 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term245 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term18 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term203 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0).
Definition term181 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0).
Definition term160 := and (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term237 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term194 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0).
Definition term34 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term133 (x0 : nat) := fun y0 : nat => ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term227 (x0 : nat) := imp (~ (~ (Peano.le x0 (NUMERAL 0)))).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term286 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term17 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term287 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term188 := forall y0 : nat, (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term62 (x0 : nat) (x1 : nat) := (~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1)) -> False.
Definition term271 (x0 : nat) (x1 : nat) := (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (x1 = x1).
Definition term172 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1).
Definition term312 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 (Nat.div x2 x1)) y0) /\ (Peano.le y0 x2).
Definition term114 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term117 (x0 : nat) (x1 : nat) := and ((x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))).
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term63 (x0 : nat) (x1 : nat) := ~ (((~ (x0 = (NUMERAL 0))) -> (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0)) -> Peano.le (Nat.mul (Nat.div x1 x0) x0) x1).
Definition term109 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term221 (x0 : nat) := @eq Prop ((~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term116 (x0 : nat) (x1 : nat) := and ((~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term264 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term123 (x0 : nat) (x1 : nat) := ~ ((x0 = (S x1)) \/ (Peano.le x0 x1)).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term1 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term252 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term206 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0.
Definition term201 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0.
Definition term97 := fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term104 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term98 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (~ (((~ (x1 = (NUMERAL 0))) -> (x2 = (Nat.add (Nat.mul (Nat.div x2 x1) x1) (Nat.modulo x2 x1))) /\ (Peano.lt (Nat.modulo x2 x1) x1)) -> Peano.le (Nat.mul (Nat.div x2 x1) x1) x2)) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term192 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term191 := fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1))).
Definition term135 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term102 := fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term87 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (((~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) -> Peano.le (Nat.mul (Nat.div x0 y0) y0) x0)) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> ~ (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)).
Definition term86 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (((~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) -> Peano.le (Nat.mul (Nat.div x0 y0) y0) x0)) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False.
Definition term50 (x0 : nat) (x1 : nat) := True \/ ((Nat.div x0 x1) = (NUMERAL 0)).
Definition term226 (x0 : nat) := ~ (~ (Peano.le x0 (NUMERAL 0))).
Definition term127 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term134 (x0 : nat) := forall y0 : nat, ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term122 := forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term91 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (~ (((~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> Peano.le (Nat.mul (Nat.div y0 y1) y1) y0)) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> ~ (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)).
Definition term90 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (~ (((~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> Peano.le (Nat.mul (Nat.div y0 y1) y1) y0)) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> (forall y3 : nat, forall y4 : nat, Peano.le y3 (Nat.add y3 y4)) -> False.
Definition term121 := fun y0 : nat => ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term209 := ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term274 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
