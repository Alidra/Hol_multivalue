Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term136 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.lt x1 x2).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x1 x0) /\ (~ (Peano.lt x1 x2))).
Definition term205 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term97 (x0 : nat -> Prop) := ~ (all x0).
Definition term268 := (~ False) -> False.
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 y0))) \/ (Peano.lt x1 y0)) x2.
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x1 x0)) \/ (Peano.lt x1 x2))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 (Nat.add y0 (NUMERAL (BIT1 0)))))) x2.
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.lt x1 x2))).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2).
Definition term197 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term172 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term147 := forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term8 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term244 (x0 : Prop) := ~ (~ x0).
Definition term217 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y2))) \/ (Peano.lt y0 y2)) x0.
Definition term114 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0)) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.div y1 y0) y2) = (Peano.lt y1 (Nat.mul y0 (Nat.add y2 (NUMERAL (BIT1 0)))))) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term80 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)).
Definition term183 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term155 := fun y0 : nat => ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term233 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term262 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (Peano.lt (NUMERAL 0) x0).
Definition term78 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.lt x1 x2).
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) /\ (~ (Peano.lt x1 x2)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> (Peano.le (Nat.div x0 x1) x2) = x3) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> x3).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term74 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term139 (x0 : nat) := ((Peano.lt (NUMERAL 0) x0) \/ (~ (~ (x0 = (NUMERAL 0))))) /\ ((~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term44 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term63 (x0 : Prop) := (~ x0) -> False.
Definition term198 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term173 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term148 := (forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term216 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)).
Definition term169 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) /\ ((~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term127 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 y0))) \/ (Peano.lt x1 y0).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (Peano.le x1 x0)) \/ (Peano.lt x1 x2)).
Definition term109 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0)) x1).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2)))) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> (Peano.le (Nat.div x0 x1) x2) = x3) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> x3).
Definition term53 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.le (Nat.div x0 x1) y0.
Definition term45 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) x1.
Definition term192 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term187 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term164 := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term159 := forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0.
Definition term138 (x0 : nat) := and ((Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0))).
Definition term134 (x0 : nat) := or (Peano.lt (NUMERAL 0) x0).
Definition term140 (x0 : nat) := ((Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0))) /\ ((~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term238 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term145 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term99 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1)).
Definition term195 := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ (forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)).
Definition term106 (x0 : nat) := ~ (forall y0 : nat, forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0)).
Definition term71 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)).
Definition term65 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0)).
Definition term11 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term160 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0)).
Definition term175 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x1 x0)) \/ (Peano.lt x1 x2)).
Definition term226 (x0 : Prop) := (~ x0) -> x0.
Definition term104 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) /\ (~ (Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1))).
Definition term256 (x0 : nat) (x1 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) x1).
Definition term267 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term153 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term241 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term111 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) /\ (~ (Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0))).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.lt x0 x2)) \/ (Peano.lt x1 x2))).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)).
Definition term77 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term207 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ (forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1))).
Definition term206 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0)).
Definition term185 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) /\ ((~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0))).
Definition term184 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0)).
Definition term157 := @eq Prop (forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))))).
Definition term156 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0)).
Definition term84 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = y0) -> (y0 -> (Peano.le (Nat.div x0 x1) x2) = y1) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (y0 -> y1)) x3.
Definition term133 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x0) \/ (~ (Peano.le x1 x2)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term265 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) -> x0 = (NUMERAL 0).
Definition term218 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 y1))) \/ (Peano.lt x0 y1)) x1.
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0)) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 (Nat.add y1 (NUMERAL (BIT1 0)))))) x1.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (Peano.lt x1 x2)).
Definition term26 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt x1 x0) \/ ((~ (Peano.lt x2 x0)) \/ (~ (Peano.le x1 x2)))).
Definition term200 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1).
Definition term128 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 y1))) \/ (Peano.lt x0 y1).
Definition term91 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1.
Definition term85 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term55 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.le (Nat.div y0 x0) y1.
Definition term167 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (Nat.add x0 x1)) \/ (~ (Peano.lt (NUMERAL 0) x1))) /\ ((~ (Peano.lt x0 (Nat.add x0 x1))) \/ (Peano.lt (NUMERAL 0) x1)).
Definition term152 (x0 : nat) := and ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) x0).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x0) \/ ((~ (Peano.lt x2 x0)) \/ (~ (Peano.le x1 x2))).
Definition term10 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term29 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term154 (x0 : nat) := ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) x0) /\ ((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) x0).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.lt x1 x2)).
Definition term221 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term186 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term163 := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.lt x0 x2)) \/ (Peano.lt x1 x2)).
Definition term255 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) x1)) -> ~ (Peano.lt (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) x1)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2.
Definition term70 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)) -> ~ (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)).
Definition term266 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 (Nat.add y0 (NUMERAL (BIT1 0))))).
Definition term263 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term69 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term73 := imp (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))).
Definition term190 (x0 : nat) := and (forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))).
Definition term162 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term67 := ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term261 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) x1))) -> ~ (Peano.lt (NUMERAL 0) x1).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x2))) \/ (Peano.lt x1 x2).
Definition term75 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = x3) -> (x3 -> (Peano.le (Nat.div x0 x1) x2) = x4) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (x3 -> x4).
Definition term158 := fun y0 : nat => (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0.
Definition term240 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term215 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1).
Definition term210 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1)).
Definition term171 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ ((~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)).
Definition term131 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y2))) \/ (Peano.lt y0 y2).
Definition term129 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 y1))) \/ (Peano.lt x0 y1).
Definition term94 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term92 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1.
Definition term72 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1).
Definition term62 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0).
Definition term61 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.le (Nat.div y1 y0) y2.
Definition term58 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0).
Definition term57 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.le (Nat.div y0 x0) y1.
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 (Nat.add y1 (NUMERAL (BIT1 0))))).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ ((Peano.lt x1 x0) \/ (~ (Peano.le x1 x2))).
Definition term86 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1)) x2).
Definition term204 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) x0).
Definition term68 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term117 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) /\ (~ (Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))).
Definition term188 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term179 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (Nat.add x0 x1)) \/ (~ (Peano.lt (NUMERAL 0) x1))).
Definition term126 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 y0))) \/ (Peano.lt x1 y0).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> (Peano.le (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2))) -> (((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> Peano.le (Nat.div x0 x2) x1) = (((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.lt x1 x2))).
Definition term64 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> False.
Definition term116 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.le y2 (Nat.mul y1 y3))) -> Peano.lt y2 (Nat.add (Nat.mul y1 y3) y1)) y0).
Definition term110 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul x0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul x0 y2) x0)) y0).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le x0 (Nat.mul x1 x2).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = x3) -> (x3 -> (Peano.le (Nat.div x0 x1) x2) = y0) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (x3 -> y0).
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term66 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) -> False.
Definition term182 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) x1) /\ ((fun y0 : nat => (~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0)) x1).
Definition term146 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term52 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1).
Definition term105 (x0 : nat) (x1 : nat) := exists y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) /\ (~ (Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1))).
Definition term165 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term176 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) x1.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = y0) -> (y0 -> (Peano.le (Nat.div x0 x1) x2) = y1) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (y0 -> y1).
Definition term31 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term246 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term141 := fun y0 : nat => ((Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term9 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term90 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0.
Definition term42 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term174 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0)).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x0 x1)) \/ (Peano.lt x0 x2))) -> ~ (Peano.lt x1 x2).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) = x3) -> (x3 -> (Peano.le (Nat.div x0 x1) x2) = y0) -> (((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2))) -> Peano.le (Nat.div x0 x1) x2) = (x3 -> y0)) x4.
Definition term194 (x0 : nat) := (forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) /\ (forall y0 : nat, (~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term166 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) /\ (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 (Nat.mul x2 x1)) /\ (~ (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2))).
Definition term212 := and (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))).
Definition term115 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0)) x0).
Definition term222 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term137 (x0 : nat) := and ((Peano.lt (NUMERAL 0) x0) \/ (~ (~ (x0 = (NUMERAL 0))))).
Definition term51 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.le (Nat.div x0 x1) y0.
Definition term87 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term12 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term213 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0.
Definition term208 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term203 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) x0.
Definition term201 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) x0.
Definition term135 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) \/ (~ (~ (x0 = (NUMERAL 0)))).
Definition term245 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.div x0 x1) x2.
Definition term177 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.add x0 x1)) \/ (~ (Peano.lt (NUMERAL 0) x1)).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.lt x1 x2)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.lt x0 x2)) -> Peano.lt x1 x2.
Definition term83 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> (Peano.le (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)).
Definition term113 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.le y2 (Nat.mul y1 y3))) -> Peano.lt y2 (Nat.add (Nat.mul y1 y3) y1)) y0).
Definition term107 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul x0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul x0 y2) x0)) y0).
Definition term100 (x0 : nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y1))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y1) x1)) y0).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term254 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) x1)).
Definition term191 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 (Nat.add x0 y1))) \/ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term211 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0).
Definition term189 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (Nat.add x0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) y0).
Definition term161 := and (forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) \/ (y1 = (NUMERAL 0))) y0).
Definition term202 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) x0).
Definition term142 := forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term40 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) /\ (~ (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2))).
Definition term81 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.add x0 x1).
Definition term260 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (Nat.add x0 x1))) -> ~ (Peano.lt (NUMERAL 0) x1).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le x0 (Nat.mul x1 x2)).
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (~ (Peano.lt x0 x2))) -> ~ (Peano.lt x1 x2).
Definition term258 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) x0).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)).
Definition term181 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (Nat.add x0 x1))) \/ (Peano.lt (NUMERAL 0) x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term199 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1)).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term118 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) /\ (~ (Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))).
Definition term112 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) /\ (~ (Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0))).
Definition term196 := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ (forall y1 : nat, (~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)).
Definition term54 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1).
Definition term178 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) x1).
Definition term103 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y1))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y1) x1)) y0).
Definition term149 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0)).
Definition term151 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) \/ (y0 = (NUMERAL 0))) x0.
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.mul x1 x2).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term257 (x0 : nat) (x1 : nat) := (~ (Peano.lt (NUMERAL 0) x1)) \/ (Peano.lt x0 (Nat.add x0 x1)).
Definition term264 (x0 : nat) := @eq Prop ((Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0))).
Definition term259 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x0 (Nat.add x0 x1)) \/ (~ (Peano.lt (NUMERAL 0) x1))).
Definition term132 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x2 x1))) -> Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2).
Definition term193 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0).
Definition term214 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (Nat.add y1 y2))) \/ (Peano.lt (NUMERAL 0) y2)) y0.
Definition term209 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (Nat.add y1 y2)) \/ (~ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term76 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2).
Definition term7 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 y0))) -> Peano.lt x0 (Nat.add (Nat.mul x1 y0) x1)) x2.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) /\ (Peano.le x0 (Nat.mul x1 x2)).
Definition term82 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term98 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term150 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term41 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term170 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (Nat.add y0 y1)) \/ (~ (Peano.lt (NUMERAL 0) y1))) /\ ((~ (Peano.lt y0 (Nat.add y0 y1))) \/ (Peano.lt (NUMERAL 0) y1)).
Definition term56 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.le y0 (Nat.mul x0 y1))) -> Peano.lt y0 (Nat.add (Nat.mul x0 y1) x0).
Definition term168 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (Nat.add x0 y0)) \/ (~ (Peano.lt (NUMERAL 0) y0))) /\ ((~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term247 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term43 := NUMERAL (BIT1 0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.lt x0 x2))) \/ (Peano.lt x1 x2).
Definition term89 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0.
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 (Nat.mul x2 x1)) /\ (~ (Peano.lt x0 (Nat.add (Nat.mul x2 x1) x2)))) -> ~ (Peano.lt (Nat.mul x2 x1) (Nat.add (Nat.mul x2 x1) x2)).
Definition term79 := imp (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0))).
Definition term229 (x0 : Prop) := x0 -> ~ x0.
Definition term130 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y2))) \/ (Peano.lt y0 y2).
Definition term93 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term60 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.lt y1 (Nat.add (Nat.mul y0 y2) y0).
Definition term59 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y1 (Nat.mul y0 y2))) -> Peano.le (Nat.div y1 y0) y2.
Definition term180 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 (Nat.add x0 y0))) \/ (Peano.lt (NUMERAL 0) y0)) x1.
