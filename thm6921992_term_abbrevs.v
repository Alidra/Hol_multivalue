Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term238 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term27 (x0 : nat) := fun y0 : nat => ((Nat.add x0 y0) = y0) /\ ((Nat.add y0 x0) = y0).
Definition term266 (x0 : nat) := ((Nat.add (NUMERAL 0) x0) = x0) -> False.
Definition term43 (x0 : nat) := @eq Prop ((fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y1) /\ ((Nat.add y1 y0) = y1)) x0).
Definition term83 (x0 : nat -> Prop) := ~ (all x0).
Definition term264 := (~ False) -> False.
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term55 (x0 : nat) := @eq Prop ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)).
Definition term19 (x0 : nat) := fun y0 : nat => (Nat.add y0 x0) = y0.
Definition term16 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.add x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.add y1 x0) = y1) y0).
Definition term53 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term252 (x0 : Prop) := ~ (~ x0).
Definition term127 := fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0))).
Definition term215 := fun y0 : nat => exists y1 : nat, (((forall y2 : nat, (Nat.add y0 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y0) = y2)) /\ (~ (y0 = (NUMERAL 0)))) \/ (((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term184 := fun y0 : nat => exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)).
Definition term140 := or (exists y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term39 (x0 : nat) := (forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0).
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term114 (x0 : nat) := ~ (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) = (x0 = (NUMERAL 0))).
Definition term144 := (exists y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (exists y0 : nat, ((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term222 (x0 : nat) := ~ ((Nat.add (NUMERAL 0) x0) = x0).
Definition term183 (x0 : nat) := exists y0 : nat, ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)).
Definition term143 := exists y0 : nat, ((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)).
Definition term4 (x0 : Prop) := (~ x0) -> False.
Definition term111 (x0 : nat) := or (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))).
Definition term17 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = y1) y0).
Definition term73 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term260 (x0 : nat) := ((Nat.add x0 (NUMERAL 0)) = x0) /\ ((Nat.add x0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term170 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0) /\ (x0 = (NUMERAL 0)).
Definition term234 (x0 : nat) := (~ ((Nat.add x0 (NUMERAL 0)) = (NUMERAL 0))) -> (Nat.add x0 (NUMERAL 0)) = (NUMERAL 0).
Definition term8 := (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False.
Definition term202 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term214 (x0 : nat) := exists y0 : nat, (((forall y1 : nat, (Nat.add x0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 x0) = y1)) /\ (~ (x0 = (NUMERAL 0)))) \/ (((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term120 := exists y0 : nat, (((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term180 (x0 : nat) (x1 : nat) := ((~ ((Nat.add x1 x0) = x0)) \/ (~ ((Nat.add x0 x1) = x0))) /\ (x1 = (NUMERAL 0)).
Definition term161 (x0 : nat) := fun y0 : nat => (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0)).
Definition term245 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term28 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = y0) /\ ((Nat.add y0 x0) = y0).
Definition term14 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term255 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term2 := (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0))) -> (@ε nat (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y1) /\ ((Nat.add y1 y0) = y1))) = (NUMERAL 0).
Definition term209 (x0 : nat) := @eq Prop ((((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ (exists y0 : nat, ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)))).
Definition term208 (x0 : nat) := @eq Prop ((((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0)).
Definition term58 := ~ (forall y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0))).
Definition term48 := ~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0))).
Definition term7 := ~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0))).
Definition term211 (x0 : nat) (x1 : nat) := (((forall y0 : nat, (Nat.add x1 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x1) = y0)) /\ (~ (x1 = (NUMERAL 0)))) \/ (((~ ((Nat.add x1 x0) = x0)) \/ (~ ((Nat.add x0 x1) = x0))) /\ (x1 = (NUMERAL 0))).
Definition term217 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term21 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Nat.add x0 y0) = y0) x1).
Definition term52 := ~ ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))).
Definition term230 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.add x1 x0) = x1)).
Definition term224 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.add x0 x1) = x1)).
Definition term129 (x0 : nat) := (fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) x0.
Definition term233 (x0 : Prop) := (~ x0) -> x0.
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term197 := fun y0 : nat => (((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term205 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))) x1.
Definition term263 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term249 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term189 (x0 : nat) := (fun y0 : nat => exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))) x0.
Definition term102 (x0 : nat) := (exists y0 : nat, ~ ((Nat.add x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.add y0 x0) = y0)).
Definition term174 (x0 : nat) := and (exists y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0).
Definition term25 (x0 : nat) (x1 : nat) := ((Nat.add x0 x1) = x1) /\ ((Nat.add x1 x0) = x1).
Definition term69 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term99 (x0 : nat) := or (~ (forall y0 : nat, (Nat.add x0 y0) = y0)).
Definition term30 (x0 : nat) := @eq Prop (forall y0 : nat, ((Nat.add x0 y0) = y0) /\ ((Nat.add y0 x0) = y0)).
Definition term29 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Nat.add x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.add y1 x0) = y1) y0)).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term75 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term74 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term190 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0.
Definition term128 := fun y0 : nat => ((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)).
Definition term241 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term132 (x0 : nat) := ((fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) x0) \/ ((fun y0 : nat => ((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))) x0).
Definition term94 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Nat.add y0 x0) = y0) x1).
Definition term87 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Nat.add x0 y0) = y0) x1).
Definition term104 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term3 := fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y1) /\ ((Nat.add y1 y0) = y1).
Definition term22 (x0 : nat) (x1 : nat) := and ((Nat.add x0 x1) = x1).
Definition term169 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0) /\ (x0 = (NUMERAL 0)).
Definition term135 := @eq Prop (exists y0 : nat, (((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)))).
Definition term134 := @eq Prop (exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0)).
Definition term117 (x0 : nat) := ~ ((fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0))) x0).
Definition term36 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.add y1 x0) = y1) y0.
Definition term31 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.add x0 y1) = y1) y0.
Definition term153 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0.
Definition term149 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0.
Definition term100 (x0 : nat) := or (exists y0 : nat, ~ ((Nat.add x0 y0) = y0)).
Definition term76 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term179 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ ((Nat.add x1 y0) = y0)) \/ (~ ((Nat.add y0 x1) = y0))) x0) /\ (x1 = (NUMERAL 0)).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term109 (x0 : nat) := and ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)).
Definition term172 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0.
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term187 := (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term145 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0).
Definition term126 := (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term136 := fun y0 : nat => (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0.
Definition term262 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term56 := fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0)).
Definition term60 := (~ (forall y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))).
Definition term54 := (~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) = (y0 = x1)) -> (@ε a0 x0) = x1.
Definition term79 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term62 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term200 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term82 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term77 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term35 (x0 : nat) := and (forall y0 : nat, (Nat.add x0 y0) = y0).
Definition term248 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term71 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term66 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term42 (x0 : nat) := (fun y0 : nat => (forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) x0.
Definition term199 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term156 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => ~ ((Nat.add x0 y0) = y0)) x1).
Definition term113 (x0 : nat) := (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ (((exists y0 : nat, ~ ((Nat.add x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term204 (x0 : nat) := exists y0 : nat, (((forall y1 : nat, (Nat.add x0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 x0) = y1)) /\ (~ (x0 = (NUMERAL 0)))) \/ ((fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term116 (x0 : nat) := (fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0))) x0.
Definition term37 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = y1) y0.
Definition term32 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = y1) y0.
Definition term186 := (exists y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term188 := exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term146 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0) \/ ((fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0).
Definition term125 := exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term178 (x0 : nat) (x1 : nat) := and ((~ ((Nat.add x0 x1) = x1)) \/ (~ ((Nat.add x1 x0) = x1))).
Definition term81 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term38 (x0 : nat) := forall y0 : nat, (Nat.add y0 x0) = y0.
Definition term33 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = y0.
Definition term47 := forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)).
Definition term5 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)).
Definition term218 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term105 (x0 : nat) := and (~ ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0))).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term168 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term182 (x0 : nat) := fun y0 : nat => ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)).
Definition term213 (x0 : nat) := fun y0 : nat => (((forall y1 : nat, (Nat.add x0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 x0) = y1)) /\ (~ (x0 = (NUMERAL 0)))) \/ (((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term6 := (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> False.
Definition term130 (x0 : nat) := or ((fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) x0).
Definition term160 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0) \/ ((fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0).
Definition term162 (x0 : nat) := exists y0 : nat, (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0)).
Definition term203 (x0 : nat) := (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0).
Definition term15 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term181 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0) /\ (x0 = (NUMERAL 0)).
Definition term228 (x0 : nat) := ~ ((Nat.add x0 (NUMERAL 0)) = x0).
Definition term138 := exists y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0))).
Definition term131 (x0 : nat) := (fun y0 : nat => ((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))) x0.
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term207 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0.
Definition term173 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0.
Definition term142 := exists y0 : nat, (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0.
Definition term137 := exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0.
Definition term18 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = y0.
Definition term107 (x0 : nat) := (~ ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)).
Definition term158 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ~ ((Nat.add x0 y0) = y0)) x1) \/ ((fun y0 : nat => ~ ((Nat.add y0 x0) = y0)) x1).
Definition term103 (x0 : nat) := ~ ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)).
Definition term254 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term78 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term267 (x0 : nat) := ((Nat.add x0 (NUMERAL 0)) = x0) -> False.
Definition term63 (x0 : nat) := fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
Definition term106 (x0 : nat) := and ((exists y0 : nat, ~ ((Nat.add x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.add y0 x0) = y0))).
Definition term229 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.add x0 y0) = x0)) x1).
Definition term223 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.add y0 x0) = x0)) x1).
Definition term72 := and (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))).
Definition term196 := fun y0 : nat => ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term232 (x0 : nat) := (~ ((Nat.add x0 (NUMERAL 0)) = x0)) -> (Nat.add x0 (NUMERAL 0)) = x0.
Definition term51 := ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False.
Definition term44 (x0 : nat) := @eq Prop ((fun y0 : nat => (forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) x0).
Definition term167 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term198 := exists y0 : nat, (((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term261 (x0 : nat) := (((Nat.add x0 (NUMERAL 0)) = x0) /\ ((Nat.add x0 (NUMERAL 0)) = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term225 (x0 : nat) := fun y0 : nat => ~ ((Nat.add x0 y0) = x0).
Definition term219 (x0 : nat) := fun y0 : nat => ~ ((Nat.add y0 x0) = x0).
Definition term265 (x0 : nat) := (~ ((Nat.add (NUMERAL 0) x0) = x0)) -> (Nat.add (NUMERAL 0) x0) = x0.
Definition term110 (x0 : nat) := ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0))).
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y1) /\ ((Nat.add y1 y0) = y1)) x0.
Definition term212 (x0 : nat) := fun y0 : nat => (((forall y1 : nat, (Nat.add x0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 x0) = y1)) /\ (~ (x0 = (NUMERAL 0)))) \/ ((fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0).
Definition term163 (x0 : nat) := and (exists y0 : nat, (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))).
Definition term96 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.add y1 x0) = y1) y0).
Definition term89 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.add x0 y1) = y1) y0).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term115 := exists y0 : nat, ~ ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) = (y1 = (NUMERAL 0))) y0).
Definition term93 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Nat.add y1 x0) = y1) y0).
Definition term86 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Nat.add x0 y1) = y1) y0).
Definition term57 := forall y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0)).
Definition term61 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term226 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.add x0 y0) = x0)) x1.
Definition term220 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.add y0 x0) = x0)) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add y0 x0) = y0) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = y0) x1.
Definition term235 (x0 : nat) := ~ ((Nat.add x0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term206 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) /\ (x0 = (NUMERAL 0))) y0.
Definition term141 := fun y0 : nat => (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0.
Definition term24 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.add x0 y0) = y0) x1) /\ ((fun y0 : nat => (Nat.add y0 x0) = y0) x1).
Definition term68 (x0 : nat) := fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term34 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = y1) y0).
Definition term108 (x0 : nat) := ((exists y0 : nat, ~ ((Nat.add x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)).
Definition term101 (x0 : nat) := (~ (forall y0 : nat, (Nat.add x0 y0) = y0)) \/ (~ (forall y0 : nat, (Nat.add y0 x0) = y0)).
Definition term97 (x0 : nat) := fun y0 : nat => ~ ((Nat.add y0 x0) = y0).
Definition term90 (x0 : nat) := fun y0 : nat => ~ ((Nat.add x0 y0) = y0).
Definition term152 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0.
Definition term148 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0.
Definition term98 (x0 : nat) := exists y0 : nat, ~ ((Nat.add y0 x0) = y0).
Definition term91 (x0 : nat) := exists y0 : nat, ~ ((Nat.add x0 y0) = y0).
Definition term70 := fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term65 := fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term157 (x0 : nat) (x1 : nat) := or (~ ((Nat.add x0 x1) = x1)).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term1 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (x0 y0) = (y0 = x1)) -> (@ε nat x0) = x1.
Definition term191 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0.
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.add y0 x0) = y0)) x1.
Definition term147 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.add x0 y0) = y0)) x1.
Definition term216 := exists y0 : nat, exists y1 : nat, (((forall y2 : nat, (Nat.add y0 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y0) = y2)) /\ (~ (y0 = (NUMERAL 0)))) \/ (((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term185 := exists y0 : nat, exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)).
Definition term10 := (((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False.
Definition term80 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term112 (x0 : nat) := (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ ((~ ((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term123 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term177 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) x1).
Definition term118 := fun y0 : nat => ~ ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) = (y1 = (NUMERAL 0))) y0).
Definition term40 := fun y0 : nat => (forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1).
Definition term176 (x0 : nat) := @eq Prop ((exists y0 : nat, (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term175 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 y1) = y1)) \/ (~ ((Nat.add y1 x0) = y1))) y0) /\ (x0 = (NUMERAL 0))).
Definition term210 (x0 : nat) (x1 : nat) := (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ ((fun y0 : nat => ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))) x1).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term133 := fun y0 : nat => ((fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.add y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0).
Definition term150 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0).
Definition term139 := or (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0).
Definition term92 (x0 : nat) := ~ (forall y0 : nat, (Nat.add y0 x0) = y0).
Definition term85 (x0 : nat) := ~ (forall y0 : nat, (Nat.add x0 y0) = y0).
Definition term46 := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)).
Definition term45 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)).
Definition term253 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term11 := (((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> ((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False.
Definition term119 := fun y0 : nat => (((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (((exists y1 : nat, ~ ((Nat.add y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))).
Definition term239 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term95 (x0 : nat) (x1 : nat) := ~ ((Nat.add x1 x0) = x1).
Definition term88 (x0 : nat) (x1 : nat) := ~ ((Nat.add x0 x1) = x1).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term159 (x0 : nat) (x1 : nat) := (~ ((Nat.add x0 x1) = x1)) \/ (~ ((Nat.add x1 x0) = x1)).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term84 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term195 (x0 : nat) := (((forall y0 : nat, (Nat.add x0 y0) = y0) /\ (forall y0 : nat, (Nat.add y0 x0) = y0)) /\ (~ (x0 = (NUMERAL 0)))) \/ (exists y0 : nat, ((~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0))).
Definition term201 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term164 (x0 : nat) := (exists y0 : nat, (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) /\ (x0 = (NUMERAL 0)).
Definition term268 := @ε nat (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y1) /\ ((Nat.add y1 y0) = y1)).
Definition term67 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term227 (x0 : nat) := (fun y0 : nat => ~ ((Nat.add x0 y0) = x0)) (NUMERAL 0).
Definition term221 (x0 : nat) := (fun y0 : nat => ~ ((Nat.add y0 x0) = x0)) (NUMERAL 0).
Definition term171 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.add x0 y0) = y0)) \/ (~ ((Nat.add y0 x0) = y0))) x1.
Definition term124 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term59 := imp (~ (forall y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) = (y0 = (NUMERAL 0)))).
Definition term50 := imp (~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))).
Definition term49 := imp (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))).
Definition term194 (x0 : nat) := ((fun y0 : nat => ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) x0) \/ ((fun y0 : nat => exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0))) x0).
Definition term26 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.add x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.add y1 x0) = y1) y0).
Definition term9 := ((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add y1 y2) = y2) /\ ((Nat.add y2 y1) = y2)) y0) = (y0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> False.
Definition term193 := @eq Prop ((exists y0 : nat, ((forall y1 : nat, (Nat.add y0 y1) = y1) /\ (forall y1 : nat, (Nat.add y1 y0) = y1)) /\ (~ (y0 = (NUMERAL 0)))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.add y0 y1) = y1)) \/ (~ ((Nat.add y1 y0) = y1))) /\ (y0 = (NUMERAL 0)))).
Definition term192 := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.add y1 y2) = y2) /\ (forall y2 : nat, (Nat.add y2 y1) = y2)) /\ (~ (y1 = (NUMERAL 0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.add y1 y2) = y2)) \/ (~ ((Nat.add y2 y1) = y2))) /\ (y1 = (NUMERAL 0))) y0)).
Definition term155 (x0 : nat) := @eq Prop ((exists y0 : nat, ~ ((Nat.add x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.add y0 x0) = y0))).
Definition term154 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ ((Nat.add x0 y1) = y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ ((Nat.add y1 x0) = y1)) y0)).
Definition term64 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
