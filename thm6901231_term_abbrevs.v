Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term242 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0))))).
Definition term28 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = y0) /\ ((Nat.mul y0 x0) = y0).
Definition term334 (x0 : nat) := ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0) -> False.
Definition term44 (x0 : nat) := @eq Prop ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = y1) /\ ((Nat.mul y1 y0) = y1)) x0).
Definition term148 := fun y0 : nat => ((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term281 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term103 (x0 : nat -> Prop) := ~ (all x0).
Definition term332 := (~ False) -> False.
Definition term59 (x0 : nat) := @eq Prop ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)).
Definition term273 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term251 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term17 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.mul x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.mul y1 x0) = y1) y0).
Definition term57 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term244 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))))).
Definition term88 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term96 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term324 (x0 : Prop) := ~ (~ x0).
Definition term189 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term255 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1.
Definition term319 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL (BIT1 0))) \/ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))).
Definition term243 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))))).
Definition term133 (x0 : nat) := (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (((exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term225 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))) x1.
Definition term259 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term130 (x0 : nat) := ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term323 (x0 : nat) (x1 : nat) := (~ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))))) -> x1 = (NUMERAL (BIT1 0)).
Definition term329 (x0 : nat) := ((Nat.mul (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))) -> x0 = (NUMERAL (BIT1 0)).
Definition term54 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term124 (x0 : nat) := ~ (x0 = (NUMERAL (BIT1 0))).
Definition term235 := fun y0 : nat => exists y1 : nat, (((forall y2 : nat, (Nat.mul y0 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y0) = y2)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term204 := fun y0 : nat => exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term160 := or (exists y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term40 (x0 : nat) := (forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0).
Definition term164 := (exists y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, ((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term307 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0).
Definition term53 := ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term239 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term68 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term5 (x0 : Prop) := (~ x0) -> False.
Definition term274 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term252 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term18 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Nat.mul x0 y1) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.mul y1 x0) = y1) y0).
Definition term292 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term78 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term85 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term131 (x0 : nat) := or (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))).
Definition term300 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term268 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term263 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0.
Definition term222 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term234 (x0 : nat) := exists y0 : nat, (((forall y1 : nat, (Nat.mul x0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 x0) = y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term140 := exists y0 : nat, (((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term181 (x0 : nat) := fun y0 : nat => (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0)).
Definition term322 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term29 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = y0) /\ ((Nat.mul y0 x0) = y0).
Definition term15 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term229 (x0 : nat) := @eq Prop ((((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))))).
Definition term228 (x0 : nat) := @eq Prop ((((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0)).
Definition term62 := ~ (forall y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0)))).
Definition term49 := ~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0)))).
Definition term8 := ~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0)))).
Definition term271 := fun y0 : nat => (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term302 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term22 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Nat.mul x0 y0) = y0) x1).
Definition term315 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.mul x1 x0) = x1)).
Definition term309 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.mul x0 x1) = x1)).
Definition term149 (x0 : nat) := (fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0.
Definition term318 (x0 : Prop) := (~ x0) -> x0.
Definition term217 := fun y0 : nat => (((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term10 := ((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term209 (x0 : nat) := (fun y0 : nat => exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term122 (x0 : nat) := (exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.mul y0 x0) = y0)).
Definition term194 (x0 : nat) := and (exists y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0).
Definition term26 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = x1) /\ ((Nat.mul x1 x0) = x1).
Definition term203 (x0 : nat) := exists y0 : nat, ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term163 := exists y0 : nat, ((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term119 (x0 : nat) := or (~ (forall y0 : nat, (Nat.mul x0 y0) = y0)).
Definition term283 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))))).
Definition term282 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0)).
Definition term261 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))))).
Definition term260 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0)).
Definition term31 (x0 : nat) := @eq Prop (forall y0 : nat, ((Nat.mul x0 y0) = y0) /\ ((Nat.mul y0 x0) = y0)).
Definition term30 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Nat.mul x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.mul y1 x0) = y1) y0)).
Definition term240 (x0 : nat) (x1 : nat) := or ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term80 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term210 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term147 := fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term152 (x0 : nat) := ((fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0) \/ ((fun y0 : nat => ((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term100 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term98 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term71 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term114 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Nat.mul y0 x0) = y0) x1).
Definition term107 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Nat.mul x0 y0) = y0) x1).
Definition term303 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0))).
Definition term75 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term3 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = y1) /\ ((Nat.mul y1 y0) = y1).
Definition term128 (x0 : nat) := ((exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term65 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term23 (x0 : nat) (x1 : nat) := and ((Nat.mul x0 x1) = x1).
Definition term155 := @eq Prop (exists y0 : nat, (((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term154 := @eq Prop (exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0)).
Definition term137 (x0 : nat) := ~ ((fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term37 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.mul y1 x0) = y1) y0.
Definition term32 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.mul x0 y1) = y1) y0.
Definition term173 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0.
Definition term169 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0.
Definition term151 (x0 : nat) := (fun y0 : nat => ((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term120 (x0 : nat) := or (exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)).
Definition term81 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term129 (x0 : nat) := and ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)).
Definition term192 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0.
Definition term254 (x0 : nat) := fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term207 := (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term165 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0).
Definition term146 := (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term156 := fun y0 : nat => (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term233 (x0 : nat) := fun y0 : nat => (((forall y1 : nat, (Nat.mul x0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 x0) = y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term266 (x0 : nat) := and (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))).
Definition term97 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term92 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) = (y0 = x1)) -> (@ε a0 x0) = x1.
Definition term220 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term267 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term262 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0.
Definition term327 (x0 : nat) (x1 : nat) := imp ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term87 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term82 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term36 (x0 : nat) := and (forall y0 : nat, (Nat.mul x0 y0) = y0).
Definition term246 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term269 (x0 : nat) := forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term298 := forall y0 : nat, forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0)))).
Definition term291 := forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term286 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0))))).
Definition term250 := forall y0 : nat, forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term102 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term76 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term70 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term61 := forall y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0))).
Definition term43 (x0 : nat) := (fun y0 : nat => (forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) x0.
Definition term219 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term176 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => ~ ((Nat.mul x0 y0) = y0)) x1).
Definition term20 (x0 : nat) := fun y0 : nat => (Nat.mul y0 x0) = y0.
Definition term224 (x0 : nat) := exists y0 : nat, (((forall y1 : nat, (Nat.mul x0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 x0) = y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0).
Definition term280 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term238 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))).
Definition term38 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.mul y1 x0) = y1) y0.
Definition term33 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.mul x0 y1) = y1) y0.
Definition term206 := (exists y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term208 := exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term166 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0) \/ ((fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0).
Definition term145 := exists y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term198 (x0 : nat) (x1 : nat) := and ((~ ((Nat.mul x0 x1) = x1)) \/ (~ ((Nat.mul x1 x0) = x1))).
Definition term127 (x0 : nat) := (~ ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term11 := (((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term231 (x0 : nat) (x1 : nat) := (((forall y0 : nat, (Nat.mul x1 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x1) = y0)) /\ (~ (x1 = (NUMERAL (BIT1 0))))) \/ (((~ ((Nat.mul x1 x0) = x0)) \/ (~ ((Nat.mul x0 x1) = x0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term326 (x0 : nat) (x1 : nat) := imp (~ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))))).
Definition term56 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term245 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term60 := fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0))).
Definition term86 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term39 (x0 : nat) := forall y0 : nat, (Nat.mul y0 x0) = y0.
Definition term34 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = y0.
Definition term301 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term99 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term125 (x0 : nat) := and (~ ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0))).
Definition term74 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term47 := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))).
Definition term46 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))).
Definition term188 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term7 := (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> False.
Definition term295 (x0 : nat) := fun y0 : nat => ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))).
Definition term200 (x0 : nat) (x1 : nat) := ((~ ((Nat.mul x1 x0) = x0)) \/ (~ ((Nat.mul x0 x1) = x0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term150 (x0 : nat) := or ((fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0).
Definition term136 (x0 : nat) := (fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term180 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0) \/ ((fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0).
Definition term182 (x0 : nat) := exists y0 : nat, (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0)).
Definition term258 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1) /\ ((fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1).
Definition term223 (x0 : nat) := (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0).
Definition term16 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term313 (x0 : nat) := ~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0).
Definition term184 (x0 : nat) := (exists y0 : nat, (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term158 := exists y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term253 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term227 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0.
Definition term193 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0.
Definition term162 := exists y0 : nat, (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term157 := exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term12 := (((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> ((~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term90 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term178 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ~ ((Nat.mul x0 y0) = y0)) x1) \/ ((fun y0 : nat => ~ ((Nat.mul y0 x0) = y0)) x1).
Definition term123 (x0 : nat) := ~ ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)).
Definition term293 (x0 : nat) (x1 : nat) := ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0)))).
Definition term83 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term134 (x0 : nat) := ~ (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) = (x0 = (NUMERAL (BIT1 0)))).
Definition term73 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term199 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ ((Nat.mul x1 y0) = y0)) \/ (~ ((Nat.mul y0 x1) = y0))) x0) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term325 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))).
Definition term331 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) -> False.
Definition term336 (x0 : nat) := ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0) -> False.
Definition term270 (x0 : nat) := (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ (forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term126 (x0 : nat) := and ((exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.mul y0 x0) = y0))).
Definition term314 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.mul x0 y0) = x0)) x1).
Definition term308 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.mul y0 x0) = x0)) x1).
Definition term288 := and (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))).
Definition term77 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term216 := fun y0 : nat => ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term202 (x0 : nat) := fun y0 : nat => ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term335 (x0 : nat) := (~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0)) -> (Nat.mul x0 (NUMERAL (BIT1 0))) = x0.
Definition term52 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term45 (x0 : nat) := @eq Prop ((fun y0 : nat => (forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) x0).
Definition term187 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term312 (x0 : nat) := (fun y0 : nat => ~ ((Nat.mul x0 y0) = x0)) (NUMERAL (BIT1 0)).
Definition term306 (x0 : nat) := (fun y0 : nat => ~ ((Nat.mul y0 x0) = x0)) (NUMERAL (BIT1 0)).
Definition term139 := fun y0 : nat => (((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (((exists y1 : nat, ~ ((Nat.mul y0 y1) = y1)) \/ (exists y1 : nat, ~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term201 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term264 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term237 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term79 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term218 := exists y0 : nat, (((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term310 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul x0 y0) = x0).
Definition term304 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul y0 x0) = x0).
Definition term289 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term284 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0.
Definition term333 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0)) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = x0.
Definition term299 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term279 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term277 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = y1) /\ ((Nat.mul y1 y0) = y1)) x0.
Definition term190 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term132 (x0 : nat) := (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((~ ((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term91 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term232 (x0 : nat) := fun y0 : nat => (((forall y1 : nat, (Nat.mul x0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 x0) = y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0).
Definition term72 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term183 (x0 : nat) := and (exists y0 : nat, (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))).
Definition term116 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.mul y1 x0) = y1) y0).
Definition term109 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.mul x0 y1) = y1) y0).
Definition term294 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term66 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term89 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term247 (x0 : nat) := fun y0 : nat => (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term2 := (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0)))) -> (@ε nat (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = y1) /\ ((Nat.mul y1 y0) = y1))) = (NUMERAL (BIT1 0)).
Definition term135 := exists y0 : nat, ~ ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) = (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term113 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Nat.mul y1 x0) = y1) y0).
Definition term106 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Nat.mul x0 y1) = y1) y0).
Definition term19 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = y0.
Definition term311 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul x0 y0) = x0)) x1.
Definition term305 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul y0 x0) = x0)) x1.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul y0 x0) = y0) x1.
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = y0) x1.
Definition term226 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) /\ (x0 = (NUMERAL (BIT1 0)))) y0.
Definition term161 := fun y0 : nat => (fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term25 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.mul x0 y0) = y0) x1) /\ ((fun y0 : nat => (Nat.mul y0 x0) = y0) x1).
Definition term287 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0).
Definition term265 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0).
Definition term35 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Nat.mul x0 y1) = y1) y0).
Definition term278 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0).
Definition term121 (x0 : nat) := (~ (forall y0 : nat, (Nat.mul x0 y0) = y0)) \/ (~ (forall y0 : nat, (Nat.mul y0 x0) = y0)).
Definition term117 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul y0 x0) = y0).
Definition term110 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul x0 y0) = y0).
Definition term172 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0.
Definition term168 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0.
Definition term241 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term321 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL (BIT1 0))) \/ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))))).
Definition term118 (x0 : nat) := exists y0 : nat, ~ ((Nat.mul y0 x0) = y0).
Definition term111 (x0 : nat) := exists y0 : nat, ~ ((Nat.mul x0 y0) = y0).
Definition term328 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) -> x1 = (NUMERAL (BIT1 0)).
Definition term64 := (~ (forall y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term58 := (~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term177 (x0 : nat) (x1 : nat) := or (~ ((Nat.mul x0 x1) = x1)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term1 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (x0 y0) = (y0 = x1)) -> (@ε nat x0) = x1.
Definition term211 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term171 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul y0 x0) = y0)) x1.
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul x0 y0) = y0)) x1.
Definition term236 := exists y0 : nat, exists y1 : nat, (((forall y2 : nat, (Nat.mul y0 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y0) = y2)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term205 := exists y0 : nat, exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term272 := forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term143 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term94 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term256 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1).
Definition term197 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) x1).
Definition term138 := fun y0 : nat => ~ ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) = (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term41 := fun y0 : nat => (forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1).
Definition term230 (x0 : nat) (x1 : nat) := (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((fun y0 : nat => ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))) x1).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term153 := fun y0 : nat => ((fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => ((exists y2 : nat, ~ ((Nat.mul y1 y2) = y2)) \/ (exists y2 : nat, ~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term170 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0).
Definition term159 := or (exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term112 (x0 : nat) := ~ (forall y0 : nat, (Nat.mul y0 x0) = y0).
Definition term105 (x0 : nat) := ~ (forall y0 : nat, (Nat.mul x0 y0) = y0).
Definition term67 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term330 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> x0 = (NUMERAL (BIT1 0)).
Definition term48 := forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))).
Definition term6 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))).
Definition term196 (x0 : nat) := @eq Prop ((exists y0 : nat, (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term195 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = y1)) \/ (~ ((Nat.mul y1 x0) = y1))) y0) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term115 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x1 x0) = x1).
Definition term108 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = x1).
Definition term290 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term285 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0.
Definition term55 := imp (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term93 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term317 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term179 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = x1)) \/ (~ ((Nat.mul x1 x0) = x1)).
Definition term9 := (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term104 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term320 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0)))).
Definition term215 (x0 : nat) := (((forall y0 : nat, (Nat.mul x0 y0) = y0) /\ (forall y0 : nat, (Nat.mul y0 x0) = y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, ((~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term221 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term337 := @ε nat (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = y1) /\ ((Nat.mul y1 y0) = y1)).
Definition term257 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term191 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.mul x0 y0) = y0)) \/ (~ ((Nat.mul y0 x0) = y0))) x1.
Definition term297 := fun y0 : nat => forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0)))).
Definition term276 := fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term275 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0))))).
Definition term249 := fun y0 : nat => forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term101 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term69 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term316 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0)))) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0)).
Definition term4 := NUMERAL (BIT1 0).
Definition term84 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term144 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term296 (x0 : nat) := forall y0 : nat, ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))).
Definition term248 (x0 : nat) := forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term63 := imp (~ (forall y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) = (y0 = (NUMERAL (BIT1 0))))).
Definition term51 := imp (~ (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))).
Definition term50 := imp (~ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = y2) /\ ((Nat.mul y2 y1) = y2)) y0) = (y0 = (NUMERAL (BIT1 0))))).
Definition term214 (x0 : nat) := ((fun y0 : nat => ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0) \/ ((fun y0 : nat => exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term95 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term27 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.mul x0 y1) = y1) y0) /\ ((fun y1 : nat => (Nat.mul y1 x0) = y1) y0).
Definition term213 := @eq Prop ((exists y0 : nat, ((forall y1 : nat, (Nat.mul y0 y1) = y1) /\ (forall y1 : nat, (Nat.mul y1 y0) = y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.mul y0 y1) = y1)) \/ (~ ((Nat.mul y1 y0) = y1))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term212 := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((forall y2 : nat, (Nat.mul y1 y2) = y2) /\ (forall y2 : nat, (Nat.mul y2 y1) = y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.mul y1 y2) = y2)) \/ (~ ((Nat.mul y2 y1) = y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0)).
Definition term175 (x0 : nat) := @eq Prop ((exists y0 : nat, ~ ((Nat.mul x0 y0) = y0)) \/ (exists y0 : nat, ~ ((Nat.mul y0 x0) = y0))).
Definition term174 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul x0 y1) = y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ ((Nat.mul y1 x0) = y1)) y0)).
