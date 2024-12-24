Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term112 (x0 : nat) := fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term335 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term287 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) y0) /\ (Peano.le y0 x1).
Definition term241 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term285 (x0 : nat) (x1 : nat) := and (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term303 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.modulo x0 x1) (Nat.modulo x0 x1)) (Nat.add x1 (Nat.modulo x0 x1)).
Definition term140 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term185 := (~ False) -> False.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) x2.
Definition term294 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.lt x0 x1).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2).
Definition term286 (x0 : nat) (x1 : nat) := (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) /\ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1).
Definition term132 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term110 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term102 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0.
Definition term329 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term176 (x0 : Prop) := ~ (~ x0).
Definition term291 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1)) x0.
Definition term268 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term233 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term219 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2) x0.
Definition term202 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) x0.
Definition term168 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0.
Definition term166 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0.
Definition term183 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1))) -> Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (Nat.sub x0 x1) x2) (Nat.add x1 x2).
Definition term318 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1).
Definition term118 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term56 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term314 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0) x1.
Definition term279 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> (Peano.le (Nat.modulo x0 x1) x1) = True.
Definition term307 (x0 : nat) (x1 : nat) := True /\ (Peano.le (Nat.add x0 (Nat.modulo x1 x0)) x1).
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term283 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term104 (x0 : nat) (x1 : nat) := or (forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0).
Definition term86 (x0 : nat) (x1 : nat) := or (forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0).
Definition term106 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term91 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term246 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term218 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term12 (x0 : nat) (x1 : nat) := (((~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x2)) /\ (Peano.lt x2 x1)) -> (Nat.modulo x0 x1) = x2.
Definition term333 (x0 : nat) := (fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ~ (Peano.lt (Nat.add x1 y0) (Nat.add x2 y0))) x0) \/ (Peano.lt x1 x2).
Definition term155 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term154 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1))).
Definition term5 (x0 : Prop) := (~ x0) -> False.
Definition term301 (x0 : nat) (x1 : nat) := Nat.add x1 (Nat.modulo x0 x1).
Definition term133 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term111 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term46 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term151 := (forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term109 (x0 : nat) := forall y0 : nat, ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term36 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term8 (x0 : nat) (x1 : nat) := (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> False.
Definition term184 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)) -> False.
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x2) (Nat.add x1 x2).
Definition term338 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 x1)) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) x1.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2)).
Definition term339 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 y0)) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo y0 x0)) y0.
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0.
Definition term171 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.sub x0 x1) x1).
Definition term113 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term300 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.modulo x0 x1) (Nat.modulo x0 x1)).
Definition term193 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) -> Peano.lt x1 x2.
Definition term127 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0.
Definition term122 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0.
Definition term84 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0.
Definition term65 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0.
Definition term60 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0.
Definition term240 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0) x2.
Definition term288 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) y0) /\ (Peano.le y0 x1).
Definition term152 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.sub x0 x1) x1) /\ (~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1))).
Definition term98 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term174 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term43 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term230 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 x1).
Definition term244 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term130 := fun y0 : nat => (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term15 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term74 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)))) -> Peano.lt x1 x2.
Definition term327 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.sub x0 x1) (Nat.mul (NUMERAL (BIT1 0)) x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term326 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term266 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)) x2.
Definition term308 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1) x1.
Definition term173 (x0 : Prop) := (~ x0) -> x0.
Definition term227 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term334 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.sub x0 x1) x1).
Definition term319 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2) /\ ((fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)) x2).
Definition term89 (x0 : nat) (x1 : nat) := and ((forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term108 (x0 : nat) := fun y0 : nat => ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := or (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term282 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x0 x1) x1.
Definition term229 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1).
Definition term142 := @eq Prop (forall y0 : nat, (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1))).
Definition term141 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0)).
Definition term120 (x0 : nat) := @eq Prop (forall y0 : nat, ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0))).
Definition term119 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0)).
Definition term100 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term99 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1)).
Definition term82 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term81 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1))).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1))).
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0)).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.sub x0 x1) x1) -> Peano.lt (Nat.add (Nat.sub x0 x1) x2) (Nat.add x1 x2).
Definition term309 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x1 (Nat.modulo x0 x1)).
Definition term332 (x0 : nat) (x1 : nat) := True /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term70 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) \/ x1.
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term28 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.lt x0 x1).
Definition term293 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0)) x1.
Definition term270 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term235 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term220 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1) x1.
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1.
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1.
Definition term161 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term160 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1)).
Definition term256 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term92 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term162 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term135 := fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term30 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.lt x0 y0).
Definition term177 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term20 (x0 : nat) := fun y0 : nat => (~ ((Peano.lt (Nat.sub y0 x0) x0) = (Peano.lt (Nat.add (Nat.sub y0 x0) x0) (Nat.add x0 x0)))) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2))) /\ ((~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2)).
Definition term10 (x0 : nat) (x1 : nat) := (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term35 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term1 := fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term317 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term225 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term121 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0.
Definition term59 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0.
Definition term0 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term153 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) /\ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term66 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term125 (x0 : nat) := and (forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))).
Definition term63 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term103 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term3 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2))).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)))).
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> (Nat.modulo x1 x2) = x3.
Definition term297 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term208 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0) x3.
Definition term340 := forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo y1 y0)) y1.
Definition term292 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term269 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term245 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term234 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term232 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term217 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term216 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1.
Definition term205 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1.
Definition term203 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2.
Definition term201 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3.
Definition term165 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term163 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term159 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term157 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term150 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term145 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term40 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term38 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.lt x0 y0).
Definition term26 := forall y0 : nat, forall y1 : nat, (~ ((Peano.lt (Nat.sub y1 y0) y0) = (Peano.lt (Nat.add (Nat.sub y1 y0) y0) (Nat.add y0 y0)))) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)).
Definition term25 := forall y0 : nat, forall y1 : nat, (~ ((Peano.lt (Nat.sub y1 y0) y0) = (Peano.lt (Nat.add (Nat.sub y1 y0) y0) (Nat.add y0 y0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False.
Definition term16 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1).
Definition term290 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term139 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0).
Definition term71 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) \/ x1.
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1) x2.
Definition term223 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term204 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2) x1.
Definition term88 (x0 : nat) (x1 : nat) := (forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term33 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.sub x0 x1) x1) /\ (~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) \/ ((~ (Peano.lt (Nat.sub x0 x1) x1)) /\ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1))).
Definition term275 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) x2).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt x0 x1) \/ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)))).
Definition term107 (x0 : nat) (x1 : nat) := ((forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term265 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term61 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term194 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)) -> Peano.lt (Nat.sub x0 x1) x1.
Definition term260 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0) x1.
Definition term322 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) (Nat.mul (NUMERAL (BIT1 0)) x1).
Definition term310 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.modulo x0 x1) x1).
Definition term330 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term331 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> (Nat.modulo x0 x1) = x2.
Definition term116 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1.
Definition term4 := forall y0 : nat, (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term271 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2.
Definition term325 (x0 : nat) (x1 : nat) := and (x0 = (Nat.add (Nat.sub x0 x1) (Nat.mul (NUMERAL (BIT1 0)) x1))).
Definition term324 (x0 : nat) (x1 : nat) := and (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.sub x0 x1))).
Definition term197 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Peano.lt (Nat.sub y0 x0) x0) = (Peano.lt (Nat.add (Nat.sub y0 x0) x0) (Nat.add x0 x0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False) x1.
Definition term105 (x0 : nat) (x1 : nat) := or (forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))).
Definition term199 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term117 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1) /\ ((fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term44 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term304 (x0 : nat) (x1 : nat) := and (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1)) (Nat.add x1 (Nat.modulo x0 x1))).
Definition term21 (x0 : nat) := forall y0 : nat, (~ ((Peano.lt (Nat.sub y0 x0) x0) = (Peano.lt (Nat.add (Nat.sub y0 x0) x0) (Nat.add x0 x0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False.
Definition term336 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term179 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term305 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (Nat.modulo x1 x0)) x1.
Definition term200 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term277 := NUMERAL (BIT0 (BIT1 0)).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term236 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.lt (Nat.add x1 y0) (Nat.add x2 y0)) x0) \/ (~ (Peano.lt x1 x2)).
Definition term129 (x0 : nat) := (forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term67 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ (forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term215 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0.
Definition term228 (x0 : nat) (x1 : nat) := (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1) \/ (~ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1)).
Definition term298 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1) (Nat.modulo x0 x1).
Definition term83 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0.
Definition term253 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term147 := and (forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))).
Definition term75 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term2 := fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term72 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term250 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1).
Definition term18 (x0 : nat) (x1 : nat) := (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term148 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0.
Definition term143 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0.
Definition term312 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) x0.
Definition term262 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term258 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) x0.
Definition term247 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term222 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term198 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term196 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Peano.lt (Nat.sub y1 y0) y0) = (Peano.lt (Nat.add (Nat.sub y1 y0) y0) (Nat.add y0 y0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False) x0.
Definition term138 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0.
Definition term136 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0.
Definition term311 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.modulo x1 x0) x0) x1.
Definition term9 (x0 : nat) (x1 : nat) := ~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1))).
Definition term252 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term11 (x0 : nat) (x1 : nat) := ((~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term278 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> (Peano.le x0 x1) = True.
Definition term284 := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ True.
Definition term7 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1).
Definition term281 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> (x0 = (NUMERAL 0)) = False.
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2)).
Definition term226 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) x1).
Definition term280 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 x1) x1) = True.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt x0 x1))) -> Peano.lt (Nat.add x0 x2) (Nat.add x1 x2).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) x2).
Definition term254 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) x0.
Definition term6 (x0 : nat) (x1 : nat) := Peano.lt (Nat.sub x0 x1) x1.
Definition term243 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term126 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0.
Definition term64 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0.
Definition term73 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term146 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0).
Definition term124 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0).
Definition term62 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0).
Definition term137 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0).
Definition term257 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term267 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term264 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term101 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0.
Definition term276 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le (Nat.modulo x0 x1) x1).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term242 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term156 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term134 := fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term24 := fun y0 : nat => forall y1 : nat, (~ ((Peano.lt (Nat.sub y1 y0) y0) = (Peano.lt (Nat.add (Nat.sub y1 y0) y0) (Nat.add y0 y0)))) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term170 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)).
Definition term131 := forall y0 : nat, (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term316 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) x1.
Definition term249 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) y0) /\ (Peano.le y0 x1)) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) x1.
Definition term289 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) x1.
Definition term115 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1).
Definition term48 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term261 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term17 (x0 : nat) (x1 : nat) := imp (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))).
Definition term123 (x0 : nat) := forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term195 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.sub x0 x1) x1) -> False.
Definition term259 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term224 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term302 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1)) (Nat.add x1 (Nat.modulo x0 x1)).
Definition term22 (x0 : nat) := forall y0 : nat, (~ ((Peano.lt (Nat.sub y0 x0) x0) = (Peano.lt (Nat.add (Nat.sub y0 x0) x0) (Nat.add x0 x0)))) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) x2.
Definition term13 (x0 : nat) (x1 : nat) := (((~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> ((~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (~ ((Peano.lt (Nat.sub x0 x1) x1) = (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term315 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term90 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term263 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term295 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1)) x2.
Definition term149 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0.
Definition term144 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0.
Definition term321 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.sub x0 x1).
Definition term328 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term251 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x0 x2) (Nat.add x1 x2).
Definition term23 := fun y0 : nat => forall y1 : nat, (~ ((Peano.lt (Nat.sub y1 y0) y0) = (Peano.lt (Nat.add (Nat.sub y1 y0) y0) (Nat.add y0 y0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False.
Definition term231 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term306 (x0 : nat) (x1 : nat) := (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x1 x0)) (Nat.add x0 (Nat.modulo x1 x0))) /\ (Peano.le (Nat.add x0 (Nat.modulo x1 x0)) x1).
Definition term114 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1.
Definition term299 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo x0 x1)).
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term37 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term255 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term337 := NUMERAL (BIT1 0).
Definition term323 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2).
Definition term87 (x0 : nat) (x1 : nat) := or (forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term128 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term19 (x0 : nat) := fun y0 : nat => (~ ((Peano.lt (Nat.sub y0 x0) x0) = (Peano.lt (Nat.add (Nat.sub y0 x0) x0) (Nat.add x0 x0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False.
Definition term164 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term158 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term39 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term32 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1).
Definition term80 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term85 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0).
Definition term248 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term172 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) -> Peano.lt (Nat.sub x0 x1) x1.
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) -> Peano.lt (Nat.add x0 x2) (Nat.add x1 x2).
Definition term313 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term320 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1)) -> (Nat.modulo x0 x1) = (Nat.sub x0 x1).
Definition term178 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
