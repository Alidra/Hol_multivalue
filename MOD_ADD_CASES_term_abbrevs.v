Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term106 := (~ False) -> False.
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (Peano.lt x0 x2)) \/ (~ (Peano.lt x1 y0))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 y0))) x3.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x0 x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.lt x2 x3).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt y0 x1) -> (Peano.lt x0 x1) -> (~ (Peano.lt (Nat.add y0 x0) (Nat.add x1 x1))) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)).
Definition term42 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt y0 x1) -> (Peano.lt x0 x1) -> (~ (Peano.lt (Nat.add y0 x0) (Nat.add x1 x1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> False.
Definition term97 (x0 : Prop) := ~ (~ x0).
Definition term107 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y0) -> (Peano.lt y1 y0) -> (~ (Peano.lt (Nat.add y2 y1) (Nat.add y0 y0))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.lt y3 y5) /\ (Peano.lt y4 y6)) -> Peano.lt (Nat.add y3 y4) (Nat.add y5 y6)) -> False) x0.
Definition term76 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.lt y0 y2)) \/ (~ (Peano.lt y1 y3))) \/ (Peano.lt (Nat.add y0 y1) (Nat.add y2 y3))) x0.
Definition term40 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt y0 x1) -> (Peano.lt x0 x1) -> (~ (Peano.lt (Nat.add y0 x0) (Nat.add x1 x1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> False.
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ (Peano.lt x0 x2)) \/ (~ (Peano.lt x1 x3))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((~ (Peano.lt x0 x2)) \/ (~ (Peano.lt x1 y0))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt (Nat.add x0 x2) (Nat.add x1 x3)) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3))).
Definition term86 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (Peano.lt x0 x1))) /\ (~ (~ (Peano.lt x2 x3))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term17 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1)).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.lt (Nat.add x0 x2) (Nat.add x1 x3)) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term23 (x0 : Prop) := (~ x0) -> False.
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term91 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x2).
Definition term31 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term83 (x0 : Prop) := (~ x0) -> x0.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term94 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 x0) -> (Peano.lt y0 x0) -> (~ (Peano.lt (Nat.add y1 y0) (Nat.add x0 x0))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> False) x1.
Definition term98 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x0 x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> (Nat.modulo (Nat.add x0 x1) x2) = (@COND nat (Peano.lt (Nat.add x0 x1) x2) (Nat.add x0 x1) (Nat.sub (Nat.add x0 x1) x2)).
Definition term20 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add x0 x1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2)).
Definition term8 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term30 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term93 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term115 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y2)) -> (Nat.modulo (Nat.add y0 y1) y2) = (@COND nat (Peano.lt (Nat.add y0 y1) y2) (Nat.add y0 y1) (Nat.sub (Nat.add y0 y1) y2)).
Definition term114 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y1)) -> (Nat.modulo (Nat.add x0 y0) y1) = (@COND nat (Peano.lt (Nat.add x0 y0) y1) (Nat.add x0 y0) (Nat.sub (Nat.add x0 y0) y1)).
Definition term75 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.lt y0 y2)) \/ (~ (Peano.lt y1 y3))) \/ (Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term73 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.lt x0 y1)) \/ (~ (Peano.lt y0 y2))) \/ (Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)).
Definition term71 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.lt x1 y1))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)).
Definition term58 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term56 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term51 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt y2 y0) -> (Peano.lt y1 y0) -> (~ (Peano.lt (Nat.add y2 y1) (Nat.add y0 y0))) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.lt y3 y5) /\ (Peano.lt y4 y6)) -> Peano.lt (Nat.add y3 y4) (Nat.add y5 y6)).
Definition term50 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt y2 y0) -> (Peano.lt y1 y0) -> (~ (Peano.lt (Nat.add y2 y1) (Nat.add y0 y0))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.lt y3 y5) /\ (Peano.lt y4 y6)) -> Peano.lt (Nat.add y3 y4) (Nat.add y5 y6)) -> False.
Definition term47 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt y1 x0) -> (Peano.lt y0 x0) -> (~ (Peano.lt (Nat.add y1 y0) (Nat.add x0 x0))) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)).
Definition term46 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt y1 x0) -> (Peano.lt y0 x0) -> (~ (Peano.lt (Nat.add y1 y0) (Nat.add x0 x0))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> False.
Definition term32 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1)).
Definition term14 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.lt x1 y1))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add y0 y1))) x2.
Definition term77 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt x0 y1)) \/ (~ (Peano.lt y0 y2))) \/ (Peano.lt (Nat.add x0 y0) (Nat.add y1 y2))) x1.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (Peano.lt x0 x2)) \/ ((~ (Peano.lt x1 x3)) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3)))).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) /\ (Peano.lt x1 x2).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (Peano.lt x1 x3)) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3))).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (Peano.lt x0 x2)) \/ (~ (Peano.lt x1 x3)))) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x2)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x2).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((~ (Peano.lt x0 x2)) \/ (~ (Peano.lt x1 y0))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or ((~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3))).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.lt x0 x1) /\ (Peano.lt x2 x3)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> ((Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term36 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term100 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term99 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.lt x0 x1))).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x1 x3)) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term81 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((Peano.lt x0 x2) /\ (Peano.lt x1 x3))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) \/ ((Peano.lt (Nat.add x0 x2) (Nat.add x1 x3)) \/ (~ (Peano.lt x2 x3))).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1))) x0.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt (Nat.add x0 x2) (Nat.add x1 x3)) \/ (~ (Peano.lt x2 x3)).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2)) -> False.
Definition term16 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1))) -> (Nat.modulo x0 x1) = (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.lt x2 x3))).
Definition term82 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x2).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False) -> (Peano.lt x0 x2) -> (Peano.lt x1 x2) -> (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> False.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x0 x1) (Nat.add x2 x2))) -> False.
Definition term113 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y0)) -> (Nat.modulo (Nat.add x0 x1) y0) = (@COND nat (Peano.lt (Nat.add x0 x1) y0) (Nat.add x0 x1) (Nat.sub (Nat.add x0 x1) y0)).
Definition term11 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo x0 y0) = (@COND nat (Peano.lt x0 y0) x0 (Nat.sub x0 y0)).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x1) -> (Peano.lt x0 x1) -> (~ (Peano.lt (Nat.add y0 x0) (Nat.add x1 x1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> False) x2.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add x0 x1) x2.
Definition term15 (x0 : nat) (x1 : nat) := @COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.lt x2 x3)).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or (~ ((Peano.lt x0 x1) /\ (Peano.lt x2 x3))).
Definition term13 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.modulo x0 x1) = (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1)).
Definition term41 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt y0 x1) -> (Peano.lt x0 x1) -> (~ (Peano.lt (Nat.add y0 x0) (Nat.add x1 x1))) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)).
Definition term70 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.lt x1 y1))) \/ (Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)).
Definition term55 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term45 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt y1 x0) -> (Peano.lt y0 x0) -> (~ (Peano.lt (Nat.add y1 y0) (Nat.add x0 x0))) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)).
Definition term44 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt y1 x0) -> (Peano.lt y0 x0) -> (~ (Peano.lt (Nat.add y1 y0) (Nat.add x0 x0))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> False.
Definition term74 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.lt y0 y2)) \/ (~ (Peano.lt y1 y3))) \/ (Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term72 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt x0 y1)) \/ (~ (Peano.lt y0 y2))) \/ (Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)).
Definition term59 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term57 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term49 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y0) -> (Peano.lt y1 y0) -> (~ (Peano.lt (Nat.add y2 y1) (Nat.add y0 y0))) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.lt y3 y5) /\ (Peano.lt y4 y6)) -> Peano.lt (Nat.add y3 y4) (Nat.add y5 y6)).
Definition term48 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt y2 y0) -> (Peano.lt y1 y0) -> (~ (Peano.lt (Nat.add y2 y1) (Nat.add y0 y0))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.lt y3 y5) /\ (Peano.lt y4 y6)) -> Peano.lt (Nat.add y3 y4) (Nat.add y5 y6)) -> False.
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat (Peano.lt (Nat.add x0 x1) x2) (Nat.add x0 x1) (Nat.sub (Nat.add x0 x1) x2).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo x0 y0) = (@COND nat (Peano.lt x0 y0) x0 (Nat.sub x0 y0))) x1.
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x2)) -> (Nat.modulo (Nat.add x0 x1) x2) = (@COND nat (Peano.lt (Nat.add x0 x1) x2) (Nat.add x0 x1) (Nat.sub (Nat.add x0 x1) x2)).
