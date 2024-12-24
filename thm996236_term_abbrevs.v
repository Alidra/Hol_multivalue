Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term80 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term125 (x0 : nat) := ((Nat.mul (BIT1 0) x0) = x0) -> False.
Definition term126 := (~ False) -> False.
Definition term1 (x0 : nat) (x1 : nat) := ((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term5 (x0 : nat) (x1 : nat) := ((~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term48 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term56 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term94 (x0 : Prop) := ~ (~ x0).
Definition term17 (x0 : nat) := fun y0 : nat => (~ (((Nat.mul (BIT1 0) y0) = y0) /\ ((Nat.mul x0 (BIT1 0)) = x0))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term58 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term60 (x0 : nat) := Nat.mul (BIT1 0) x0.
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term107 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0).
Definition term62 (x0 : nat) := ~ ((Nat.mul (BIT1 0) x0) = x0).
Definition term75 := ~ ((NUMERAL (BIT1 0)) = (BIT1 0)).
Definition term8 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term78 (x0 : nat) := ~ (x0 = x0).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term38 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term11 := imp ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term45 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term4 (x0 : nat) (x1 : nat) := (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term18 (x0 : nat) := forall y0 : nat, (~ (((Nat.mul (BIT1 0) y0) = y0) /\ ((Nat.mul x0 (BIT1 0)) = x0))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term87 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term97 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term66 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term76 (x0 : Prop) := (~ x0) -> x0.
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term6 (x0 : nat) (x1 : nat) := (((~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term3 (x0 : nat) (x1 : nat) := ~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1)).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term103 (x0 : nat) := (((NUMERAL (BIT1 0)) = (BIT1 0)) /\ (x0 = x0)) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0).
Definition term91 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term77 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term13 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term40 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term83 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term123 (x0 : nat) := (((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0)) /\ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0)) -> (Nat.mul (BIT1 0) x0) = x0.
Definition term31 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term35 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3)).
Definition term25 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term105 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0)).
Definition term128 (x0 : nat) := ((x0 = x0) /\ ((NUMERAL (BIT1 0)) = (BIT1 0))) -> (Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0)).
Definition term19 (x0 : nat) := forall y0 : nat, (~ (((Nat.mul (BIT1 0) y0) = y0) /\ ((Nat.mul x0 (BIT1 0)) = x0))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term41 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term104 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0))) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0).
Definition term129 (x0 : nat) := (~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0)))) -> (Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0)).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term57 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term52 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term64 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term15 (x0 : nat) (x1 : nat) := (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term47 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term42 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term90 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term36 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term30 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term23 := forall y0 : nat, forall y1 : nat, (~ (((Nat.mul (BIT1 0) y1) = y1) /\ ((Nat.mul y0 (BIT1 0)) = y0))) -> ((forall y2 : nat, (Nat.mul (NUMERAL 0) y2) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul (NUMERAL (BIT1 0)) y2) = y2) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL (BIT1 0))) = y2) /\ ((forall y2 : nat, forall y3 : nat, (Nat.mul (S y2) y3) = (Nat.add (Nat.mul y2 y3) y3)) /\ (forall y2 : nat, forall y3 : nat, (Nat.mul y2 (S y3)) = (Nat.add y2 (Nat.mul y2 y3)))))))) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term22 := forall y0 : nat, forall y1 : nat, (~ (((Nat.mul (BIT1 0) y1) = y1) /\ ((Nat.mul y0 (BIT1 0)) = y0))) -> ((forall y2 : nat, (Nat.mul (NUMERAL 0) y2) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul (NUMERAL (BIT1 0)) y2) = y2) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL (BIT1 0))) = y2) /\ ((forall y2 : nat, forall y3 : nat, (Nat.mul (S y2) y3) = (Nat.add (Nat.mul y2 y3) y3)) /\ (forall y2 : nat, forall y3 : nat, (Nat.mul y2 (S y3)) = (Nat.add y2 (Nat.mul y2 y3)))))))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)))).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term46 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term65 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term10 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term61 (x0 : nat) := Nat.mul x0 (BIT1 0).
Definition term14 (x0 : nat) (x1 : nat) := imp (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term34 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term134 (x0 : nat) := (((Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0))) /\ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0)) -> (Nat.mul x0 (BIT1 0)) = x0.
Definition term102 (x0 : nat) := ((NUMERAL (BIT1 0)) = (BIT1 0)) /\ (x0 = x0).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term132 (x0 : nat) := ~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0).
Definition term63 (x0 : nat) := ~ ((Nat.mul x0 (BIT1 0)) = x0).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 (x0 : nat) (x1 : nat) := (((~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term50 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term96 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term43 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term33 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term74 := (~ ((NUMERAL (BIT1 0)) = (BIT1 0))) -> (NUMERAL (BIT1 0)) = (BIT1 0).
Definition term136 (x0 : nat) := ((Nat.mul x0 (BIT1 0)) = x0) -> False.
Definition term138 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (((Nat.mul (BIT1 0) y0) = y0) /\ ((Nat.mul x0 (BIT1 0)) = x0))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False) x1.
Definition term37 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term135 (x0 : nat) := (~ ((Nat.mul x0 (BIT1 0)) = x0)) -> (Nat.mul x0 (BIT1 0)) = x0.
Definition term131 (x0 : nat) := (~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0)) -> (Nat.mul x0 (NUMERAL (BIT1 0))) = x0.
Definition term39 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term130 (x0 : nat) := ~ ((Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3))).
Definition term124 (x0 : nat) := (~ ((Nat.mul (BIT1 0) x0) = x0)) -> (Nat.mul (BIT1 0) x0) = x0.
Definition term106 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0)) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = x0.
Definition term137 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((Nat.mul (BIT1 0) y1) = y1) /\ ((Nat.mul y0 (BIT1 0)) = y0))) -> ((forall y2 : nat, (Nat.mul (NUMERAL 0) y2) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul (NUMERAL (BIT1 0)) y2) = y2) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL (BIT1 0))) = y2) /\ ((forall y2 : nat, forall y3 : nat, (Nat.mul (S y2) y3) = (Nat.add (Nat.mul y2 y3) y3)) /\ (forall y2 : nat, forall y3 : nat, (Nat.mul y2 (S y3)) = (Nat.add y2 (Nat.mul y2 y3)))))))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False) x0.
Definition term127 (x0 : nat) := (x0 = x0) /\ ((NUMERAL (BIT1 0)) = (BIT1 0)).
Definition term51 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term32 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term26 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term49 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term122 (x0 : nat) := ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (BIT1 0) x0)) /\ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0).
Definition term68 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term12 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term24 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3))).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term2 (x0 : nat) (x1 : nat) := (~ (((Nat.mul (BIT1 0) x0) = x0) /\ ((Nat.mul x1 (BIT1 0)) = x1))) -> False.
Definition term54 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term133 (x0 : nat) := ((Nat.mul x0 (NUMERAL (BIT1 0))) = (Nat.mul x0 (BIT1 0))) /\ ((Nat.mul x0 (NUMERAL (BIT1 0))) = x0).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term16 (x0 : nat) := fun y0 : nat => (~ (((Nat.mul (BIT1 0) y0) = y0) /\ ((Nat.mul x0 (BIT1 0)) = x0))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term9 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term27 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term95 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term81 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term53 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term21 := fun y0 : nat => forall y1 : nat, (~ (((Nat.mul (BIT1 0) y1) = y1) /\ ((Nat.mul y0 (BIT1 0)) = y0))) -> ((forall y2 : nat, (Nat.mul (NUMERAL 0) y2) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul (NUMERAL (BIT1 0)) y2) = y2) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL (BIT1 0))) = y2) /\ ((forall y2 : nat, forall y3 : nat, (Nat.mul (S y2) y3) = (Nat.add (Nat.mul y2 y3) y3)) /\ (forall y2 : nat, forall y3 : nat, (Nat.mul y2 (S y3)) = (Nat.add y2 (Nat.mul y2 y3)))))))) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term20 := fun y0 : nat => forall y1 : nat, (~ (((Nat.mul (BIT1 0) y1) = y1) /\ ((Nat.mul y0 (BIT1 0)) = y0))) -> ((forall y2 : nat, (Nat.mul (NUMERAL 0) y2) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y2 : nat, (Nat.mul (NUMERAL (BIT1 0)) y2) = y2) /\ ((forall y2 : nat, (Nat.mul y2 (NUMERAL (BIT1 0))) = y2) /\ ((forall y2 : nat, forall y3 : nat, (Nat.mul (S y2) y3) = (Nat.add (Nat.mul y2 y3) y3)) /\ (forall y2 : nat, forall y3 : nat, (Nat.mul y2 (S y3)) = (Nat.add y2 (Nat.mul y2 y3)))))))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term73 := NUMERAL (BIT1 0).
Definition term44 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term59 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (BIT1 0) x0) = x0)) \/ (~ ((Nat.mul x1 (BIT1 0)) = x1)).
Definition term55 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
