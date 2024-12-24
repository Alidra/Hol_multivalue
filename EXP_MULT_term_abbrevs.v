Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term104 (x0 : nat) := ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0) -> (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (S x0).
Definition term99 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0.
Definition term47 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) x0.
Definition term52 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term34 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term121 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) (Nat.pow (NUMERAL (BIT1 0)) x0).
Definition term25 (x0 : nat) := forall y0 : nat, (forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) -> forall y1 : nat, (Nat.pow x0 (Nat.mul (S y0) y1)) = (Nat.pow (Nat.pow x0 (S y0)) y1).
Definition term114 := fun y0 : nat => (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term63 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term54 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (S x1).
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term35 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term33 (x0 : nat) := ((forall y0 : nat, (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) -> forall y1 : nat, (Nat.pow x0 (Nat.mul (S y0) y1)) = (Nat.pow (Nat.pow x0 (S y0)) y1))) -> forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1).
Definition term95 := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0).
Definition term115 := forall y0 : nat, (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.mul x0 x1) x2.
Definition term110 := ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0)).
Definition term65 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 (Nat.mul x1 x2)).
Definition term94 := (((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term8 (x0 : nat) := (((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0.
Definition term64 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term105 (x0 : nat) := ((Nat.pow (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S x0)) = (NUMERAL (BIT1 0)).
Definition term103 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) (S x0).
Definition term102 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (S x0).
Definition term39 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term7 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow (Nat.mul x0 y0) x1) = (Nat.mul (Nat.pow x0 x1) (Nat.pow y0 x1))) x2.
Definition term112 := imp (((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0))).
Definition term28 (x0 : nat) := imp (((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) (S y0))).
Definition term91 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.pow (Nat.pow x0 x1) y0) (Nat.pow x0 y0)) = (Nat.pow (Nat.mul x0 (Nat.pow x0 x1)) y0).
Definition term19 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x0 (Nat.mul (S x1) y0)) = (Nat.pow (Nat.pow x0 (S x1)) y0).
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0).
Definition term44 (x0 : nat) := Nat.pow (Nat.pow x0 (NUMERAL 0)).
Definition term122 (x0 : nat) := @eq nat (Nat.pow (NUMERAL (BIT1 0)) (S x0)).
Definition term41 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.mul (NUMERAL 0) x1).
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1))) x1.
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0))) x1.
Definition term59 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term108 := forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0).
Definition term24 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) (S y0).
Definition term9 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1).
Definition term86 (x0 : nat) (x1 : nat) := Nat.pow (Nat.mul x0 (Nat.pow x0 x1)).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term98 := and ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term97 := and ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 (Nat.mul x0 x2)) (Nat.pow x1 x2).
Definition term12 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0)).
Definition term49 := fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.pow (NUMERAL (BIT1 0)) y0).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.pow x0 (S x1)) x2.
Definition term13 (x0 : nat) := and (forall y0 : nat, (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0)).
Definition term90 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.pow (Nat.pow x0 x1) y0) (Nat.pow x0 y0)) = (Nat.pow (Nat.mul x0 (Nat.pow x0 x1)) y0).
Definition term101 (x0 : nat) := imp ((Nat.pow (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (NUMERAL 0).
Definition term38 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term106 := fun y0 : nat => ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul (Nat.pow (Nat.pow x1 x0) x2) (Nat.pow x1 x2)).
Definition term29 (x0 : nat) := imp ((forall y0 : nat, (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) -> forall y1 : nat, (Nat.pow x0 (Nat.mul (S y0) y1)) = (Nat.pow (Nat.pow x0 (S y0)) y1))).
Definition term45 := Nat.pow (NUMERAL (BIT1 0)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.pow x0 (Nat.mul (S x1) x2)).
Definition term129 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow y0 y1) y2).
Definition term68 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term61 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term55 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0)).
Definition term96 := Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow (Nat.pow x1 x0) x2) (Nat.pow x1 x2).
Definition term92 := fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term117 := @eq nat (Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term89 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow x0 (Nat.mul (S x1) y0)) = (Nat.pow (Nat.pow x0 (S x1)) y0).
Definition term48 (x0 : nat) := fun y0 : nat => (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0).
Definition term118 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term66 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term93 := forall y0 : nat, (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term119 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add (Nat.mul x1 x2) x2).
Definition term85 (x0 : nat) (x1 : nat) := Nat.pow (Nat.pow x0 (S x1)).
Definition term57 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term125 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.pow (Nat.pow x0 x1) y0) (Nat.pow x0 y0)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow (Nat.pow x0 x1) y0)).
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term16 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) x1).
Definition term127 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0)) x2.
Definition term23 (x0 : nat) := fun y0 : nat => (forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) -> forall y1 : nat, (Nat.pow x0 (Nat.mul (S y0) y1)) = (Nat.pow (Nat.pow x0 (S y0)) y1).
Definition term22 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) (S y0).
Definition term128 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term53 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term20 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) x1) -> (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (S x1).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.mul x1 x2).
Definition term27 (x0 : nat) := (forall y0 : nat, (Nat.pow x0 (Nat.mul (NUMERAL 0) y0)) = (Nat.pow (Nat.pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) -> forall y1 : nat, (Nat.pow x0 (Nat.mul (S y0) y1)) = (Nat.pow (Nat.pow x0 (S y0)) y1)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow (Nat.pow x0 x1) x2).
Definition term30 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0.
Definition term111 := ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0))).
Definition term43 := @eq nat (NUMERAL (BIT1 0)).
Definition term126 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term56 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term37 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term60 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term26 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) (S y0)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term46 (x0 : nat) (x1 : nat) := Nat.pow (Nat.pow x0 (NUMERAL 0)) x1.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow (Nat.mul x0 y0) x1) = (Nat.mul (Nat.pow x0 x1) (Nat.pow y0 x1)).
Definition term107 := fun y0 : nat => ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.mul x0 (Nat.pow x0 x1)) x2.
Definition term124 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.pow (Nat.pow x0 x1) y0) (Nat.pow x0 y0)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow (Nat.pow x0 x1) y0)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.pow x0 x1) x2.
Definition term50 := forall y0 : nat, (NUMERAL (BIT1 0)) = (Nat.pow (NUMERAL (BIT1 0)) y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 x2) (Nat.pow (Nat.pow x0 x1) x2).
Definition term36 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term100 (x0 : nat) := imp ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0).
Definition term109 := forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)).
Definition term31 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.pow x0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow x0 y1) y2)) y0.
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 (Nat.mul (NUMERAL 0) x1)).
Definition term51 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term116 := (((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)))) -> forall y0 : nat, (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.mul (S x1) x2).
Definition term40 := NUMERAL (BIT1 0).
Definition term120 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term113 := imp (((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)))).
Definition term21 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0)) -> forall y0 : nat, (Nat.pow x0 (Nat.mul (S x1) y0)) = (Nat.pow (Nat.pow x0 (S x1)) y0).
