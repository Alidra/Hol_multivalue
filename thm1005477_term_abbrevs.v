Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term139 (x0 : nat) := @eq nat (S (NUMERAL x0)).
Definition term117 := (~ False) -> False.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term127 := fun y0 : nat => (~ (y0 = (NUMERAL y0))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term122 (x0 : nat) := ((~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term6 (x0 : nat) := ((~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term44 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term75 (x0 : Prop) := ~ (~ x0).
Definition term108 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) \/ (~ (x0 = x1)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term16 (x0 : nat) := (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term9 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term34 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term133 (x0 : nat) := ((NUMERAL x0) = x0) /\ ((NUMERAL x0) = (NUMERAL x0)).
Definition term88 (x0 : nat) := (~ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (NUMERAL x0))) -> (Nat.add (NUMERAL 0) (NUMERAL x0)) = (NUMERAL x0).
Definition term129 := forall y0 : nat, (~ (y0 = (NUMERAL y0))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term19 := forall y0 : nat, (~ ((S (Nat.add 0 y0)) = (S (NUMERAL y0)))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term68 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term78 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term121 (x0 : nat) := (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term57 (x0 : Prop) := (~ x0) -> x0.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term107 (x0 : nat) := ~ ((Nat.add 0 x0) = (NUMERAL x0)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term123 (x0 : nat) := (((~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term7 (x0 : nat) := (((~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term58 (x0 : nat) := (~ ((NUMERAL x0) = x0)) -> (NUMERAL x0) = x0.
Definition term72 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term104 (x0 : nat) := ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0)) /\ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (NUMERAL x0)).
Definition term87 (x0 : nat) := ~ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0)).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term2 (x0 : nat) := S (NUMERAL x0).
Definition term14 := ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term30 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term55 := (~ ((NUMERAL 0) = 0)) -> (NUMERAL 0) = 0.
Definition term36 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term35 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term64 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term126 (x0 : nat) := (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term110 (x0 : nat) (x1 : nat) := @eq Prop (((S x0) = (S x1)) \/ (~ (x0 = x1))).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3)).
Definition term115 (x0 : nat) := (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> (S (Nat.add 0 x0)) = (S (NUMERAL x0)).
Definition term130 := forall y0 : nat, (~ (y0 = (NUMERAL y0))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term20 := forall y0 : nat, (~ ((S (Nat.add 0 y0)) = (S (NUMERAL y0)))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term37 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term85 (x0 : nat) := Nat.add (NUMERAL 0) (NUMERAL x0).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term18 := fun y0 : nat => (~ ((S (Nat.add 0 y0)) = (S (NUMERAL y0)))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term138 (x0 : nat) := @eq nat (S (Nat.add 0 x0)).
Definition term113 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term45 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term40 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term119 (x0 : nat) := (~ (x0 = (NUMERAL x0))) -> False.
Definition term12 := imp ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))).
Definition term23 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term132 (x0 : nat) := ~ ((NUMERAL x0) = (NUMERAL x0)).
Definition term43 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term38 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term71 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term32 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term27 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)))).
Definition term134 (x0 : nat) := (((NUMERAL x0) = x0) /\ ((NUMERAL x0) = (NUMERAL x0))) -> x0 = (NUMERAL x0).
Definition term120 (x0 : nat) := ~ (x0 = (NUMERAL x0)).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term105 (x0 : nat) := (((Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0)) /\ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (NUMERAL x0))) -> (Nat.add 0 x0) = (NUMERAL x0).
Definition term42 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term17 := fun y0 : nat => (~ ((S (Nat.add 0 y0)) = (S (NUMERAL y0)))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term46 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term11 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term131 (x0 : nat) := (~ ((NUMERAL x0) = (NUMERAL x0))) -> (NUMERAL x0) = (NUMERAL x0).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term124 (x0 : nat) := (((~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (x0 = (NUMERAL x0))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term8 (x0 : nat) := (((~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term77 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term39 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term5 (x0 : nat) := (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term1 (x0 : nat) := S (Nat.add 0 x0).
Definition term24 (x0 : nat) := fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
Definition term33 := and (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3))).
Definition term3 (x0 : nat) := (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))) -> False.
Definition term116 (x0 : nat) := ((S (Nat.add 0 x0)) = (S (NUMERAL x0))) -> False.
Definition term125 (x0 : nat) := imp (~ (x0 = (NUMERAL x0))).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term52 (x0 : nat) (x1 : nat) := (x0 = x1) -> (S x0) = (S x1).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term22 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term106 (x0 : nat) := (~ ((Nat.add 0 x0) = (NUMERAL x0))) -> (Nat.add 0 x0) = (NUMERAL x0).
Definition term29 (x0 : nat) := fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term48 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term111 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (S x0) = (S x1).
Definition term4 (x0 : nat) := ~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0))).
Definition term13 := ((forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term114 (x0 : nat) := ((Nat.add 0 x0) = (NUMERAL x0)) -> (S (Nat.add 0 x0)) = (S (NUMERAL x0)).
Definition term21 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term59 (x0 : nat) := ~ ((NUMERAL x0) = x0).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3))).
Definition term31 := fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term26 := fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term56 := ~ ((NUMERAL 0) = 0).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term86 (x0 : nat) := (~ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0))) -> (Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0).
Definition term41 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((S x0) = (S x1))).
Definition term53 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((S x0) = (S x1)).
Definition term84 (x0 : nat) := (((NUMERAL 0) = 0) /\ ((NUMERAL x0) = x0)) -> (Nat.add (NUMERAL 0) (NUMERAL x0)) = (Nat.add 0 x0).
Definition term15 (x0 : nat) := imp (~ ((S (Nat.add 0 x0)) = (S (NUMERAL x0)))).
Definition term137 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL y0))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False) x0.
Definition term118 (x0 : nat) := (fun y0 : nat => (~ ((S (Nat.add 0 y0)) = (S (NUMERAL y0)))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False) x0.
Definition term83 (x0 : nat) := ((NUMERAL 0) = 0) /\ ((NUMERAL x0) = x0).
Definition term128 := fun y0 : nat => (~ (y0 = (NUMERAL y0))) -> ((forall y1 : nat, (Nat.add (NUMERAL 0) y1) = y1) /\ ((forall y1 : nat, (Nat.add y1 (NUMERAL 0)) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.add (S y1) y2) = (S (Nat.add y1 y2))) /\ (forall y1 : nat, forall y2 : nat, (Nat.add y1 (S y2)) = (S (Nat.add y1 y2)))))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term10 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term136 (x0 : nat) := (x0 = (NUMERAL x0)) -> False.
Definition term76 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term62 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term89 (x0 : nat) := ~ ((Nat.add (NUMERAL 0) (NUMERAL x0)) = (NUMERAL x0)).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term135 (x0 : nat) := (~ (x0 = (NUMERAL x0))) -> x0 = (NUMERAL x0).
Definition term28 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term112 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term25 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
