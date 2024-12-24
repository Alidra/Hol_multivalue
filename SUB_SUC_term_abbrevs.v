Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 (x0 : nat) := ((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) x0) -> (fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (S x0).
Definition term104 (x0 : nat) := Nat.pred (Nat.sub (S (S x0)) (NUMERAL 0)).
Definition term96 := Nat.pred (Nat.sub (S (NUMERAL 0)) (NUMERAL 0)).
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0))) x1.
Definition term92 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub x0 x1).
Definition term109 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub (S (S x0)) (S x1)).
Definition term99 := @eq nat (NUMERAL 0).
Definition term98 := @eq nat (Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0))).
Definition term84 (x0 : nat) := forall y0 : nat, (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0).
Definition term91 (x0 : nat) (x1 : nat) := Nat.sub x0 (S x1).
Definition term35 (x0 : nat) := Nat.sub (S (NUMERAL 0)) (S x0).
Definition term77 (x0 : nat) := ((Nat.sub (S (S x0)) (S (NUMERAL 0))) = (Nat.sub (S x0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) -> (Nat.sub (S (S x0)) (S (S y0))) = (Nat.sub (S x0) (S y0))).
Definition term49 := ((Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0))) = (Nat.sub (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) -> (Nat.sub (S (NUMERAL 0)) (S (S y0))) = (Nat.sub (NUMERAL 0) (S y0))).
Definition term58 (x0 : nat) := Nat.sub (S (S x0)) (S (NUMERAL 0)).
Definition term18 := forall y0 : nat, (forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) -> forall y1 : nat, (Nat.sub (S (S y0)) (S y1)) = (Nat.sub (S y0) y1).
Definition term41 (x0 : nat) := Nat.sub (NUMERAL 0) (S x0).
Definition term97 := S (NUMERAL 0).
Definition term61 (x0 : nat) := and ((Nat.sub (S (S x0)) (S (NUMERAL 0))) = (Nat.sub (S x0) (NUMERAL 0))).
Definition term38 (x0 : nat) := imp ((Nat.sub (S (NUMERAL 0)) (S x0)) = (Nat.sub (NUMERAL 0) x0)).
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0).
Definition term26 := ((forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) -> forall y1 : nat, (Nat.sub (S (S y0)) (S y1)) = (Nat.sub (S y0) y1))) -> forall y0 : nat, forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1).
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) x1.
Definition term81 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0.
Definition term53 := forall y0 : nat, (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0.
Definition term76 (x0 : nat) := ((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) (S y0)).
Definition term48 := ((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) (S y0)).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) x1.
Definition term94 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 (NUMERAL 0)) = y0) x0.
Definition term70 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) x1) -> (fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (S x1).
Definition term89 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0)).
Definition term55 (x0 : nat) := (((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0.
Definition term27 := (((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0.
Definition term1 := (((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0.
Definition term105 (x0 : nat) := S (S x0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term78 (x0 : nat) := imp (((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) (S y0))).
Definition term50 := imp (((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) (S y0))).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) (S y0))).
Definition term12 (x0 : nat) := forall y0 : nat, (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0).
Definition term4 := forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0).
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) x0.
Definition term74 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) (S y0).
Definition term46 := forall y0 : nat, ((fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) (S y0).
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) (S y0).
Definition term39 (x0 : nat) := (fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (S x0).
Definition term2 := fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1).
Definition term102 (x0 : nat) := @eq nat (Nat.sub (S (NUMERAL 0)) (S (S x0))).
Definition term110 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S (S x0)) (S (S x1))).
Definition term93 := forall y0 : nat, (Nat.sub y0 (NUMERAL 0)) = y0.
Definition term36 (x0 : nat) := Nat.sub (NUMERAL 0) x0.
Definition term106 (x0 : nat) := @eq nat (Nat.sub (S (S x0)) (S (NUMERAL 0))).
Definition term60 (x0 : nat) := and ((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (NUMERAL 0)).
Definition term32 := and ((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (NUMERAL 0)).
Definition term64 (x0 : nat) (x1 : nat) := Nat.sub (S x0) x1.
Definition term5 := and ((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (NUMERAL 0)).
Definition term10 (x0 : nat) := imp (forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)).
Definition term6 := and (forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (S x0).
Definition term71 (x0 : nat) (x1 : nat) := ((Nat.sub (S (S x0)) (S x1)) = (Nat.sub (S x0) x1)) -> (Nat.sub (S (S x0)) (S (S x1))) = (Nat.sub (S x0) (S x1)).
Definition term3 := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (NUMERAL 0).
Definition term72 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) (S y0).
Definition term44 := fun y0 : nat => ((fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0) -> (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) (S y0).
Definition term22 := imp ((forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) -> forall y1 : nat, (Nat.sub (S (S y0)) (S y1)) = (Nat.sub (S y0) y1))).
Definition term87 := forall y0 : nat, forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1).
Definition term28 := fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0).
Definition term100 (x0 : nat) := Nat.pred (Nat.sub (S (NUMERAL 0)) (S x0)).
Definition term65 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) x1).
Definition term103 (x0 : nat) := @eq nat (Nat.pred (Nat.sub (NUMERAL 0) x0)).
Definition term40 (x0 : nat) := Nat.sub (S (NUMERAL 0)) (S (S x0)).
Definition term82 (x0 : nat) := (((Nat.sub (S (S x0)) (S (NUMERAL 0))) = (Nat.sub (S x0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) -> (Nat.sub (S (S x0)) (S (S y0))) = (Nat.sub (S x0) (S y0)))) -> forall y0 : nat, (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0).
Definition term54 := (((Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0))) = (Nat.sub (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) -> (Nat.sub (S (NUMERAL 0)) (S (S y0))) = (Nat.sub (NUMERAL 0) (S y0)))) -> forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0).
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (S x1).
Definition term33 := and ((Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0))) = (Nat.sub (NUMERAL 0) (NUMERAL 0))).
Definition term16 := fun y0 : nat => (forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) -> forall y1 : nat, (Nat.sub (S (S y0)) (S y1)) = (Nat.sub (S y0) y1).
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) (S y0).
Definition term59 (x0 : nat) := Nat.sub (S x0) (NUMERAL 0).
Definition term56 (x0 : nat) := fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0).
Definition term57 (x0 : nat) := (fun y0 : nat => (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) (NUMERAL 0).
Definition term29 := (fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) (NUMERAL 0).
Definition term63 (x0 : nat) (x1 : nat) := Nat.sub (S (S x0)) (S x1).
Definition term20 := (forall y0 : nat, (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) -> forall y1 : nat, (Nat.sub (S (S y0)) (S y1)) = (Nat.sub (S y0) y1)).
Definition term107 (x0 : nat) := @eq nat (S x0).
Definition term30 := Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0)).
Definition term95 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term69 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0.
Definition term88 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1))) x0.
Definition term83 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pred (Nat.sub (S y0) y1)) = (Nat.sub y0 y1)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0.
Definition term68 (x0 : nat) (x1 : nat) := Nat.sub (S (S x0)) (S (S x1)).
Definition term101 (x0 : nat) := Nat.pred (Nat.sub (NUMERAL 0) x0).
Definition term19 := ((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) (S y0)).
Definition term73 (x0 : nat) := fun y0 : nat => ((Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) -> (Nat.sub (S (S x0)) (S (S y0))) = (Nat.sub (S x0) (S y0)).
Definition term45 := fun y0 : nat => ((Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) -> (Nat.sub (S (NUMERAL 0)) (S (S y0))) = (Nat.sub (NUMERAL 0) (S y0)).
Definition term111 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 x1).
Definition term86 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub (S x0) x1).
Definition term43 (x0 : nat) := ((Nat.sub (S (NUMERAL 0)) (S x0)) = (Nat.sub (NUMERAL 0) x0)) -> (Nat.sub (S (NUMERAL 0)) (S (S x0))) = (Nat.sub (NUMERAL 0) (S x0)).
Definition term79 (x0 : nat) := imp (((Nat.sub (S (S x0)) (S (NUMERAL 0))) = (Nat.sub (S x0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) -> (Nat.sub (S (S x0)) (S (S y0))) = (Nat.sub (S x0) (S y0)))).
Definition term51 := imp (((Nat.sub (S (NUMERAL 0)) (S (NUMERAL 0))) = (Nat.sub (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) -> (Nat.sub (S (NUMERAL 0)) (S (S y0))) = (Nat.sub (NUMERAL 0) (S y0)))).
Definition term66 (x0 : nat) (x1 : nat) := imp ((Nat.sub (S (S x0)) (S x1)) = (Nat.sub (S x0) x1)).
Definition term80 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.sub (S (S x0)) (S y1)) = (Nat.sub (S x0) y1)) y0.
Definition term52 := fun y0 : nat => (fun y1 : nat => (Nat.sub (S (NUMERAL 0)) (S y1)) = (Nat.sub (NUMERAL 0) y1)) y0.
Definition term85 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) x1.
Definition term75 (x0 : nat) := forall y0 : nat, ((Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0)) -> (Nat.sub (S (S x0)) (S (S y0))) = (Nat.sub (S x0) (S y0)).
Definition term47 := forall y0 : nat, ((Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) -> (Nat.sub (S (NUMERAL 0)) (S (S y0))) = (Nat.sub (NUMERAL 0) (S y0)).
Definition term31 := Nat.sub (NUMERAL 0) (NUMERAL 0).
Definition term37 (x0 : nat) := imp ((fun y0 : nat => (Nat.sub (S (NUMERAL 0)) (S y0)) = (Nat.sub (NUMERAL 0) y0)) x0).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0) -> (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) (S x0).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.sub (S y1) (S y2)) = (Nat.sub y1 y2)) y0.
Definition term14 (x0 : nat) := (forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) -> forall y0 : nat, (Nat.sub (S (S x0)) (S y0)) = (Nat.sub (S x0) y0).
