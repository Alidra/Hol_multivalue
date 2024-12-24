Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term105 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0)) x1.
Definition term46 (x0 : nat) := ((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) x0) -> (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (S x0).
Definition term3 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term90 := @eq nat (NUMERAL 0).
Definition term63 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term81 (x0 : nat) := (((Nat.sub (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (S x0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) -> ((Nat.sub (S x0) (S y0)) = (NUMERAL 0)) = (Peano.le (S x0) (S y0))).
Definition term53 := (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) -> ((Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S y0))).
Definition term23 := forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> forall y1 : nat, ((Nat.sub (S y0) y1) = (NUMERAL 0)) = (Peano.le (S y0) y1).
Definition term44 (x0 : nat) := Nat.sub (NUMERAL 0) (S x0).
Definition term103 (x0 : nat) := forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0).
Definition term100 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term13 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term31 := ((forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> forall y1 : nat, ((Nat.sub (S y0) y1) = (NUMERAL 0)) = (Peano.le (S y0) y1))) -> forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) x1.
Definition term85 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0.
Definition term57 := forall y0 : nat, (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0.
Definition term70 (x0 : nat) (x1 : nat) := imp (((Nat.sub (S x0) x1) = (NUMERAL 0)) = (Peano.le (S x0) x1)).
Definition term80 (x0 : nat) := ((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) (S y0)).
Definition term52 := ((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) (S y0)).
Definition term14 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) x0).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term38 := and (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term74 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) x1) -> (fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (S x1).
Definition term59 (x0 : nat) := (((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0.
Definition term32 := (((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0.
Definition term6 := (((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0.
Definition term5 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term82 (x0 : nat) := imp (((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) (S y0))).
Definition term54 := imp (((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) (S y0))).
Definition term26 := imp (((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) (S y0))).
Definition term17 (x0 : nat) := forall y0 : nat, ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0).
Definition term9 := forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0).
Definition term87 (x0 : nat) := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0)) x0.
Definition term78 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) (S y0).
Definition term50 := forall y0 : nat, ((fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) (S y0).
Definition term22 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) (S y0).
Definition term43 (x0 : nat) := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (S x0).
Definition term7 := fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term66 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) x1.
Definition term40 (x0 : nat) := Nat.sub (NUMERAL 0) x0.
Definition term64 (x0 : nat) := and ((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (NUMERAL 0)).
Definition term37 := and ((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (NUMERAL 0)).
Definition term67 (x0 : nat) (x1 : nat) := Nat.sub (S x0) x1.
Definition term10 := and ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (NUMERAL 0)).
Definition term15 (x0 : nat) := imp (forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0)).
Definition term11 := and (forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (S x0).
Definition term8 := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (NUMERAL 0).
Definition term76 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) (S y0).
Definition term48 := fun y0 : nat => ((fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) (S y0).
Definition term101 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term60 (x0 : nat) := fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0).
Definition term27 := imp ((forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> forall y1 : nat, ((Nat.sub (S y0) y1) = (NUMERAL 0)) = (Peano.le (S y0) y1))).
Definition term30 := forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term47 (x0 : nat) := (((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) x0)) -> ((Nat.sub (NUMERAL 0) (S x0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S x0)).
Definition term106 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S x0) (S x1)).
Definition term69 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) x1).
Definition term33 := fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0).
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term77 (x0 : nat) := fun y0 : nat => (((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) -> ((Nat.sub (S x0) (S y0)) = (NUMERAL 0)) = (Peano.le (S x0) (S y0)).
Definition term49 := fun y0 : nat => (((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) -> ((Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S y0)).
Definition term86 (x0 : nat) := ((((Nat.sub (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (S x0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) -> ((Nat.sub (S x0) (S y0)) = (NUMERAL 0)) = (Peano.le (S x0) (S y0)))) -> forall y0 : nat, ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0).
Definition term58 := ((((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) -> ((Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S y0)))) -> forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0).
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term71 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (S x1).
Definition term21 := fun y0 : nat => (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> forall y1 : nat, ((Nat.sub (S y0) y1) = (NUMERAL 0)) = (Peano.le (S y0) y1).
Definition term20 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) (S y0).
Definition term62 (x0 : nat) := Nat.sub (S x0) (NUMERAL 0).
Definition term61 (x0 : nat) := (fun y0 : nat => ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) (NUMERAL 0).
Definition term34 := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) (NUMERAL 0).
Definition term39 (x0 : nat) := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) x0.
Definition term25 := (forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) -> forall y1 : nat, ((Nat.sub (S y0) y1) = (NUMERAL 0)) = (Peano.le (S y0) y1)).
Definition term96 (x0 : nat) := @eq nat (S x0).
Definition term108 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.sub (S x0) (S x1)) = (NUMERAL 0)).
Definition term93 (x0 : nat) := @eq Prop ((Nat.sub (NUMERAL 0) (S x0)) = (NUMERAL 0)).
Definition term94 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term72 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term28 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0.
Definition term102 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0.
Definition term99 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) x0.
Definition term95 (x0 : nat) := @eq nat (Nat.sub (S x0) (NUMERAL 0)).
Definition term88 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ ((Nat.sub x0 (NUMERAL 0)) = x0).
Definition term24 := ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) (S y0)).
Definition term45 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term89 := @eq nat (Nat.sub (NUMERAL 0) (NUMERAL 0)).
Definition term107 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 x1).
Definition term98 (x0 : nat) := @eq Prop ((S x0) = (NUMERAL 0)).
Definition term2 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term68 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term42 (x0 : nat) := imp (((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) x0)).
Definition term75 (x0 : nat) (x1 : nat) := (((Nat.sub (S x0) x1) = (NUMERAL 0)) = (Peano.le (S x0) x1)) -> ((Nat.sub (S x0) (S x1)) = (NUMERAL 0)) = (Peano.le (S x0) (S x1)).
Definition term92 (x0 : nat) := @eq nat (Nat.sub (NUMERAL 0) (S x0)).
Definition term83 (x0 : nat) := imp ((((Nat.sub (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (S x0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) -> ((Nat.sub (S x0) (S y0)) = (NUMERAL 0)) = (Peano.le (S x0) (S y0)))).
Definition term55 := imp ((((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) -> ((Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S y0)))).
Definition term84 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.sub (S x0) y1) = (NUMERAL 0)) = (Peano.le (S x0) y1)) y0.
Definition term56 := fun y0 : nat => (fun y1 : nat => ((Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y1)) y0.
Definition term79 (x0 : nat) := forall y0 : nat, (((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0)) -> ((Nat.sub (S x0) (S y0)) = (NUMERAL 0)) = (Peano.le (S x0) (S y0)).
Definition term51 := forall y0 : nat, (((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) -> ((Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) (S y0)).
Definition term35 := Nat.sub (NUMERAL 0) (NUMERAL 0).
Definition term65 (x0 : nat) := and (((Nat.sub (S x0) (NUMERAL 0)) = (NUMERAL 0)) = (Peano.le (S x0) (NUMERAL 0))).
Definition term73 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term41 (x0 : nat) := imp ((fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) = (Peano.le (NUMERAL 0) y0)) x0).
Definition term18 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) x0) -> (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) (S x0).
Definition term97 (x0 : nat) := @eq Prop ((Nat.sub (S x0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term91 := @eq Prop ((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term29 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.sub y1 y2) = (NUMERAL 0)) = (Peano.le y1 y2)) y0.
Definition term4 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term36 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term19 (x0 : nat) := (forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0)) -> forall y0 : nat, ((Nat.sub (S x0) y0) = (NUMERAL 0)) = (Peano.le (S x0) y0).
