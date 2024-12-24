Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x2 y0)) (dist (@pair nat nat y0 x0))) (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))) y3) -> Peano.le (dist (@pair nat nat y0 y2)) y3) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))) y3) -> Peano.le (dist (@pair nat nat y0 y2)) y3) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term1 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term47 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term31 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))) y3) -> Peano.le (dist (@pair nat nat y0 y2)) y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := ((Peano.le (dist (@pair nat nat x0 x2)) x4) /\ (Peano.le (dist (@pair nat nat x1 x3)) x5)) -> Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5))) -> Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0) x2.
Definition term3 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat x2 y0)) (dist (@pair nat nat y0 x0))) (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (Nat.add x2 x3).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term50 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term52 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := ((Peano.le (dist (@pair nat nat x0 x4)) x2) /\ (Peano.le (dist (@pair nat nat x4 x1)) (Nat.add x3 (dist (@pair nat nat x4 x5))))) -> Peano.le (Nat.add (dist (@pair nat nat x0 x4)) (dist (@pair nat nat x4 x1))) (Nat.add x2 (Nat.add x3 (dist (@pair nat nat x4 x5)))).
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1) x1.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term54 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat x2 x0)) (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) x3) -> Peano.le (dist (@pair nat nat x1 x2)) x3.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat x0 x4)) x1) /\ (Peano.le (dist (@pair nat nat x4 x2)) (Nat.add x3 (dist (@pair nat nat x4 x5)))).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))) x3.
Definition term96 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le (dist (@pair nat nat y0 y1)) y4) /\ (Peano.le (dist (@pair nat nat y2 y3)) y5)) -> Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat y1 y3)) (Nat.add y4 y5)).
Definition term95 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le (dist (@pair nat nat x0 y0)) y3) /\ (Peano.le (dist (@pair nat nat y1 y2)) y4)) -> Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat y0 y2)) (Nat.add y3 y4)).
Definition term94 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le (dist (@pair nat nat x0 x1)) y2) /\ (Peano.le (dist (@pair nat nat y0 y1)) y3)) -> Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x1 y1)) (Nat.add y2 y3)).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le (dist (@pair nat nat x0 x2)) y1) /\ (Peano.le (dist (@pair nat nat x1 y0)) y2)) -> Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 y0)) (Nat.add y1 y2)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le (dist (@pair nat nat x0 x2)) y0) /\ (Peano.le (dist (@pair nat nat x1 x3)) y1)) -> Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add y0 y1)).
Definition term61 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term60 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term57 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term56 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term39 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term35 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term30 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1.
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1.
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))) y2) -> Peano.le (dist (@pair nat nat x0 y1)) y2.
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))) y3) -> Peano.le (dist (@pair nat nat y0 y2)) y3.
Definition term5 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1) x2.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))) y2) -> Peano.le (dist (@pair nat nat x0 y1)) y2) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := True /\ (Peano.le (dist (@pair nat nat x2 x0)) (Nat.add x1 (dist (@pair nat nat x2 x3)))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (dist (@pair nat nat x0 x1)) x2).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x2 x1))) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 x5)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x4)) (dist (@pair nat nat x4 x1))) (Nat.add (Nat.add x2 x3) (dist (@pair nat nat x4 x5))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x2 x3)) (dist (@pair nat nat x3 x0))) (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 y1)) = (dist (@pair nat nat y1 y0))) x0.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat x0 x1)) x2) /\ (Peano.le (dist (@pair nat nat x3 x4)) x5).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 x1) (dist (@pair nat nat x2 x3)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x0))) (Nat.add (dist (@pair nat nat x1 x2)) x3).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x2 y0)) (dist (@pair nat nat y0 x0))) (Nat.add x1 (dist (@pair nat nat x2 x3)))) -> Peano.le (dist (@pair nat nat x2 x0)) (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x4)) (dist (@pair nat nat x4 x1))) (Nat.add x2 (Nat.add x3 (dist (@pair nat nat x4 x5)))).
Definition term53 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, ((Peano.le (dist (@pair nat nat x0 x2)) x4) /\ (Peano.le (dist (@pair nat nat x1 x3)) y0)) -> Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat x2 x3)) (Nat.add x4 y0)).
Definition term84 (x0 : nat) (x1 : nat) := Peano.le (dist (@pair nat nat x0 x1)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (dist (@pair nat nat x1 x2)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat x0 x1)) x2.
Definition term51 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0))) x1.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term55 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term59 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term58 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0) x3.
