Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term96 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) (Nat.add (dest_nadd x2 y1) (dest_nadd x3 y1)))) y0.
Definition term70 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) y1) (dest_nadd (nadd_add x2 x3) y1))) y0.
Definition term62 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term86 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) x4) (dest_nadd (nadd_add x2 x3) x4))).
Definition term84 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := dist (@pair nat nat (dest_nadd (nadd_add x0 x1) x4) (dest_nadd (nadd_add x2 x3) x4)).
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3)))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term64 (x0 : nadd) (x1 : nadd) := and (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0).
Definition term107 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 x4) (dest_nadd x1 x4))) (dist (@pair nat nat (dest_nadd x2 x4) (dest_nadd x3 x4)))) (Nat.add x5 x6).
Definition term53 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term33 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term12 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) x4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term114 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_add y0 y2) (nadd_add y1 y3).
Definition term113 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_add x0 y1) (nadd_add y0 y2).
Definition term112 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_add x0 y0) (nadd_add x1 y1).
Definition term76 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x0 x2) (dest_nadd x1 x2).
Definition term79 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x2).
Definition term65 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term71 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_add x0 x1) x2.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))).
Definition term81 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.add (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term103 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2) x3.
Definition term98 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x2 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 y1) (dest_nadd x3 y1))) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) (Nat.add (dest_nadd x2 y1) (dest_nadd x3 y1)))) y0.
Definition term31 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term57 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_add x0 x1).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4)))).
Definition term67 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((nadd_eq x0 x1) /\ (nadd_eq x2 x3)).
Definition term69 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_add x0 x1) (nadd_add x2 x3).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))) x4.
Definition term72 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x2.
Definition term78 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0) x2).
Definition term56 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1))) x1.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term80 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd (nadd_add x0 x1) x2).
Definition term91 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) (Nat.add (dest_nadd x2 y0) (dest_nadd x3 y0)))) x4.
Definition term90 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) y0) (dest_nadd (nadd_add x2 x3) y0))) x4.
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) x4) (dest_nadd (nadd_add x2 x3) x4))) x5.
Definition term106 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nadd) (x4 : nadd) (x5 : nat) (x6 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x0 x5) (dest_nadd x1 x5))) x2) /\ (Peano.le (dist (@pair nat nat (dest_nadd x3 x5) (dest_nadd x4 x5))) x6).
Definition term25 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term61 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term30 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1) x3.
Definition term43 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3.
Definition term41 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1.
Definition term32 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term21 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term89 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4)))) x5.
Definition term68 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 y1) (dest_nadd x3 y1))) y0)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term102 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1)))) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3) x1.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term83 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := @pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4)).
Definition term63 (x0 : nadd) (x1 : nadd) := and (nadd_eq x0 x1).
Definition term55 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)).
Definition term74 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term54 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_add y0 y1)) = (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2))) x0.
Definition term99 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term97 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> nadd_eq (nadd_add x0 x1) (nadd_add x2 x3).
Definition term85 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := dist (@pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4))).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3)).
Definition term100 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := (Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 x4) (dest_nadd x2 x4))) (dist (@pair nat nat (dest_nadd x1 x4) (dest_nadd x3 x4)))) (Nat.add x5 x6)) -> Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4)))) (Nat.add x5 x6).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2) x2.
Definition term75 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0) x2.
Definition term101 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := ((Peano.le (dist (@pair nat nat (dest_nadd x0 x4) (dest_nadd x1 x4))) x5) /\ (Peano.le (dist (@pair nat nat (dest_nadd x2 x4) (dest_nadd x3 x4))) x6)) -> Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 x4) (dest_nadd x1 x4))) (dist (@pair nat nat (dest_nadd x2 x4) (dest_nadd x3 x4)))) (Nat.add x5 x6).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0) x4.
Definition term93 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) (Nat.add (dest_nadd x2 y0) (dest_nadd x3 y0)))) x4.
Definition term92 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) y0) (dest_nadd (nadd_add x2 x3) y0))) x4.
Definition term110 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term95 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) (Nat.add (dest_nadd x2 y1) (dest_nadd x3 y1)))) y0.
Definition term94 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_add x0 x1) y1) (dest_nadd (nadd_add x2 x3) y1))) y0.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term109 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) (Nat.add (dest_nadd x2 y0) (dest_nadd x3 y0)))) (Nat.add x4 x5).
Definition term82 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) := @pair nat nat (dest_nadd (nadd_add x0 x1) x4) (dest_nadd (nadd_add x2 x3) x4).
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term66 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 y1) (dest_nadd x3 y1))) y0).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term111 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_add x0 x1) (nadd_add x2 y0).
Definition term104 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3.
Definition term58 (x0 : nadd) (x1 : nadd) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0).
Definition term105 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3).
Definition term60 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0)))) x3.
Definition term77 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0.
Definition term108 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4)) (Nat.add (dest_nadd x2 x4) (dest_nadd x3 x4)))) (Nat.add x5 x6).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0))).
