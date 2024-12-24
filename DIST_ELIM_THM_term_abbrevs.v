Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x0 = (Nat.add (Nat.add x0 x1) x3)) -> x2 x3) /\ ((x1 = x3) -> x2 x3).
Definition term158 (x0 : nat -> Prop) (x1 : nat) := (x1 = x1) -> x0 x1.
Definition term135 := @eq nat (NUMERAL 0).
Definition term28 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term69 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (dist (@pair nat nat x1 x2)).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x3 = x0) -> x2 x3) /\ (((Nat.add (Nat.add x1 x0) x3) = x1) -> x2 x3).
Definition term156 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (forall y0 : nat, (y0 = x0) -> x1 y0) -> x1 x2.
Definition term128 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))) -> x1 y0) /\ ((y0 = x0) -> x1 y0).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (x0 = (Nat.add (Nat.add x0 x1) x3)) -> x2 x3.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := and ((x0 = (Nat.add (Nat.add x0 x1) x3)) -> x2 x3).
Definition term165 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term145 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term88 (x0 : nat -> Prop) (x1 : nat) := x0 (Nat.add x1 (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term73 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 (dist (@pair nat nat y0 x0))) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) -> x1 y1) /\ ((x0 = (Nat.add y0 y1)) -> x1 y1))) x2.
Definition term64 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 (dist (@pair nat nat x0 y0))) = (forall y1 : nat, ((x0 = (Nat.add y0 y1)) -> x1 y1) /\ ((y0 = (Nat.add x0 y1)) -> x1 y1))) x2.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add (Nat.add x0 x1) x2)).
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term56 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x1 = y0) -> x2 y0) /\ ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0).
Definition term53 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term159 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (y0 = x1) -> x0 y0) -> x0 x1.
Definition term152 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0) -> x0 x1.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := and (((Nat.add x1 x0) = (Nat.add x1 x3)) -> x2 x3).
Definition term37 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term136 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term89 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop (x0 (dist (@pair nat nat (Nat.add x2 x1) x2))).
Definition term162 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0.
Definition term5 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term131 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((y0 = x0) -> x1 y0) /\ (((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))) -> x1 y0).
Definition term143 (x0 : nat -> Prop) := forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term27 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term90 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 (Nat.add x1 (NUMERAL 0))).
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term137 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((Nat.add (Nat.add x1 x0) x3) = x1) -> x2 x3.
Definition term38 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term141 (x0 : nat -> Prop) (x1 : nat) := ((x1 = (NUMERAL 0)) -> x0 x1) /\ ((x1 = (NUMERAL 0)) -> x0 x1).
Definition term126 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and (((x0 = (NUMERAL 0)) /\ (x2 = (NUMERAL 0))) -> x1 x2).
Definition term18 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = x0) = (y0 = (NUMERAL 0))) x1.
Definition term20 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term2 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term9 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term140 (x0 : nat -> Prop) (x1 : nat) := and ((x1 = (NUMERAL 0)) -> x0 x1).
Definition term60 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term138 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term36 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term146 (x0 : nat -> Prop) (x1 : nat) := False -> x0 x1.
Definition term103 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((x0 = x2) -> x1 x2).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((x2 (dist (@pair nat nat x1 x0))) = (forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> x2 y0) /\ ((x0 = (Nat.add x1 y0)) -> x2 y0))).
Definition term142 (x0 : nat -> Prop) := fun y0 : nat => (y0 = (NUMERAL 0)) -> x0 y0.
Definition term124 (x0 : nat) (x1 : nat) := imp ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.add x1 x2)).
Definition term161 (x0 : nat -> Prop) := (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0) -> x0 (NUMERAL 0).
Definition term93 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term58 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term41 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term118 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((x2 = x0) -> x1 x2).
Definition term91 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 x1).
Definition term125 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x0 = (NUMERAL 0)) /\ (x2 = (NUMERAL 0))) -> x1 x2.
Definition term49 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term160 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) -> forall y0 : nat, (y0 = x0) -> x1 y0.
Definition term163 (x0 : nat -> Prop) (x1 : nat) := ((x0 x1) -> forall y0 : nat, (y0 = x1) -> x0 y0) /\ ((forall y0 : nat, (y0 = x1) -> x0 y0) -> x0 x1).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term16 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term15 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term11 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term1 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add x0 x1) x2).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (((Nat.add x0 x1) = (Nat.add x0 y0)) -> x2 y0) /\ ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x1 = (Nat.add (Nat.add x1 x0) y0)) -> x2 y0) /\ (((Nat.add x1 x0) = (Nat.add x1 y0)) -> x2 y0).
Definition term79 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x1 (Nat.add x1 x0)) (Nat.sub (Nat.add x1 x0) x1).
Definition term114 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) -> x1 x2.
Definition term47 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term39 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term40 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0)) x1.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term132 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((y0 = x0) -> x1 y0) /\ (((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))) -> x1 y0).
Definition term129 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))) -> x1 y0) /\ ((y0 = x0) -> x1 y0).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((y0 = x0) -> x2 y0) /\ (((Nat.add (Nat.add x1 x0) y0) = x1) -> x2 y0).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, (((Nat.add (Nat.add x0 x1) y0) = x0) -> x2 y0) /\ ((y0 = x1) -> x2 y0).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x1 = y0) -> x2 y0) /\ ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0) /\ ((x1 = y0) -> x2 y0).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, (((Nat.add x0 x1) = (Nat.add x0 y0)) -> x2 y0) /\ ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> x2 y0) /\ ((x0 = (Nat.add x1 y0)) -> x2 y0).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x1 = (Nat.add (Nat.add x1 x0) y0)) -> x2 y0) /\ (((Nat.add x1 x0) = (Nat.add x1 y0)) -> x2 y0).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := and (((Nat.add (Nat.add x1 x0) x3) = x1) -> x2 x3).
Definition term80 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 (Nat.add x0 x1)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x1 = x3) -> x2 x3) /\ ((x0 = (Nat.add (Nat.add x0 x1) x3)) -> x2 x3).
Definition term164 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) -> forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0) /\ ((forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0) -> x0 (NUMERAL 0)).
Definition term78 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 (Nat.add x0 x1)).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x1 = (Nat.add (Nat.add x1 x0) x3)) -> x2 x3) /\ (((Nat.add x1 x0) = (Nat.add x1 x3)) -> x2 x3).
Definition term62 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term82 (x0 : nat -> Prop) (x1 : nat) := x0 (Nat.add (NUMERAL 0) x1).
Definition term85 (x0 : nat) (x1 : nat) := dist (@pair nat nat (Nat.add x1 x0) x1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term134 (x0 : nat -> Prop) := @eq Prop (x0 (NUMERAL 0)).
Definition term127 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (((x0 = (NUMERAL 0)) /\ (x2 = (NUMERAL 0))) -> x1 x2) /\ ((x2 = x0) -> x1 x2).
Definition term95 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x0 = x2) -> x1 x2.
Definition term86 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add x0 x1) x0) (Nat.sub x0 (Nat.add x0 x1)).
Definition term35 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term72 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 (dist (@pair nat nat y0 x0))) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) -> x1 y1) /\ ((x0 = (Nat.add y0 y1)) -> x1 y1)).
Definition term63 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 (dist (@pair nat nat x0 y0))) = (forall y1 : nat, ((x0 = (Nat.add y0 y1)) -> x1 y1) /\ ((y0 = (Nat.add x0 y1)) -> x1 y1)).
Definition term81 := Nat.add (NUMERAL 0).
Definition term149 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (y0 = x0) -> x1 y0.
Definition term133 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term130 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x2 = x0) -> x1 x2) /\ (((x0 = (NUMERAL 0)) /\ (x2 = (NUMERAL 0))) -> x1 x2).
Definition term45 (x0 : nat) (x1 : nat) := Nat.sub x0 (Nat.add x0 x1).
Definition term83 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop (x0 (dist (@pair nat nat x1 (Nat.add x1 x2)))).
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y1 y0)) = (Nat.add (Nat.sub y1 y0) (Nat.sub y0 y1))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (Nat.add y0 y1)) = (NUMERAL 0)) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = y0) = (y1 = (NUMERAL 0))) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term43 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term75 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (dist (@pair nat nat (Nat.add x2 x1) x2)).
Definition term54 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1).
Definition term74 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 (dist (@pair nat nat y0 x1))) = (forall y1 : nat, ((y0 = (Nat.add x1 y1)) -> x0 y1) /\ ((x1 = (Nat.add y0 y1)) -> x0 y1))) (Nat.add x1 x2).
Definition term65 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 (dist (@pair nat nat x1 y0))) = (forall y1 : nat, ((x1 = (Nat.add y0 y1)) -> x0 y1) /\ ((y0 = (Nat.add x1 y1)) -> x0 y1))) (Nat.add x1 x2).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
Definition term144 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term77 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((fun y0 : nat => (x1 (dist (@pair nat nat y0 x0))) = (forall y1 : nat, ((y0 = (Nat.add x0 y1)) -> x1 y1) /\ ((x0 = (Nat.add y0 y1)) -> x1 y1))) x2).
Definition term68 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((fun y0 : nat => (x1 (dist (@pair nat nat x0 y0))) = (forall y1 : nat, ((x0 = (Nat.add y0 y1)) -> x1 y1) /\ ((y0 = (Nat.add x0 y1)) -> x1 y1))) x2).
Definition term151 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) -> x0 y0) x1.
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.add x2 x0) x1) = x2).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (((Nat.add (Nat.add x0 x1) x3) = x0) -> x2 x3) /\ ((x3 = x1) -> x2 x3).
Definition term147 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := True /\ ((x2 = x0) -> x1 x2).
Definition term51 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0)).
Definition term150 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x2 = x0) -> x1 x2) /\ True.
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (((Nat.add x0 x1) = (Nat.add x0 x3)) -> x2 x3) /\ ((x0 = (Nat.add (Nat.add x0 x1) x3)) -> x2 x3).
Definition term6 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term139 (x0 : nat -> Prop) (x1 : nat) := (x1 = (NUMERAL 0)) -> x0 x1.
Definition term22 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = x0) = (y0 = (NUMERAL 0)).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((y0 = x0) -> x2 y0) /\ (((Nat.add (Nat.add x1 x0) y0) = x1) -> x2 y0).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => (((Nat.add (Nat.add x0 x1) y0) = x0) -> x2 y0) /\ ((y0 = x1) -> x2 y0).
Definition term57 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term155 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (y0 = x0) -> x1 y0) x2.
Definition term84 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 (Nat.add (NUMERAL 0) x1)).
Definition term66 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (dist (@pair nat nat x1 (Nat.add x1 x2))).
Definition term154 (x0 : nat -> Prop) := ((NUMERAL 0) = (NUMERAL 0)) -> x0 (NUMERAL 0).
Definition term148 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (y0 = x0) -> x1 y0.
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0))) x1.
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term10 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term87 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add x1 x0) x1).
Definition term14 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term13 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add x1 x0) = (Nat.add x1 x2)).
Definition term157 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (y0 = x0) -> x1 y0) -> forall y0 : nat, (y0 = x0) -> x1 y0.
Definition term153 (x0 : nat -> Prop) := (forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0) -> forall y0 : nat, (y0 = (NUMERAL 0)) -> x0 y0.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((Nat.add x1 x0) = (Nat.add x1 x3)) -> x2 x3.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x0 = (Nat.add (Nat.add x0 x1) y0)) -> x2 y0) /\ ((x1 = y0) -> x2 y0).
