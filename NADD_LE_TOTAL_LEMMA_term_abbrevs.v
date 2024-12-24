Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term119 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.lt (Nat.add (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 x3)) -> Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3).
Definition term74 (x0 : nadd) (x1 : nat) (x2 : nadd) := (fun y0 : nat => exists y1 : nat, Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x2 y1)) (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term24 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term76 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat, Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))) (dest_nadd x2 y0).
Definition term103 := @eq nat (NUMERAL 0).
Definition term128 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term89 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (dest_nadd x0 x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))).
Definition term71 (x0 : nadd) (x1 : nadd) := forall y0 : nat, exists y1 : nat, Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1).
Definition term63 (x0 : nadd) (x1 : nadd) := forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term60 (x0 : nadd) (x1 : nadd) := forall y0 : nat, exists y1 : nat, ~ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term112 (x0 : nadd) (x1 : nat) (x2 : nadd) := ~ (Peano.lt (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))).
Definition term37 (x0 : nadd) (x1 : nadd) := @eq Prop (~ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))).
Definition term36 (x0 : nadd) (x1 : nadd) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0)).
Definition term139 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term73 (x0 : nadd) (x1 : nadd) := (forall y0 : nat, exists y1 : nat, Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)) -> forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term65 (x0 : nadd) (x1 : nadd) := (forall y0 : nat, exists y1 : nat, ~ (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0))) -> forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term107 (x0 : nadd) (x1 : nat) (x2 : nadd) := Peano.lt (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0)).
Definition term150 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := (Peano.le (Nat.add (dest_nadd x0 x1) x2) (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0)))) -> Peano.le (dest_nadd x3 x1) (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term47 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term156 := forall y0 : nadd, forall y1 : nadd, (~ (nadd_le y0 y1)) -> forall y2 : nat, exists y3 : nat, (~ (y3 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y1 y3) y2) (dest_nadd y0 y3)).
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term109 (x0 : nadd) (x1 : nat) (x2 : nadd) := False /\ (Peano.lt (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))).
Definition term67 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 x1) x2.
Definition term51 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0.
Definition term68 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0).
Definition term123 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := imp (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3)).
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := ~ (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3)).
Definition term110 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.lt (Nat.add (dest_nadd x0 x3) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))) (dest_nadd x2 x3)) -> (~ (x3 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3)).
Definition term39 (x0 : nadd) (x1 : nadd) (x2 : nat) := ~ (forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term95 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (dest_nadd x0 x1) x2).
Definition term48 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3.
Definition term111 (x0 : nadd) (x1 : nat) (x2 : nadd) := (Peano.lt (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))) -> False.
Definition term137 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term153 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0)).
Definition term77 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.lt (Nat.add (dest_nadd x0 x3) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))) (dest_nadd x2 x3).
Definition term66 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term57 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => ~ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term85 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term70 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1).
Definition term58 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, ~ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term116 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.lt (Nat.add (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 x3).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term130 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term10 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term31 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term118 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := True /\ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3)).
Definition term91 (x0 : nadd) := dest_nadd x0 (NUMERAL 0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term146 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2) x3.
Definition term117 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := imp (Peano.lt (Nat.add (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 x3)).
Definition term101 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := imp (Peano.lt (Nat.add (dest_nadd x0 x3) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))) (dest_nadd x2 x3)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term122 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := imp (~ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3))).
Definition term14 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term152 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0)).
Definition term96 (x0 : nadd) (x1 : nat) := Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1).
Definition term131 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term23 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term59 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, ~ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term125 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dest_nadd x3 x1) (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term136 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term138 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term129 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term127 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term108 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (~ (x3 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3)).
Definition term9 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)) x2.
Definition term12 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term5 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term61 (x0 : nadd) (x1 : nadd) := imp (~ (nadd_le x0 x1)).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term28 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term50 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0.
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : nat) := ~ (forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term93 (x0 : nadd) := Nat.add (dest_nadd x0 (NUMERAL 0)).
Definition term105 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (dest_nadd x0 x1) x2).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term69 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat, Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0).
Definition term29 (x0 : nadd) (x1 : nadd) := ~ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0).
Definition term148 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0) -> Peano.le (dest_nadd x2 x3) x4.
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3).
Definition term147 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) x2.
Definition term40 (x0 : nadd) (x1 : nadd) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0).
Definition term75 (x0 : nat) (x1 : nadd) := Nat.add x0 (dest_nadd x1 (NUMERAL 0)).
Definition term144 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0) x4.
Definition term115 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.lt (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term104 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term99 (x0 : nadd) (x1 : nat) (x2 : nadd) := Peano.lt (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))).
Definition term7 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term102 (x0 : nadd) (x1 : nat) (x2 : nadd) := imp (Peano.lt (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))).
Definition term30 (x0 : nadd) (x1 : nadd) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0).
Definition term113 (x0 : nadd) (x1 : nat) (x2 : nadd) := Peano.le (dest_nadd x2 (NUMERAL 0)) (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))).
Definition term81 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term34 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0.
Definition term90 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0)).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term97 (x0 : nadd) (x1 : nat) (x2 : nadd) := Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0)).
Definition term140 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term78 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq Prop (~ (forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2))).
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq Prop (~ (forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0)).
Definition term41 (x0 : nadd) (x1 : nadd) := fun y0 : nat => ~ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term143 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term142 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le (dest_nadd x2 x3) (Nat.add (dest_nadd x0 x3) x1)) -> forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term120 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (~ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3))) -> ~ (Peano.lt (Nat.add (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 x3)).
Definition term100 (x0 : nadd) (x1 : nat) (x2 : nadd) := Peano.lt (Nat.add (Nat.add (dest_nadd x0 (NUMERAL 0)) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0)).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term26 (x0 : nadd) (x1 : nadd) := ~ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term42 (x0 : nadd) (x1 : nadd) := forall y0 : nat, ~ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term49 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3).
Definition term114 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term155 (x0 : nadd) := forall y0 : nadd, (~ (nadd_le x0 y0)) -> forall y1 : nat, exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y0 y2) y1) (dest_nadd x0 y2)).
Definition term22 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term106 (x0 : nadd) (x1 : nat) := Peano.lt (Nat.add (dest_nadd x0 (NUMERAL 0)) x1).
Definition term43 (x0 : nat -> Prop) := ~ (forall y0 : nat, x0 y0).
Definition term35 (x0 : nadd) (x1 : nadd) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd x1 y2) y1)) y0.
Definition term98 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.lt (Nat.add (dest_nadd x0 x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term27 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term92 (x0 : nadd) (x1 : nat) := Nat.add (dest_nadd x0 x1).
Definition term135 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term25 (x0 : nadd) (x1 : nadd) := ~ (nadd_le x0 x1).
Definition term151 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (Nat.add (dest_nadd x0 x1) x2) (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) x1.
Definition term94 (x0 : nadd) (x1 : nat) := Nat.add (dest_nadd x0 (NUMERAL 0)) x1.
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nat) := ~ ((fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)) x2).
Definition term126 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := (Peano.le (dest_nadd x3 x1) (Nat.add (dest_nadd x0 x1) x2)) -> Peano.le (dest_nadd x3 x1) (Nat.add (Nat.add (dest_nadd x0 x1) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term64 (x0 : nadd) (x1 : nadd) := (~ (nadd_le x1 x0)) -> forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term72 (x0 : nadd) (x1 : nadd) := imp (forall y0 : nat, exists y1 : nat, Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term62 (x0 : nadd) (x1 : nadd) := imp (forall y0 : nat, exists y1 : nat, ~ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))).
Definition term44 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term145 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dest_nadd x0 x3) x1) x4) -> Peano.le (dest_nadd x2 x3) x4.
Definition term124 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := ~ (Peano.lt (Nat.add (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 x3)).
Definition term8 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term141 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term79 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term154 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))) (dest_nadd x2 y0).
Definition term121 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := ~ (Peano.lt (Nat.add (dest_nadd x0 x3) x1) (dest_nadd x2 x3)).
Definition term149 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0) -> forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
