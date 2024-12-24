Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le x1 (Nat.div x2 x3)) = x5) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3)) = (x4 -> x5).
Definition term136 (x0 : nat -> Prop) := ~ (all x0).
Definition term58 := (~ False) -> False.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2.
Definition term116 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x1) -> (~ (x0 = (NUMERAL 0))) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.mul x0 y1) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False.
Definition term119 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x1) -> (~ (x0 = (NUMERAL 0))) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.mul x0 y1) x1)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3).
Definition term118 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x1) -> (~ (x0 = (NUMERAL 0))) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.mul x0 y1) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False.
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x0) -> Peano.le y0 x1.
Definition term51 (x0 : Prop) := ~ (~ x0).
Definition term182 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y2 y0) -> (~ (y1 = (NUMERAL 0))) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.mul y1 y3) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> False) x0.
Definition term157 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term73 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term61 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1) -> Peano.le x0 x1.
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term11 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) /\ (~ (Peano.le (Nat.mul x1 y0) x2)).
Definition term117 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x1) -> (~ (x0 = (NUMERAL 0))) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.mul x0 y1) x1)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3).
Definition term15 := (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term13 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) \/ (~ (Peano.le x1 x2)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le (Nat.mul x1 x2) x3) -> (Peano.le x2 (Nat.div x0 x1)) = x4) -> ((Peano.le x2 (Nat.div x3 x1)) -> Peano.le x2 (Nat.div x0 x1)) = ((Peano.le (Nat.mul x1 x2) x3) -> x4).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term152 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x1 y0) x0) /\ (~ (Peano.le (Nat.mul x1 y0) x2)).
Definition term28 := fun y0 : nat => Peano.le y0 y0.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.mul x1 x2) x0) -> (Peano.le x2 (Nat.div x3 x1)) = (Peano.le (Nat.mul x1 x2) x3)) -> ((Peano.le x2 (Nat.div x0 x1)) -> Peano.le x2 (Nat.div x3 x1)) = ((Peano.le (Nat.mul x1 x2) x0) -> Peano.le (Nat.mul x1 x2) x3).
Definition term19 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term62 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1) -> (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1.
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1.
Definition term49 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2).
Definition term107 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term54 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term45 (x0 : Prop) := (~ x0) -> x0.
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x0 x1) x2) /\ (Peano.le x2 x3).
Definition term112 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term172 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term44 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term56 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le x2 (Nat.div x3 x1)) = (Peano.le (Nat.mul x1 x2) x3)) -> ((Peano.le (Nat.mul x1 x2) x3) -> (Peano.le x2 (Nat.div x0 x1)) = x4) -> ((Peano.le x2 (Nat.div x3 x1)) -> Peano.le x2 (Nat.div x0 x1)) = ((Peano.le (Nat.mul x1 x2) x3) -> x4).
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x0 x1) x2).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, (Peano.le y0 (Nat.div x0 x2)) -> Peano.le y0 (Nat.div x1 x2)) -> Peano.le (Nat.div x0 x2) (Nat.div x1 x2).
Definition term43 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term183 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 x0) -> (~ (y0 = (NUMERAL 0))) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.mul y0 y2) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False) x1.
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x1 x2) x0) -> Peano.le (Nat.mul x1 x2) x3.
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term68 (x0 : nat) (x1 : nat) := Peano.le (Nat.div x0 x1).
Definition term65 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term153 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term131 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term21 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> ~ (forall y1 : nat, Peano.le y1 y1).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x1 x2) x0) -> (Peano.le x2 (Nat.div x3 x1)) = (Peano.le (Nat.mul x1 x2) x3).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le (Nat.mul x1 x2) x0) -> Peano.le (Nat.mul x1 x2) x3).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x0 x1) x2)) -> Peano.le (Nat.mul x0 x1) x2.
Definition term82 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term41 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term36 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term151 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term66 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term186 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 x1) -> Peano.le (Nat.div x0 y0) (Nat.div x1 y0).
Definition term106 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term35 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term32 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1).
Definition term38 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)).
Definition term37 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1.
Definition term171 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term188 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> Peano.le (Nat.div y0 y2) (Nat.div y1 y2).
Definition term187 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.div x0 y1) (Nat.div y0 y1).
Definition term156 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term154 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term132 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term127 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y2 y0) -> (~ (y1 = (NUMERAL 0))) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.mul y1 y3) y0)) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5).
Definition term126 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y2 y0) -> (~ (y1 = (NUMERAL 0))) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.mul y1 y3) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> False.
Definition term123 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le y1 x0) -> (~ (y0 = (NUMERAL 0))) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.mul y0 y2) x0)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4).
Definition term122 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le y1 x0) -> (~ (y0 = (NUMERAL 0))) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.mul y0 y2) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False.
Definition term108 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term74 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term27 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> ~ (forall y2 : nat, Peano.le y2 y2).
Definition term26 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> False.
Definition term64 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> Peano.le (Nat.div x0 x2) (Nat.div x1 x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.mul x1 x2) x0) /\ (Peano.le x0 x3)) -> Peano.le (Nat.mul x1 x2) x3.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x0 x1) x2) -> False.
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le y0 (Nat.div x0 x2)) -> Peano.le y0 (Nat.div x1 x2).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2) x3).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> False.
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> ((Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> False) x1.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le x1 (Nat.div x2 x3)) = y0) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3)) = (x4 -> y0).
Definition term83 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term40 (x0 : nat) (x1 : nat) := (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) /\ (~ (Peano.le x0 x1)).
Definition term39 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) /\ (~ (Peano.le x0 x1)).
Definition term22 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> False.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = y0) -> (y0 -> (Peano.le x1 (Nat.div x2 x3)) = y1) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3)) = (y0 -> y1).
Definition term84 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term10 (x0 : nat) (x1 : nat) := ~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term175 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term130 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term165 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term18 (x0 : nat) (x1 : nat) := imp (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x1 x2) x0) /\ (~ (Peano.le (Nat.mul x1 x2) x3)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le x1 (Nat.div x2 x3)) = y0) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3)) = (x4 -> y0)) x5.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> False) x0.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.le x1 x2.
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term12 (x0 : nat) (x1 : nat) := ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term52 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x1 x0) \/ (~ (Peano.le x1 x2))).
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term34 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.le (Nat.mul x1 y1) x0) -> Peano.le (Nat.mul x1 y1) x2) y0).
Definition term17 := forall y0 : nat, Peano.le y0 y0.
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term129 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term81 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3).
Definition term25 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> ~ (forall y2 : nat, Peano.le y2 y2).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2) x3.
Definition term69 := Peano.le (NUMERAL 0).
Definition term9 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> False.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le y0 (Nat.div x0 x2)) -> Peano.le y0 (Nat.div x1 x2).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le y0 x1) -> (~ (x0 = (NUMERAL 0))) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.mul x0 y1) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False) x2.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.le (Nat.mul x1 y1) x0) -> Peano.le (Nat.mul x1 y1) x2) y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term55 (x0 : nat) (x1 : nat) := (Peano.le x0 x0) -> Peano.le x0 x1.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term16 := ~ (forall y0 : nat, Peano.le y0 y0).
Definition term23 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> ~ (forall y1 : nat, Peano.le y1 y1).
Definition term14 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le x1 x2).
Definition term76 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term67 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = y0) -> (y0 -> (Peano.le x1 (Nat.div x2 x3)) = y1) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le x1 (Nat.div x2 x3)) = (y0 -> y1)) x4.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> Peano.le x1 x2.
Definition term57 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term24 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> False.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.div x0 x2) (Nat.div x1 x2).
Definition term137 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term63 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term121 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y1 x0) -> (~ (y0 = (NUMERAL 0))) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.mul y0 y2) x0)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4).
Definition term120 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y1 x0) -> (~ (y0 = (NUMERAL 0))) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.mul y0 y2) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False.
Definition term176 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.mul x1 y0) x2)).
Definition term20 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> False.
Definition term155 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term133 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term125 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y2 y0) -> (~ (y1 = (NUMERAL 0))) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.mul y1 y3) y0)) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5).
Definition term124 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y2 y0) -> (~ (y1 = (NUMERAL 0))) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.mul y1 y3) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> False.
Definition term71 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term53 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) -> Peano.le x1 x2.
