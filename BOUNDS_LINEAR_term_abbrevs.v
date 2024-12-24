Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (forall y1 : nat, Peano.le (Nat.mul y0 y1) (Nat.add (Nat.mul x0 y1) x1))) x2.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2) x3.
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term49 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term68 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul (S x1) x2).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term106 (x0 : nat) (x1 : nat) := (Peano.le (Nat.mul (S x0) (S x1)) x1) -> False.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x0) -> ~ (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term140 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term138 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term119 (x0 : nat) (x1 : nat) := (forall y0 : nat, Peano.le (Nat.mul (S x0) y0) x1) -> False.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Nat.mul (S x0) y0) x1) (S x1).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul (Nat.add x0 x1) y0) x2).
Definition term54 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term51 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term41 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul (Nat.add x0 x1) y0) x2).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul (Nat.add x1 (S x0)) y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term143 (x0 : nat) (x1 : nat) := forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul x1 y1) y0)) = (Peano.le x0 x1).
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term71 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term37 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = (Peano.le x0 y0).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 (S x1)) x2.
Definition term75 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term29 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (forall y0 : nat, Peano.le (Nat.mul (Nat.add x1 (S x0)) y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term15 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term70 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term62 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x1 x2) (Nat.mul (S x0) x2)) (Nat.add (Nat.mul x1 x2) x3).
Definition term121 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul y0 y1) x1).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term56 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) -> ~ (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)) x3.
Definition term67 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term118 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x2) (Nat.add (Nat.mul (Nat.add x0 x1) x2) x3).
Definition term31 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul x1 y1) (Nat.add (Nat.mul y0 y1) x0)) (Nat.add x1 x2).
Definition term116 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1).
Definition term111 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul x0 (S x1)) x1).
Definition term47 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.add x1 (S x0)) x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x2) (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 x2) x3)).
Definition term145 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (forall y3 : nat, Peano.le (Nat.mul y0 y3) (Nat.add (Nat.mul y1 y3) y2)) = (Peano.le y0 y1).
Definition term144 (x0 : nat) := forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.le (Nat.mul x0 y2) (Nat.add (Nat.mul y0 y2) y1)) = (Peano.le x0 y0).
Definition term69 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term58 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term52 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term42 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term102 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul (S x0) y0) x1.
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul y0 y1) x1)) x2.
Definition term65 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul y0 y1) x1)) x2).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = (Peano.le x0 y0)) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term39 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term137 := forall y0 : nat, True.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x2) (Nat.mul (S x1) x2)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term60 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term136 := fun y0 : nat => True.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (S x0) x1) x2.
Definition term77 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term82 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term112 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term50 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term40 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ (forall y1 : nat, Peano.le (Nat.mul y0 y1) (Nat.add (Nat.mul x0 y1) x1))) x2).
Definition term115 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1.
Definition term132 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 x1).
Definition term35 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term17 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term74 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term64 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term53 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term43 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = (Peano.le y0 y1)) x0.
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2))).
Definition term117 (x0 : nat) (x1 : nat) := Peano.lt x1 (S (Nat.add (Nat.add x0 (Nat.mul x0 x1)) x1)).
Definition term85 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (forall y1 : nat, Peano.le (Nat.mul y0 y1) (Nat.add (Nat.mul x0 y1) x1)).
Definition term63 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term57 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul (Nat.add x1 (S x0)) y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := ((forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)) -> Peano.le x0 x1) /\ ((Peano.le x0 x1) -> forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul x1 y0) x2)).
Definition term113 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term120 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term24 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term81 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term100 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul (S x0) y0) x1.
Definition term46 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term110 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) (S x1).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul x2 y0) x0)) -> Peano.le x1 x2.
Definition term108 (x0 : nat) (x1 : nat) := Peano.lt x1 (Nat.mul (S x0) (S x1)).
Definition term139 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term103 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, Peano.le (Nat.mul (S x0) y0) x1).
Definition term66 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term76 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term105 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (S x0) (S x1)) x1.
Definition term114 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)) x1.
Definition term48 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term107 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.mul (S x0) (S x1)) x1).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (Nat.add x0 (S x1)) x2).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term33 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term109 (x0 : nat) (x1 : nat) := Nat.mul (S x0) (S x1).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (forall y1 : nat, Peano.le (Nat.mul y0 y1) (Nat.add (Nat.mul x1 y1) x0))) (Nat.add x1 (S x2)).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term44 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
