Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term94 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x0 x1).
Definition term108 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (BIT0 x0) (BIT1 x1)).
Definition term23 := (forall y0 : nat, (Nat.add 0 y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term22 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term63 (x0 : nat) := @eq nat (Nat.add 0 (BIT0 x0)).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL x0) (NUMERAL x1).
Definition term47 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term75 := forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0).
Definition term80 := forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0).
Definition term155 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))))).
Definition term154 := (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))).
Definition term153 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))))).
Definition term152 := (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))).
Definition term151 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))).
Definition term150 := (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))).
Definition term90 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (Nat.add x1 x1).
Definition term156 := ((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))))).
Definition term135 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 x1) (S (Nat.add x0 x1))).
Definition term111 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)).
Definition term12 (x0 : nat) := @eq nat (Nat.add x0 0).
Definition term143 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))).
Definition term142 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))).
Definition term19 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term87 (x0 : nat) := Nat.add (BIT0 x0).
Definition term127 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT1 x1).
Definition term134 (x0 : nat) (x1 : nat) := Nat.add (S (Nat.add x0 x1)) (S (Nat.add x0 x1)).
Definition term25 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term38 (x0 : nat) := (fun y0 : nat => (Nat.add y0 0) = y0) x0.
Definition term73 (x0 : nat) := @eq nat (S (Nat.add x0 x0)).
Definition term97 (x0 : nat) := forall y0 : nat, (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0)).
Definition term59 := @eq nat (Nat.add 0 0).
Definition term128 (x0 : nat) (x1 : nat) := Nat.add (S (Nat.add x0 x0)) (S (Nat.add x1 x1)).
Definition term112 (x0 : nat) := fun y0 : nat => (Nat.add (BIT0 x0) (BIT1 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term65 := fun y0 : nat => (Nat.add 0 (BIT0 y0)) = (BIT0 y0).
Definition term110 (x0 : nat) (x1 : nat) := BIT1 (Nat.add x0 x1).
Definition term83 (x0 : nat) := @eq nat (Nat.add (BIT1 x0) 0).
Definition term78 (x0 : nat) := @eq nat (Nat.add (BIT0 x0) 0).
Definition term89 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 x1).
Definition term157 := (0 = 0) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))))))).
Definition term92 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term96 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 y0) (Nat.add x0 y0)).
Definition term122 (x0 : nat) := fun y0 : nat => (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term95 (x0 : nat) := fun y0 : nat => (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0)).
Definition term139 (x0 : nat) := forall y0 : nat, (Nat.add (BIT1 x0) (BIT1 y0)) = (BIT0 (S (Nat.add x0 y0))).
Definition term35 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term120 (x0 : nat) (x1 : nat) := Nat.add (S (Nat.add x0 x0)) (Nat.add x1 x1).
Definition term13 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term117 (x0 : nat) := Nat.add (BIT1 x0).
Definition term119 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT0 x1).
Definition term44 (x0 : nat) := Nat.add (NUMERAL x0).
Definition term133 (x0 : nat) (x1 : nat) := BIT0 (S (Nat.add x0 x1)).
Definition term54 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term147 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))).
Definition term146 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))).
Definition term50 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term41 (x0 : nat) := S (Nat.add x0 x0).
Definition term2 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term106 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (S (Nat.add x1 x1)).
Definition term51 (x0 : nat) := forall y0 : nat, (Nat.add (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.add x0 y0)).
Definition term15 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term145 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))).
Definition term144 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))).
Definition term121 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (BIT1 x0) (BIT0 x1)).
Definition term42 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term11 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term131 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (BIT1 x0) (BIT1 x1)).
Definition term109 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add (Nat.add x0 x0) (Nat.add x1 x1))).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term64 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term86 := and (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)).
Definition term81 := and (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)).
Definition term76 := and (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)).
Definition term70 := and (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)).
Definition term69 := and (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)).
Definition term68 := forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0).
Definition term52 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term71 (x0 : nat) := Nat.add 0 (BIT1 x0).
Definition term43 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term1 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term14 := fun y0 : nat => (Nat.add y0 0) = y0.
Definition term32 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term74 := fun y0 : nat => (Nat.add 0 (BIT1 y0)) = (BIT1 y0).
Definition term18 := and (forall y0 : nat, (Nat.add y0 0) = y0).
Definition term17 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term9 := and (forall y0 : nat, (Nat.add 0 y0) = y0).
Definition term8 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term141 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))).
Definition term125 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term115 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term102 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)).
Definition term101 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1)).
Definition term56 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term55 := forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1)).
Definition term33 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term27 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term82 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term46 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (NUMERAL x0) (NUMERAL x1)).
Definition term84 := fun y0 : nat => (Nat.add (BIT1 y0) 0) = (BIT1 y0).
Definition term85 := forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0).
Definition term7 := forall y0 : nat, (Nat.add 0 y0) = y0.
Definition term6 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term39 (x0 : nat) := (fun y0 : nat => (Nat.add 0 y0) = y0) x0.
Definition term136 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (S (Nat.add x0 x1)).
Definition term5 := fun y0 : nat => (Nat.add 0 y0) = y0.
Definition term118 (x0 : nat) := Nat.add (S (Nat.add x0 x0)).
Definition term98 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 y0) (Nat.add x0 y0)).
Definition term40 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term61 := and (0 = 0).
Definition term66 := fun y0 : nat => (Nat.add y0 y0) = (Nat.add y0 y0).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term21 := (forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term20 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term107 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term138 (x0 : nat) := fun y0 : nat => (Nat.add (BIT1 x0) (BIT1 y0)) = (BIT0 (S (Nat.add x0 y0))).
Definition term0 := Nat.add (NUMERAL 0).
Definition term126 := and (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))).
Definition term116 := and (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))).
Definition term104 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))).
Definition term103 := and (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))).
Definition term58 := and (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)).
Definition term57 := and (forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))).
Definition term132 (x0 : nat) (x1 : nat) := @eq nat (S (S (Nat.add (Nat.add x0 x0) (Nat.add x1 x1)))).
Definition term123 (x0 : nat) := forall y0 : nat, (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term113 (x0 : nat) := forall y0 : nat, (Nat.add (BIT0 x0) (BIT1 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term105 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT1 x1).
Definition term16 := forall y0 : nat, (Nat.add y0 0) = y0.
Definition term137 (x0 : nat) (x1 : nat) := S (S (Nat.add (Nat.add x0 x1) (Nat.add x0 x1))).
Definition term130 (x0 : nat) (x1 : nat) := S (S (Nat.add (Nat.add x0 x0) (Nat.add x1 x1))).
Definition term31 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term79 := fun y0 : nat => (Nat.add (BIT0 y0) 0) = (BIT0 y0).
Definition term88 (x0 : nat) := Nat.add (Nat.add x0 x0).
Definition term129 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 x0) (S (Nat.add x1 x1))).
Definition term140 := fun y0 : nat => forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))).
Definition term124 := fun y0 : nat => forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term114 := fun y0 : nat => forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term99 := fun y0 : nat => forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1)).
Definition term53 := fun y0 : nat => forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1)).
Definition term62 (x0 : nat) := Nat.add 0 (BIT0 x0).
Definition term67 := forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0).
Definition term93 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).
Definition term49 (x0 : nat) := fun y0 : nat => (Nat.add (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.add x0 y0)).
Definition term4 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term3 (x0 : nat) := @eq nat (Nat.add 0 x0).
Definition term159 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ ((0 = 0) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))))))).
Definition term158 := (forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))) /\ (((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))))).
Definition term72 (x0 : nat) := @eq nat (Nat.add 0 (BIT1 x0)).
Definition term91 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (BIT0 x0) (BIT0 x1)).
Definition term60 := and ((Nat.add 0 0) = 0).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term48 (x0 : nat) (x1 : nat) := NUMERAL (Nat.add x0 x1).
Definition term149 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))).
Definition term148 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
Definition term77 (x0 : nat) := Nat.add (BIT0 x0) 0.
Definition term37 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term100 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)).
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
