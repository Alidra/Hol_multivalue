Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := Peano.le (S (Nat.add x0 x0)) 0.
Definition term127 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term129 := (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) /\ (((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))))).
Definition term54 := fun y0 : nat => Peano.le 0 (S (Nat.add y0 y0)).
Definition term126 := (forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))))).
Definition term125 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term122 := (forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term104 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S (Nat.add x0 x0)) (S (Nat.add x1 x1))).
Definition term57 := and (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True).
Definition term49 := and (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True).
Definition term41 := and (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False).
Definition term53 := fun y0 : nat => (Peano.le 0 (BIT1 y0)) = True.
Definition term45 := fun y0 : nat => (Peano.le 0 (BIT0 y0)) = True.
Definition term114 := (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)).
Definition term113 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term108 (x0 : nat) := forall y0 : nat, (Peano.le (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term107 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term94 (x0 : nat) := forall y0 : nat, (Peano.le (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (Peano.lt x0 y0).
Definition term93 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term80 (x0 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term79 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term66 (x0 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x0) (Nat.add y0 y0)) = (Peano.le x0 y0).
Definition term65 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0).
Definition term10 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term105 (x0 : nat) := fun y0 : nat => (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term77 (x0 : nat) := fun y0 : nat => (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term63 (x0 : nat) := fun y0 : nat => (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0).
Definition term8 (x0 : nat) := fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term102 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x0)) (S (Nat.add x1 x1)).
Definition term4 (x0 : nat) := Peano.le (NUMERAL x0).
Definition term56 := forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0)).
Definition term42 := and (forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)).
Definition term106 (x0 : nat) := fun y0 : nat => (Peano.le (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term78 (x0 : nat) := fun y0 : nat => (Peano.le (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term34 (x0 : nat) := Peano.le (S (Nat.add x0 x0)).
Definition term26 := fun y0 : nat => (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0).
Definition term25 := fun y0 : nat => (Peano.le (BIT0 y0) 0) = (Peano.le y0 0).
Definition term36 (x0 : nat) := ~ (Peano.le (S (Nat.add x0 x0)) 0).
Definition term24 (x0 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) 0).
Definition term52 (x0 : nat) := Peano.le 0 (S (Nat.add x0 x0)).
Definition term44 (x0 : nat) := Peano.le 0 (Nat.add x0 x0).
Definition term89 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (BIT1 x0) (BIT0 x1)).
Definition term60 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x0) (Nat.add x1 x1).
Definition term51 (x0 : nat) := Peano.le 0 (BIT1 x0).
Definition term110 := fun y0 : nat => forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term109 := fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term96 := fun y0 : nat => forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1).
Definition term95 := fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term82 := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term81 := fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term68 := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1).
Definition term67 := fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1).
Definition term14 := fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term118 := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))).
Definition term117 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))).
Definition term2 (x0 : nat) := S (Nat.add x0 x0).
Definition term40 := forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0).
Definition term128 := (Peano.le 0 0) /\ ((forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))))))).
Definition term116 := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))).
Definition term115 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))).
Definition term74 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x0) (S (Nat.add x1 x1)).
Definition term23 (x0 : nat) := @eq Prop (Peano.le (BIT0 x0) 0).
Definition term32 (x0 : nat) := ~ (Peano.le (BIT1 x0) 0).
Definition term18 := and (Peano.le 0 0).
Definition term39 := forall y0 : nat, (Peano.le (BIT1 y0) 0) = False.
Definition term0 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term48 := forall y0 : nat, Peano.le 0 (Nat.add y0 y0).
Definition term58 := and (forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))).
Definition term50 := and (forall y0 : nat, Peano.le 0 (Nat.add y0 y0)).
Definition term30 := and (forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)).
Definition term29 := and (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term90 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S (Nat.add x0 x0)) (Nat.add x1 x1)).
Definition term28 := forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0).
Definition term27 := forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0).
Definition term112 := forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term111 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term98 := forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1).
Definition term97 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term84 := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term83 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term70 := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1).
Definition term69 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1).
Definition term15 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term101 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT1 x1).
Definition term33 (x0 : nat) := Peano.le (BIT1 x0).
Definition term92 (x0 : nat) := fun y0 : nat => (Peano.le (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (Peano.lt x0 y0).
Definition term11 := forall y0 : nat, True.
Definition term103 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (BIT1 x0) (BIT1 x1)).
Definition term17 := and ((Peano.le 0 0) = True).
Definition term20 (x0 : nat) := Peano.le (Nat.add x0 x0).
Definition term91 (x0 : nat) := fun y0 : nat => (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term76 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) (S (Nat.add x1 x1))).
Definition term9 := fun y0 : nat => True.
Definition term1 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term37 := fun y0 : nat => (Peano.le (BIT1 y0) 0) = False.
Definition term31 (x0 : nat) := Peano.le (BIT1 x0) 0.
Definition term7 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term46 := fun y0 : nat => Peano.le 0 (Nat.add y0 y0).
Definition term87 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT0 x1).
Definition term88 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x0)) (Nat.add x1 x1).
Definition term100 := and (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)).
Definition term99 := and (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)).
Definition term86 := and (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)).
Definition term85 := and (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term72 := and (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)).
Definition term71 := and (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)).
Definition term16 := and (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)).
Definition term38 := fun y0 : nat => ~ (Peano.le (S (Nat.add y0 y0)) 0).
Definition term21 (x0 : nat) := Peano.le (BIT0 x0) 0.
Definition term75 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (BIT0 x0) (BIT1 x1)).
Definition term5 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term61 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (BIT0 x0) (BIT0 x1)).
Definition term43 (x0 : nat) := Peano.le 0 (BIT0 x0).
Definition term62 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term13 (x0 : Prop) := forall y0 : nat, x0.
Definition term124 := (forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))))).
Definition term123 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term121 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term59 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT0 x1).
Definition term19 (x0 : nat) := Peano.le (BIT0 x0).
Definition term73 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT1 x1).
Definition term22 (x0 : nat) := Peano.le (Nat.add x0 x0) 0.
Definition term120 := (forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))).
Definition term130 := True /\ ((Peano.le 0 0) /\ ((forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))))))).
Definition term64 (x0 : nat) := fun y0 : nat => (Peano.le (Nat.add x0 x0) (Nat.add y0 y0)) = (Peano.le x0 y0).
Definition term119 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term55 := forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True.
Definition term47 := forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True.
Definition term6 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (NUMERAL x0) (NUMERAL x1)).
