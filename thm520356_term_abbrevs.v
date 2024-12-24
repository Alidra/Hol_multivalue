Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT0 y0)) = True) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT1 y0)) = True) x0.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term108 (x0 : Prop) := ~ (~ x0).
Definition term99 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (BIT0 x0) (BIT0 x1)).
Definition term9 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term135 := (forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))).
Definition term10 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term125 (x0 : nat) (x1 : nat) := ~ (Peano.le (BIT1 x0) (BIT1 x1)).
Definition term90 := forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0).
Definition term64 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (NUMERAL x0) (NUMERAL x1)).
Definition term72 (x0 : nat) := Peano.lt (BIT0 x0) 0.
Definition term96 := and (forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True).
Definition term83 := and (forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False).
Definition term77 := and (forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False).
Definition term131 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)).
Definition term16 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term80 (x0 : nat) := ~ (Peano.le 0 (BIT1 x0)).
Definition term84 (x0 : nat) := Peano.lt 0 (BIT0 x0).
Definition term87 (x0 : nat) := @eq Prop (Peano.lt 0 (BIT0 x0)).
Definition term128 (x0 : nat) := forall y0 : nat, (Peano.lt (BIT1 x0) (BIT1 y0)) = (Peano.lt x0 y0).
Definition term120 (x0 : nat) := forall y0 : nat, (Peano.lt (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term112 (x0 : nat) := forall y0 : nat, (Peano.lt (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term101 (x0 : nat) := forall y0 : nat, (Peano.lt (BIT0 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term62 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0).
Definition term51 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term34 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0).
Definition term29 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term24 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term111 (x0 : nat) := fun y0 : nat => (Peano.lt (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term70 := ~ (Peano.le 0 0).
Definition term89 := fun y0 : nat => (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0).
Definition term124 (x0 : nat) (x1 : nat) := Peano.lt (BIT1 x0) (BIT1 x1).
Definition term105 (x0 : nat) (x1 : nat) := Peano.lt (BIT0 x0) (BIT1 x1).
Definition term118 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (BIT1 x0) (BIT0 x1)).
Definition term44 (x0 : nat) := (fun y0 : nat => (Peano.le (BIT1 y0) 0) = False) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) x0.
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (BIT0 x0) (BIT1 x1)).
Definition term79 (x0 : nat) := ~ (Peano.lt (BIT1 x0) 0).
Definition term73 (x0 : nat) := ~ (Peano.lt (BIT0 x0) 0).
Definition term117 (x0 : nat) (x1 : nat) := ~ (Peano.le (BIT0 x0) (BIT1 x1)).
Definition term69 := ~ (Peano.lt 0 0).
Definition term39 (x0 : nat) := Peano.le 0 (BIT1 x0).
Definition term129 := fun y0 : nat => forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1).
Definition term121 := fun y0 : nat => forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term113 := fun y0 : nat => forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term102 := fun y0 : nat => forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term66 := fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term133 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))).
Definition term14 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))).
Definition term94 := fun y0 : nat => (Peano.lt 0 (BIT1 y0)) = True.
Definition term139 := (forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) /\ (((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))))).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term132 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))).
Definition term15 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))).
Definition term93 (x0 : nat) := ~ (Peano.le (BIT1 x0) 0).
Definition term85 (x0 : nat) := ~ (Peano.le (BIT0 x0) 0).
Definition term82 := forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False.
Definition term76 := forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False.
Definition term43 := forall y0 : nat, (Peano.le (BIT1 y0) 0) = False.
Definition term86 (x0 : nat) := ~ (Peano.le x0 0).
Definition term91 := and (forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0)) x1.
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0)) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0)) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0)) x1.
Definition term126 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (BIT1 x0) (BIT1 x1)).
Definition term81 := fun y0 : nat => (Peano.lt (BIT1 y0) 0) = False.
Definition term75 := fun y0 : nat => (Peano.lt (BIT0 y0) 0) = False.
Definition term46 := forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0).
Definition term130 := forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1).
Definition term122 := forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term114 := forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term103 := forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term67 := forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1).
Definition term49 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term32 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1).
Definition term27 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term22 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term17 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term21 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT1 x1).
Definition term78 (x0 : nat) := Peano.lt (BIT1 x0) 0.
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term63 := forall y0 : nat, True.
Definition term92 (x0 : nat) := Peano.lt 0 (BIT1 x0).
Definition term138 := ((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))))).
Definition term88 (x0 : nat) := @eq Prop (~ (Peano.le x0 0)).
Definition term127 (x0 : nat) := fun y0 : nat => (Peano.lt (BIT1 x0) (BIT1 y0)) = (Peano.lt x0 y0).
Definition term119 (x0 : nat) := fun y0 : nat => (Peano.lt (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term100 (x0 : nat) := fun y0 : nat => (Peano.lt (BIT0 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term60 (x0 : nat) := fun y0 : nat => (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0).
Definition term61 := fun y0 : nat => True.
Definition term106 (x0 : nat) (x1 : nat) := ~ (Peano.le (BIT1 x0) (BIT0 x1)).
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0)) x1.
Definition term45 (x0 : nat) := Peano.le (BIT1 x0) 0.
Definition term110 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term26 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT0 x1).
Definition term98 (x0 : nat) (x1 : nat) := ~ (Peano.le (BIT0 x0) (BIT0 x1)).
Definition term123 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)).
Definition term115 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term104 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)).
Definition term68 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)).
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)) x0.
Definition term107 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term48 (x0 : nat) := Peano.le (BIT0 x0) 0.
Definition term74 (x0 : nat) := ~ (Peano.le 0 (BIT0 x0)).
Definition term116 (x0 : nat) (x1 : nat) := Peano.lt (BIT1 x0) (BIT0 x1).
Definition term53 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term42 (x0 : nat) := Peano.le 0 (BIT0 x0).
Definition term56 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL x0) (NUMERAL x1).
Definition term59 (x0 : nat) (x1 : nat) := @eq Prop (~ (Peano.le x0 x1)).
Definition term65 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term97 (x0 : nat) (x1 : nat) := Peano.lt (BIT0 x0) (BIT0 x1).
Definition term137 := (forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))).
Definition term136 := (forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))).
Definition term12 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term11 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term71 := and ((Peano.lt 0 0) = False).
Definition term36 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT0 x1).
Definition term31 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT1 x1).
Definition term134 := (forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))).
Definition term13 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term57 (x0 : nat) (x1 : nat) := ~ (Peano.le (NUMERAL x0) (NUMERAL x1)).
Definition term95 := forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True.
Definition term40 := forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True.
Definition term37 := forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True.
