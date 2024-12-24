Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term92 (x0 : nat) := True /\ (Peano.le x0 0).
Definition term96 := fun y0 : nat => (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0)).
Definition term134 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.le x0 x1).
Definition term116 (x0 : nat) (x1 : nat) := (Peano.le (BIT0 x1) (BIT1 x0)) /\ (Peano.le (BIT1 x0) (BIT0 x1)).
Definition term41 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT0 y0)) = True) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT1 y0)) = True) x0.
Definition term85 (x0 : nat) := (Peano.le (BIT1 x0) 0) /\ (Peano.le 0 (BIT1 x0)).
Definition term115 (x0 : nat) (x1 : nat) := ~ ((BIT0 x0) = (BIT1 x1)).
Definition term167 := True /\ ((forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0))) /\ ((forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)))))).
Definition term166 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term9 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term0 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term168 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term118 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.lt x0 x1).
Definition term164 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term160 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term10 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term130 (x0 : nat) (x1 : nat) := ~ ((BIT1 x0) = (BIT0 x1)).
Definition term78 := fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0).
Definition term97 := forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0).
Definition term65 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term106 := and (forall y0 : nat, (0 = (BIT1 y0)) = False).
Definition term89 := and (forall y0 : nat, ((BIT1 y0) = 0) = False).
Definition term156 := (forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))).
Definition term153 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term16 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term137 (x0 : nat) := fun y0 : nat => ~ ((Peano.lt x0 y0) /\ (Peano.le y0 x0)).
Definition term121 (x0 : nat) := fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0)).
Definition term1 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term79 := fun y0 : nat => (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0)).
Definition term150 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term111 (x0 : nat) := forall y0 : nat, ((BIT0 x0) = (BIT0 y0)) = (x0 = y0).
Definition term63 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term51 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term34 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0).
Definition term29 (x0 : nat) := forall y0 : nat, (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term24 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0).
Definition term3 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term146 (x0 : nat) (x1 : nat) := (Peano.le (BIT1 x1) (BIT1 x0)) /\ (Peano.le (BIT1 x0) (BIT1 x1)).
Definition term132 (x0 : nat) (x1 : nat) := and (Peano.le (BIT1 x0) (BIT0 x1)).
Definition term98 := forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0)).
Definition term95 := fun y0 : nat => (0 = (BIT0 y0)) = (0 = y0).
Definition term148 (x0 : nat) (x1 : nat) := @eq Prop ((BIT1 x0) = (BIT1 x1)).
Definition term44 (x0 : nat) := (fun y0 : nat => (Peano.le (BIT1 y0) 0) = False) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) x0.
Definition term149 (x0 : nat) := fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term110 (x0 : nat) := fun y0 : nat => ((BIT0 x0) = (BIT0 y0)) = (x0 = y0).
Definition term61 (x0 : nat) := fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term81 := forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0)).
Definition term138 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT0 y0)) = False.
Definition term122 (x0 : nat) := forall y0 : nat, ((BIT0 x0) = (BIT1 y0)) = False.
Definition term105 := forall y0 : nat, (0 = (BIT1 y0)) = False.
Definition term84 (x0 : nat) := ~ ((BIT1 x0) = 0).
Definition term2 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term56 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL x1) (NUMERAL x0)) /\ (Peano.le (NUMERAL x0) (NUMERAL x1)).
Definition term71 (x0 : nat) := (Peano.le (BIT0 x0) 0) /\ (Peano.le 0 (BIT0 x0)).
Definition term163 := True /\ ((forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))))).
Definition term39 (x0 : nat) := Peano.le 0 (BIT1 x0).
Definition term151 := fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term112 := fun y0 : nat => forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1).
Definition term67 := fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term5 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term157 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term14 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))).
Definition term158 := True /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)))).
Definition term155 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term15 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))).
Definition term77 (x0 : nat) := (Peano.le x0 0) /\ (Peano.le 0 x0).
Definition term88 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term43 := forall y0 : nat, (Peano.le (BIT1 y0) 0) = False.
Definition term57 (x0 : nat) (x1 : nat) := and (Peano.le (NUMERAL x0) (NUMERAL x1)).
Definition term100 := and (forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))).
Definition term99 := and (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)).
Definition term83 := and (forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0))).
Definition term82 := and (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)).
Definition term139 (x0 : nat) := forall y0 : nat, ~ ((Peano.lt x0 y0) /\ (Peano.le y0 x0)).
Definition term123 (x0 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0)).
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop ((BIT0 x0) = (BIT0 x1)).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0)) x1.
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT0 x0) (BIT0 y0)) = (Peano.le x0 y0)) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT0 x0) (BIT1 y0)) = (Peano.le x0 y0)) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT1 x0) (BIT1 y0)) = (Peano.le x0 y0)) x1.
Definition term161 := (forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)))).
Definition term136 (x0 : nat) := fun y0 : nat => ((BIT1 x0) = (BIT0 y0)) = False.
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0))) x1.
Definition term107 (x0 : nat) (x1 : nat) := (Peano.le (BIT0 x1) (BIT0 x0)) /\ (Peano.le (BIT0 x0) (BIT0 x1)).
Definition term80 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term46 := forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0).
Definition term152 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term143 := forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)).
Definition term142 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False.
Definition term127 := forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term126 := forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False.
Definition term113 := forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1).
Definition term68 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term49 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term32 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1).
Definition term27 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term22 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term17 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term7 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term21 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT1 x1).
Definition term120 (x0 : nat) := fun y0 : nat => ((BIT0 x0) = (BIT1 y0)) = False.
Definition term76 (x0 : nat) := @eq Prop (Peano.le x0 0).
Definition term64 := forall y0 : nat, True.
Definition term70 := and ((0 = 0) = True).
Definition term135 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x1 x0) /\ (Peano.le x0 x1)).
Definition term73 (x0 : nat) := and (Peano.le x0 0).
Definition term62 := fun y0 : nat => True.
Definition term108 (x0 : nat) (x1 : nat) := and (Peano.le (BIT0 x0) (BIT0 x1)).
Definition term74 (x0 : nat) := (Peano.le x0 0) /\ True.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0)) x1.
Definition term75 (x0 : nat) := @eq Prop ((BIT0 x0) = 0).
Definition term45 (x0 : nat) := Peano.le (BIT1 x0) 0.
Definition term93 (x0 : nat) := @eq Prop (0 = (BIT0 x0)).
Definition term119 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1)).
Definition term94 (x0 : nat) := (Peano.le 0 x0) /\ (Peano.le x0 0).
Definition term133 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term87 := fun y0 : nat => ((BIT1 y0) = 0) = False.
Definition term140 := fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False.
Definition term124 := fun y0 : nat => forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False.
Definition term147 (x0 : nat) (x1 : nat) := and (Peano.le (BIT1 x0) (BIT1 x1)).
Definition term26 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT0 x1).
Definition term60 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term145 := and (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))).
Definition term144 := and (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False).
Definition term129 := and (forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))).
Definition term128 := and (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False).
Definition term114 := and (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)).
Definition term69 := and (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)).
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0))) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)) x0.
Definition term165 := (forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0))) /\ ((forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))))).
Definition term48 (x0 : nat) := Peano.le (BIT0 x0) 0.
Definition term154 := (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))) /\ True.
Definition term86 (x0 : nat) := and (Peano.le (BIT1 x0) 0).
Definition term72 (x0 : nat) := and (Peano.le (BIT0 x0) 0).
Definition term102 (x0 : nat) := (Peano.le 0 (BIT1 x0)) /\ (Peano.le (BIT1 x0) 0).
Definition term4 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term131 (x0 : nat) (x1 : nat) := (Peano.le (BIT1 x1) (BIT0 x0)) /\ (Peano.le (BIT0 x0) (BIT1 x1)).
Definition term53 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term42 (x0 : nat) := Peano.le 0 (BIT0 x0).
Definition term90 (x0 : nat) := (Peano.le 0 (BIT0 x0)) /\ (Peano.le (BIT0 x0) 0).
Definition term91 (x0 : nat) := and (Peano.le 0 (BIT0 x0)).
Definition term141 := fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)).
Definition term125 := fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term104 := fun y0 : nat => (0 = (BIT1 y0)) = False.
Definition term66 (x0 : Prop) := forall y0 : nat, x0.
Definition term59 (x0 : nat) (x1 : nat) := @eq Prop ((NUMERAL x0) = (NUMERAL x1)).
Definition term103 (x0 : nat) := and (Peano.le 0 (BIT1 x0)).
Definition term162 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term12 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term11 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term36 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT0 x1).
Definition term31 (x0 : nat) (x1 : nat) := Peano.le (BIT0 x0) (BIT1 x1).
Definition term117 (x0 : nat) (x1 : nat) := and (Peano.le (BIT0 x0) (BIT1 x1)).
Definition term159 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term13 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term6 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term58 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term40 := forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True.
Definition term37 := forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True.
Definition term101 (x0 : nat) := ~ (0 = (BIT1 x0)).
