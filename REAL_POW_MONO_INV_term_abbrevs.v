Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term174 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term51 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 x0)) -> real_le (real_inv x0) (real_inv x1).
Definition term169 (x0 : real) := and (real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)).
Definition term141 (x0 : nat) := ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term122 (x0 : nat) := ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term16 (x0 : nat) (x1 : real) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1)) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term92 (x0 : nat) := (fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term79 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_inv (real_inv (real_pow x1 x0))) (real_inv (real_inv (real_pow x1 x2))).
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le y0 y2)) -> real_le (real_pow y1 y0) (real_pow y1 y2)) x0.
Definition term67 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term62 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term146 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term132 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term70 := real_of_num (NUMERAL 0).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1)) x0.
Definition term117 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term162 (x0 : real) (x1 : nat) := real_le (real_pow (real_inv x0) x1).
Definition term93 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term171 (x0 : real) := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)) /\ True.
Definition term52 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1).
Definition term20 := (forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1)) -> forall y0 : nat, forall y1 : real, forall y2 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le y0 y2)) -> real_le (real_pow y1 y0) (real_pow y1 y2).
Definition term161 (x0 : real) (x1 : nat) := real_le (real_inv (real_pow x0 x1)).
Definition term64 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term177 (x0 : real) := (~ ((real_of_num (NUMERAL 0)) = x0)) -> ((real_of_num (NUMERAL 0)) = x0) = False.
Definition term87 (x0 : real) (x1 : Prop) (x2 : nat) (x3 : real) := (x1 -> (fun y0 : real => real_le y0 (@COND real (x2 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0) /\ ((~ x1) -> (fun y0 : real => real_le y0 (@COND real (x2 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x3).
Definition term135 := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term116 := (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term106 (x0 : nat) (x1 : nat) := @eq Prop (real_le (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term57 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_inv y1) (real_inv y0)) -> forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y0)) -> real_le (real_inv y0) (real_inv y1).
Definition term34 := (forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term4 (x0 : real) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0).
Definition term69 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term97 (x0 : nat) := (fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term61 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term170 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)) /\ (Peano.le x1 x2).
Definition term129 (x0 : nat) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term110 (x0 : nat) := (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term149 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term175 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term140 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term121 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term94 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term164 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_pow (real_inv x1) x0) (real_pow (real_inv x1) x2).
Definition term56 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y0)) -> real_le (real_inv y0) (real_inv y1).
Definition term47 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_inv y1) (real_inv y0).
Definition term44 := forall y0 : real, forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1).
Definition term43 := forall y0 : real, forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1)).
Definition term27 := forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term18 (x0 : nat) := forall y0 : real, forall y1 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 y1)) -> real_le (real_pow y0 x0) (real_pow y0 y1).
Definition term46 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0)) x1.
Definition term65 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term38 (x0 : real) := fun y0 : nat => (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0).
Definition term158 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow (real_inv x0) x1).
Definition term63 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term180 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term152 (x0 : real) (x1 : nat) := real_inv (real_inv (real_pow x0 x1)).
Definition term182 (x0 : nat) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le x1 x0))) -> real_le (real_pow y0 x0) (real_pow y0 x1).
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 x1)) -> real_le (real_pow y0 x0) (real_pow y0 x1).
Definition term54 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_inv y1) (real_inv y0)) -> real_le (real_inv x0) (real_inv x1).
Definition term125 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term72 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term3 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term15 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term85 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term156 := real_lt (real_of_num (NUMERAL 0)).
Definition term133 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL 0)).
Definition term114 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL 0)).
Definition term99 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term130 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL 0))).
Definition term111 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL 0))).
Definition term179 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term101 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term83 (x0 : nat) (x1 : nat) := real_le (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term45 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1)) x0.
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term68 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term142 (x0 : nat) := @eq Prop ((fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term123 (x0 : nat) := @eq Prop ((fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term29 (x0 : real) := forall y0 : nat, (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term24 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) x0.
Definition term1 (x0 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv y0)) x0.
Definition term115 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le y0 (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := real_le x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term153 (x0 : real) (x1 : nat) := real_le (real_inv (real_inv (real_pow x0 x1))).
Definition term137 (x0 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term118 (x0 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term126 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (@COND real x0 x1 x2).
Definition term107 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (@COND real x0 x1 x2).
Definition term166 (x0 : nat) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_inv x1) x0)) /\ (real_le (real_pow (real_inv x1) x0) (real_pow (real_inv x1) x2)).
Definition term60 (x0 : real) := real_inv (real_inv x0).
Definition term55 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 x0)) -> real_le (real_inv x0) (real_inv y0).
Definition term49 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_inv y0) (real_inv x0).
Definition term0 := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv y0).
Definition term184 := forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ ((real_le y2 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le y1 y0))) -> real_le (real_pow y2 y0) (real_pow y2 y1).
Definition term183 (x0 : nat) := forall y0 : nat, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le y0 x0))) -> real_le (real_pow y1 x0) (real_pow y1 y0).
Definition term19 := forall y0 : nat, forall y1 : real, forall y2 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le y0 y2)) -> real_le (real_pow y1 y0) (real_pow y1 y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le x0 y0)) -> real_le (real_pow y1 x0) (real_pow y1 y0).
Definition term7 := forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1).
Definition term155 (x0 : nat) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_pow x1 x2))) /\ (real_le (real_inv (real_pow x1 x2)) (real_inv (real_pow x1 x0)))) -> real_le (real_inv (real_inv (real_pow x1 x0))) (real_inv (real_inv (real_pow x1 x2))).
Definition term77 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0.
Definition term131 := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL 0)).
Definition term112 := (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL 0)).
Definition term109 := fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0.
Definition term163 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_inv (real_pow x1 x0)) (real_inv (real_pow x1 x2)).
Definition term41 := fun y0 : real => forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1)).
Definition term37 (x0 : real) := fun y0 : nat => (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term172 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term58 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y0)) -> real_le (real_inv y0) (real_inv y1)) x0.
Definition term48 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_inv y1) (real_inv y0)) x0.
Definition term74 (x0 : real) (x1 : nat) (x2 : nat) := (real_le x0 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le x1 x2).
Definition term32 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term75 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term81 (x0 : real) (x1 : nat) := real_le (real_pow x0 x1).
Definition term6 := (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv y0)) -> forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv y0).
Definition term39 (x0 : real) := forall y0 : nat, (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term59 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 x0)) -> real_le (real_inv x0) (real_inv y0)) x1.
Definition term50 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_inv y0) (real_inv x0)) x1.
Definition term139 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term138 (x0 : nat) := (x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 (x0 : nat) := (x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term178 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0)).
Definition term82 (x0 : nat) := real_le (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term105 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term134 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term127 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) x0) /\ ((~ x1) -> (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) x2).
Definition term108 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) x0) /\ ((~ x1) -> (fun y0 : real => real_le (real_of_num (NUMERAL (BIT1 0))) y0) x2).
Definition term71 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term143 (x0 : nat) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term2 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0).
Definition term104 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL 0)) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term86 (x0 : nat) (x1 : Prop) (x2 : real) (x3 : real) := (fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (@COND real x1 x2 x3).
Definition term159 (x0 : real) (x1 : nat) := and (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_pow x0 x1))).
Definition term157 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_inv (real_pow x0 x1)).
Definition term13 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 x2)) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term30 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term5 (x0 : real) := (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv y0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x0).
Definition term26 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term42 := fun y0 : real => forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1).
Definition term66 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term14 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.le x1 x2).
Definition term17 (x0 : nat) (x1 : real) := forall y0 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 y0)) -> real_le (real_pow x1 x0) (real_pow x1 y0).
Definition term35 (x0 : real) (x1 : nat) := real_pow (real_inv x0) x1.
Definition term53 (x0 : real) (x1 : real) := real_le (real_inv x0) (real_inv x1).
Definition term88 (x0 : nat) := fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term90 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le y0 (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : real => real_le y0 (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term176 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term91 := real_of_num (NUMERAL (BIT1 0)).
Definition term124 (x0 : nat) := @eq Prop (real_le (real_of_num (NUMERAL (BIT1 0))) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term84 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term145 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le x0 y0)) -> real_le (real_pow y1 x0) (real_pow y1 y0)) x1.
Definition term100 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : real => real_le y0 (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 y0)) -> real_le (real_pow x1 x0) (real_pow x1 y0)) x2.
Definition term36 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term150 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term148 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term168 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_inv x1)) /\ (Peano.le x0 x2)) -> real_le (real_pow (real_inv x1) x0) (real_pow (real_inv x1) x2).
Definition term25 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term160 (x0 : real) (x1 : nat) := and (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_inv x0) x1)).
Definition term40 (x0 : real) := forall y0 : nat, (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0).
Definition term12 (x0 : nat) (x1 : nat) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 x1)) -> real_le (real_pow y0 x0) (real_pow y0 x1)) x2.
Definition term73 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le x1 x2)).
Definition term167 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) -> real_lt (real_of_num (NUMERAL 0)) (real_pow (real_inv x0) x1).
Definition term136 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term103 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term113 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term102 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : real => real_le y0 (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term78 (x0 : nat) := real_pow (real_of_num (NUMERAL 0)) x0.
Definition term33 (x0 : real) (x1 : nat) := (forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term80 := real_pow (real_of_num (NUMERAL 0)).
Definition term98 (x0 : nat) := real_le (real_of_num (NUMERAL (BIT1 0))) (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term151 := False -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> real_le (real_of_num (NUMERAL 0)) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term128 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0.
Definition term147 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term89 (x0 : nat) (x1 : nat) := (fun y0 : real => real_le y0 (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (@COND real (x1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term144 := NUMERAL (BIT1 0).
Definition term181 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_le x1 (real_of_num (NUMERAL (BIT1 0)))) /\ (Peano.le x2 x0))) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term165 (x0 : nat) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_inv (real_pow x1 x0))) /\ (real_le (real_inv (real_pow x1 x0)) (real_inv (real_pow x1 x2))).
Definition term173 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term22 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : nat, ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 y1)) -> real_le (real_pow y0 x0) (real_pow y0 y1)) x1.
