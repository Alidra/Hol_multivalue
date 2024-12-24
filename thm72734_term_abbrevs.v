Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term110 (x0 : nat) := (~ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0)))) -> (dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0)).
Definition term98 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term36 := and (NUM_REP IND_0).
Definition term85 := fun y0 : ind => (~ (NUM_REP y0)) \/ (NUM_REP (IND_SUC y0)).
Definition term120 (x0 : ind) := ~ (~ ((dest_num (mk_num x0)) = x0)).
Definition term166 (x0 : ind) (x1 : ind) := and (x0 = x1).
Definition term88 (x0 : ind) := (fun y0 : ind => ~ ((IND_SUC y0) = IND_0)) x0.
Definition term116 (x0 : nat) := (~ ((dest_num (mk_num (dest_num x0))) = (dest_num x0))) -> (dest_num (mk_num (dest_num x0))) = (dest_num x0).
Definition term45 (x0 : nat -> Prop) := ~ (all x0).
Definition term186 := (~ False) -> False.
Definition term14 := ~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0))).
Definition term64 (x0 : ind) := (fun y0 : ind => (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) x0.
Definition term76 := forall y0 : ind, (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0)).
Definition term91 (x0 : nat) (x1 : nat) := (x0 = x1) -> (dest_num x0) = (dest_num x1).
Definition term60 := forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0) /\ ((fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0).
Definition term9 := fun y0 : nat => ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)).
Definition term58 (x0 : ind -> Prop) (x1 : ind -> Prop) := forall y0 : ind, (x0 y0) /\ (x1 y0).
Definition term48 (x0 : nat) := (fun y0 : nat => ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0))) x0.
Definition term103 (x0 : Prop) := ~ (~ x0).
Definition term38 := fun y0 : nat => (mk_num (dest_num y0)) = y0.
Definition term112 (x0 : nat) := (~ ((mk_num (dest_num x0)) = x0)) -> (mk_num (dest_num x0)) = x0.
Definition term15 := (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term50 := fun y0 : nat => ~ ((fun y1 : nat => ~ ((mk_num (IND_SUC (dest_num y1))) = (mk_num IND_0))) y0).
Definition term8 := fun y0 : nat => ~ ((S y0) = 0).
Definition term66 (x0 : ind) := and ((fun y0 : ind => (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) x0).
Definition term163 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term63 := fun y0 : ind => (~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0).
Definition term108 (x0 : nat) := dest_num (mk_num (IND_SUC (dest_num x0))).
Definition term80 := forall y0 : ind, (fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0.
Definition term75 := forall y0 : ind, (fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0.
Definition term81 := forall y0 : ind, (~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0).
Definition term138 (x0 : nat) := (~ (NUM_REP (IND_SUC (dest_num x0)))) -> NUM_REP (IND_SUC (dest_num x0)).
Definition term12 (x0 : Prop) := (~ x0) -> False.
Definition term168 (x0 : ind) (x1 : ind) (x2 : ind) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term111 (x0 : nat) := ~ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0))).
Definition term114 (x0 : nat) := ((mk_num (dest_num x0)) = x0) -> (dest_num (mk_num (dest_num x0))) = (dest_num x0).
Definition term95 (x0 : nat) := (~ ((mk_num (IND_SUC (dest_num x0))) = (mk_num IND_0))) -> (mk_num (IND_SUC (dest_num x0))) = (mk_num IND_0).
Definition term171 (x0 : nat) := ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0))) /\ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0))).
Definition term113 (x0 : nat) := ~ ((mk_num (dest_num x0)) = x0).
Definition term101 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term49 (x0 : nat) := ~ ((fun y0 : nat => ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0))) x0).
Definition term142 (x0 : ind) := @eq Prop (((dest_num (mk_num x0)) = x0) \/ (~ (NUM_REP x0))).
Definition term22 := imp (forall y0 : nat, (mk_num (dest_num y0)) = y0).
Definition term177 := (NUM_REP IND_0) -> (dest_num (mk_num IND_0)) = IND_0.
Definition term135 (x0 : ind) := imp (NUM_REP x0).
Definition term183 (x0 : nat) := ~ ((IND_SUC (dest_num x0)) = IND_0).
Definition term179 := ~ ((dest_num (mk_num IND_0)) = IND_0).
Definition term20 := ~ ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))).
Definition term43 := forall y0 : ind, ~ ((IND_SUC y0) = IND_0).
Definition term77 := and (forall y0 : ind, (fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0).
Definition term42 := fun y0 : ind => ~ ((IND_SUC y0) = IND_0).
Definition term173 (x0 : nat) := (~ ((dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0)))) -> (dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0)).
Definition term96 (x0 : Prop) := (~ x0) -> x0.
Definition term132 (x0 : ind) := (~ (~ (NUM_REP x0))) -> NUM_REP (IND_SUC x0).
Definition term127 (x0 : nat) := ~ (NUM_REP (dest_num x0)).
Definition term159 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term33 (x0 : ind) := (NUM_REP x0) -> NUM_REP (IND_SUC x0).
Definition term161 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term185 (x0 : nat) := ((IND_SUC (dest_num x0)) = IND_0) -> False.
Definition term6 (x0 : nat) := ~ ((S x0) = 0).
Definition term82 := (forall y0 : ind, (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) /\ (forall y0 : ind, (~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0)).
Definition term156 (x0 : ind) (x1 : ind) (x2 : ind) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term136 (x0 : nat) := (NUM_REP (dest_num x0)) -> NUM_REP (IND_SUC (dest_num x0)).
Definition term157 (x0 : ind) (x1 : ind) (x2 : ind) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term86 := forall y0 : ind, (~ (NUM_REP y0)) \/ (NUM_REP (IND_SUC y0)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term59 (x0 : ind -> Prop) (x1 : ind -> Prop) := (forall y0 : ind, x0 y0) /\ (forall y0 : ind, x1 y0).
Definition term151 (x0 : ind) (x1 : ind) := ~ (x0 = x1).
Definition term147 (x0 : nat) := (~ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0)))) -> (dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0)).
Definition term133 (x0 : ind) := ~ (~ (NUM_REP x0)).
Definition term154 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term170 (x0 : ind) (x1 : ind) (x2 : ind) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term100 (x0 : nat) (x1 : nat) := @eq Prop (((dest_num x0) = (dest_num x1)) \/ (~ (x0 = x1))).
Definition term176 := ~ (NUM_REP IND_0).
Definition term83 (x0 : ind) := (~ (NUM_REP x0)) \/ (NUM_REP (IND_SUC x0)).
Definition term44 (x0 : nat) := ~ (~ ((mk_num (IND_SUC (dest_num x0))) = (mk_num IND_0))).
Definition term10 := forall y0 : nat, ~ ((S y0) = 0).
Definition term119 (x0 : ind) := ~ ((dest_num (mk_num x0)) = x0).
Definition term97 (x0 : nat) (x1 : nat) := ((dest_num x0) = (dest_num x1)) \/ (~ (x0 = x1)).
Definition term11 := forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)).
Definition term41 (x0 : ind) := ~ ((IND_SUC x0) = IND_0).
Definition term115 (x0 : nat) := dest_num (mk_num (dest_num x0)).
Definition term94 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term140 (x0 : ind) := ((dest_num (mk_num x0)) = x0) \/ (~ (NUM_REP x0)).
Definition term68 (x0 : ind) := (fun y0 : ind => (~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0)) x0.
Definition term180 (x0 : nat) := ((dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0))) /\ ((dest_num (mk_num IND_0)) = IND_0).
Definition term34 := fun y0 : ind => (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term174 (x0 : nat) := ~ ((dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0))).
Definition term18 := (((~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> ((~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term118 (x0 : ind) := (~ (~ ((dest_num (mk_num x0)) = x0))) -> NUM_REP x0.
Definition term175 := (~ (NUM_REP IND_0)) -> NUM_REP IND_0.
Definition term106 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term181 (x0 : nat) := (((dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0))) /\ ((dest_num (mk_num IND_0)) = IND_0)) -> (IND_SUC (dest_num x0)) = IND_0.
Definition term90 (x0 : ind) := (fun y0 : ind => (~ (NUM_REP y0)) \/ (NUM_REP (IND_SUC y0))) x0.
Definition term87 := (NUM_REP IND_0) /\ (forall y0 : ind, (~ (NUM_REP y0)) \/ (NUM_REP (IND_SUC y0))).
Definition term21 := (NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)).
Definition term124 (x0 : nat) := ((dest_num (mk_num (dest_num x0))) = (dest_num x0)) -> NUM_REP (dest_num x0).
Definition term74 := fun y0 : ind => (fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0.
Definition term160 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term130 (x0 : ind) := @eq Prop ((~ (NUM_REP x0)) \/ (NUM_REP (IND_SUC x0))).
Definition term65 (x0 : ind) := (NUM_REP x0) \/ (~ ((dest_num (mk_num x0)) = x0)).
Definition term25 := imp (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)).
Definition term2 (x0 : nat) := (fun y0 : nat => (S y0) = (mk_num (IND_SUC (dest_num y0)))) x0.
Definition term155 (x0 : ind) (x1 : ind) (x2 : ind) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term17 := (((~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term28 := imp (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)).
Definition term128 (x0 : ind) := (NUM_REP (IND_SUC x0)) \/ (~ (NUM_REP x0)).
Definition term19 := ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term145 (x0 : nat) := (NUM_REP (IND_SUC (dest_num x0))) -> (dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0)).
Definition term182 (x0 : nat) := (~ ((IND_SUC (dest_num x0)) = IND_0)) -> (IND_SUC (dest_num x0)) = IND_0.
Definition term178 := (~ ((dest_num (mk_num IND_0)) = IND_0)) -> (dest_num (mk_num IND_0)) = IND_0.
Definition term16 := ((~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False) -> (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term172 (x0 : nat) := (((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0))) /\ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0)))) -> (dest_num (mk_num IND_0)) = (IND_SUC (dest_num x0)).
Definition term13 := (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> False.
Definition term67 (x0 : ind) := and ((NUM_REP x0) \/ (~ ((dest_num (mk_num x0)) = x0))).
Definition term62 := fun y0 : ind => (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0)).
Definition term70 (x0 : ind) := ((fun y0 : ind => (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) x0) /\ ((fun y0 : ind => (~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0)) x0).
Definition term167 (x0 : ind) (x1 : ind) (x2 : ind) := (x1 = x0) /\ (x1 = x2).
Definition term126 (x0 : nat) := (~ (NUM_REP (dest_num x0))) -> NUM_REP (dest_num x0).
Definition term153 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term109 := dest_num (mk_num IND_0).
Definition term129 (x0 : ind) := ~ (NUM_REP x0).
Definition term184 (x0 : ind) := ((IND_SUC x0) = IND_0) -> False.
Definition term165 (x0 : ind) (x1 : ind) := and (~ (~ (x0 = x1))).
Definition term150 (x0 : ind) (x1 : ind) (x2 : ind) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term141 (x0 : ind) := @eq Prop ((~ (NUM_REP x0)) \/ ((dest_num (mk_num x0)) = x0)).
Definition term78 := and (forall y0 : ind, (NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))).
Definition term0 := forall y0 : nat, (mk_num (dest_num y0)) = y0.
Definition term4 (x0 : nat) := @eq nat (S x0).
Definition term102 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (dest_num x0) = (dest_num x1).
Definition term134 (x0 : ind) := imp (~ (~ (NUM_REP x0))).
Definition term39 (x0 : ind) := dest_num (mk_num x0).
Definition term53 (x0 : ind) := ((NUM_REP x0) \/ (~ ((dest_num (mk_num x0)) = x0))) /\ ((~ (NUM_REP x0)) \/ ((dest_num (mk_num x0)) = x0)).
Definition term107 (x0 : nat) := ((mk_num (IND_SUC (dest_num x0))) = (mk_num IND_0)) -> (dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num IND_0)).
Definition term117 (x0 : nat) := ~ ((dest_num (mk_num (dest_num x0))) = (dest_num x0)).
Definition term5 (x0 : nat) := @eq nat (mk_num (IND_SUC (dest_num x0))).
Definition term3 (x0 : nat) := mk_num (IND_SUC (dest_num x0)).
Definition term61 := (forall y0 : ind, (fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0) /\ (forall y0 : ind, (fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0).
Definition term23 := (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term84 (x0 : ind) := NUM_REP (IND_SUC x0).
Definition term131 (x0 : ind) := @eq Prop ((NUM_REP (IND_SUC x0)) \/ (~ (NUM_REP x0))).
Definition term69 (x0 : ind) := (~ (NUM_REP x0)) \/ ((dest_num (mk_num x0)) = x0).
Definition term99 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((dest_num x0) = (dest_num x1))).
Definition term122 (x0 : ind) := imp ((dest_num (mk_num x0)) = x0).
Definition term54 := fun y0 : ind => ((NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) /\ ((~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0)).
Definition term162 (x0 : ind) (x1 : ind) (x2 : ind) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term143 (x0 : ind) := (~ (~ (NUM_REP x0))) -> (dest_num (mk_num x0)) = x0.
Definition term47 := exists y0 : nat, ~ ((fun y1 : nat => ~ ((mk_num (IND_SUC (dest_num y1))) = (mk_num IND_0))) y0).
Definition term55 := forall y0 : ind, ((NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) /\ ((~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0)).
Definition term30 := (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ~ ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))).
Definition term144 (x0 : ind) := (NUM_REP x0) -> (dest_num (mk_num x0)) = x0.
Definition term137 (x0 : nat) := NUM_REP (IND_SUC (dest_num x0)).
Definition term92 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term73 := @eq Prop (forall y0 : ind, ((NUM_REP y0) \/ (~ ((dest_num (mk_num y0)) = y0))) /\ ((~ (NUM_REP y0)) \/ ((dest_num (mk_num y0)) = y0))).
Definition term72 := @eq Prop (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0) /\ ((fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0)).
Definition term93 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((dest_num x0) = (dest_num x1)).
Definition term27 := (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ~ ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))).
Definition term123 (x0 : ind) := ((dest_num (mk_num x0)) = x0) -> NUM_REP x0.
Definition term149 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term169 (x0 : ind) (x1 : ind) (x2 : ind) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term125 (x0 : nat) := NUM_REP (dest_num x0).
Definition term52 := exists y0 : nat, (mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0).
Definition term40 := fun y0 : ind => (NUM_REP y0) = ((dest_num (mk_num y0)) = y0).
Definition term35 := forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term32 := (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))) -> (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ~ ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))).
Definition term51 := fun y0 : nat => (mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0).
Definition term29 := (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)) -> (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term24 := (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ~ ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))).
Definition term79 := fun y0 : ind => (fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0.
Definition term164 (x0 : ind) (x1 : ind) := ~ (~ (x0 = x1)).
Definition term104 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term71 := fun y0 : ind => ((fun y1 : ind => (NUM_REP y1) \/ (~ ((dest_num (mk_num y1)) = y1))) y0) /\ ((fun y1 : ind => (~ (NUM_REP y1)) \/ ((dest_num (mk_num y1)) = y1)) y0).
Definition term152 (x0 : ind) (x1 : ind) := or (~ (x0 = x1)).
Definition term7 (x0 : nat) := ~ ((mk_num (IND_SUC (dest_num x0))) = (mk_num IND_0)).
Definition term89 (x0 : nat) := (fun y0 : nat => (mk_num (dest_num y0)) = y0) x0.
Definition term158 (x0 : ind) (x1 : ind) (x2 : ind) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term139 (x0 : nat) := ~ (NUM_REP (IND_SUC (dest_num x0))).
Definition term37 (x0 : nat) := mk_num (dest_num x0).
Definition term26 := (forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0)) -> (forall y0 : nat, (mk_num (dest_num y0)) = y0) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) -> False.
Definition term148 (x0 : nat) := ~ ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (IND_SUC (dest_num x0))).
Definition term46 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term146 (x0 : nat) := IND_SUC (dest_num x0).
Definition term1 := forall y0 : ind, (NUM_REP y0) = ((dest_num (mk_num y0)) = y0).
Definition term31 := imp (~ (forall y0 : nat, ~ ((mk_num (IND_SUC (dest_num y0))) = (mk_num IND_0)))).
Definition term121 (x0 : ind) := imp (~ (~ ((dest_num (mk_num x0)) = x0))).
Definition term105 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
