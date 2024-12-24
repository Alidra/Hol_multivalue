Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term246 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0)).
Definition term176 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term207 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term260 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term188 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term141 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term65 (x0 : nat -> Prop) := ~ (all x0).
Definition term251 := (~ False) -> False.
Definition term90 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) x1).
Definition term144 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term229 (x0 : Prop) := ~ (~ x0).
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term172 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term167 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ ((forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))))).
Definition term57 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term25 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term78 := fun y0 : nat => exists y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term102 (x0 : nat) := or (exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))).
Definition term177 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term106 (x0 : nat) := (exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) \/ (exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term136 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.lt (NUMERAL 0) x0).
Definition term1 (x0 : Prop) := (~ x0) -> False.
Definition term178 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term100 (x0 : nat) := exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term250 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> False.
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x1 = x2)).
Definition term19 := imp ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term187 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (Peano.lt (NUMERAL 0) y0)) x1.
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3))).
Definition term261 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term222 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term232 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term259 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term64 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (Peano.lt (NUMERAL 0) x1))) \/ ((~ (Peano.lt (Nat.modulo x0 x1) x1)) /\ (Peano.lt (NUMERAL 0) x1)).
Definition term67 (x0 : nat) := ~ (forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (Peano.lt (NUMERAL 0) y0)).
Definition term17 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term4 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1)).
Definition term72 (x0 : nat) := fun y0 : nat => ((Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term168 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term55 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term50 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term14 := imp (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term199 (x0 : Prop) := (~ x0) -> x0.
Definition term184 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term171 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term116 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) x0) \/ ((fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) x0).
Definition term0 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term34 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term252 (x0 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ (Peano.lt (NUMERAL 0) x0)).
Definition term185 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term226 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term111 := fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1)).
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term255 (x0 : nat) := ~ (~ (Peano.lt (NUMERAL 0) x0)).
Definition term115 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) x0.
Definition term113 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) x0.
Definition term201 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0)) -> ~ (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0)).
Definition term112 := fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term202 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) (NUMERAL 0).
Definition term155 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term146 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term54 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term125 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0.
Definition term120 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term205 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term139 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.lt x1 x2)).
Definition term138 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term62 := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term169 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term235 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term88 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) x1.
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term12 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term119 := @eq Prop (exists y0 : nat, (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1))).
Definition term118 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0)).
Definition term97 (x0 : nat) := @eq Prop (exists y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0))).
Definition term96 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0)).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3)).
Definition term236 (x0 : nat) (x1 : nat) := and (~ (Peano.lt x0 x1)).
Definition term197 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> (Nat.modulo x0 x1) = (Nat.modulo x0 x1).
Definition term13 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term211 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term181 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0))) x0.
Definition term254 (x0 : nat) := (~ (~ (Peano.lt (NUMERAL 0) x0))) -> ~ (x0 = (NUMERAL 0)).
Definition term110 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term85 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term16 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term247 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term98 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term137 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term8 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term166 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term164 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term162 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term160 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term158 := and (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term56 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term51 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term46 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term41 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term36 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term15 := imp (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term10 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term6 := ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term105 (x0 : nat) := exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term243 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)) /\ ((~ (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term161 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))).
Definition term42 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x2 x3) = (Peano.lt x0 x1)) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term49 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term134 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term182 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)) x0.
Definition term23 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term27 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term135 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term225 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term180 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term174 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term18 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term2 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1).
Definition term73 (x0 : nat) := exists y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term22 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term150 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3).
Definition term108 := exists y0 : nat, (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term87 (x0 : nat) := fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0).
Definition term109 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term84 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term258 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term143 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term44 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term61 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (Peano.lt (NUMERAL 0) y0).
Definition term244 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = (Nat.modulo x0 x1)) /\ ((~ (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) -> ~ (x1 = (NUMERAL 0)).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term124 := or (exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))).
Definition term3 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> False.
Definition term77 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) = (Peano.lt (NUMERAL 0) y2)) y0).
Definition term53 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term92 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0)) x1.
Definition term89 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (Peano.lt (NUMERAL 0) x1)).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term39 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term245 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term157 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term148 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term249 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0.
Definition term145 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term140 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term104 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term99 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0.
Definition term91 (x0 : nat) (x1 : nat) := or ((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (Peano.lt (NUMERAL 0) x1))).
Definition term231 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = x0) /\ ((~ (Peano.lt x0 x3)) /\ (Peano.lt x1 x2))) -> ~ (x2 = x3).
Definition term107 := fun y0 : nat => (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term198 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term189 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term159 := (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term37 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term45 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term32 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term9 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term117 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0).
Definition term63 (x0 : nat) (x1 : nat) := ~ ((Peano.lt (Nat.modulo x0 x1) x1) = (Peano.lt (NUMERAL 0) x1)).
Definition term76 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1)) x0).
Definition term208 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term114 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) x0).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x1 = x0)) \/ ((Peano.lt x0 x3) \/ (~ (Peano.lt x1 x2))))) -> ~ (x2 = x3).
Definition term183 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term75 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1)) x0.
Definition term163 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))).
Definition term47 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term40 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term35 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term11 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term142 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term5 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term175 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term60 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (Peano.lt (NUMERAL 0) y0).
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term74 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) = (Peano.lt (NUMERAL 0) y2)) y0).
Definition term68 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) = (Peano.lt (NUMERAL 0) y1)) y0).
Definition term152 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term200 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0)).
Definition term128 := (exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ (exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((~ (x2 = x0)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term193 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term58 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term33 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) /\ (~ (~ (Peano.lt x2 x3))).
Definition term20 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term149 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term186 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) x0).
Definition term93 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term257 (x0 : nat) := imp (Peano.lt (NUMERAL 0) x0).
Definition term126 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0.
Definition term121 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0.
Definition term38 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term127 := exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1).
Definition term122 := exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1)).
Definition term79 := exists y0 : nat, exists y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)).
Definition term82 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term71 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) = (Peano.lt (NUMERAL 0) y1)) y0).
Definition term70 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (Peano.lt (NUMERAL 0) y0)) x1).
Definition term30 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term48 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term170 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term262 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> False.
Definition term248 (x0 : nat) := @eq Prop ((Peano.lt (NUMERAL 0) x0) \/ (x0 = (NUMERAL 0))).
Definition term21 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term95 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0).
Definition term123 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0).
Definition term101 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0).
Definition term133 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term230 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term94 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) x1) \/ ((fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0)) x1).
Definition term28 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term213 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term154 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term151 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term165 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))))).
Definition term52 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term31 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term242 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) (NUMERAL 0))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term59 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term66 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term156 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term147 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term253 (x0 : nat) := @eq Prop ((~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term179 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term173 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term29 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term86 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0)).
Definition term43 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term83 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term24 := imp (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (Peano.lt (NUMERAL 0) y1))).
Definition term256 (x0 : nat) := imp (~ (~ (Peano.lt (NUMERAL 0) x0))).
Definition term203 (x0 : Prop) := x0 -> ~ x0.
Definition term153 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term204 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term103 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term132 (x0 : nat) := @eq Prop ((exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (~ (Peano.lt (NUMERAL 0) y0))) \/ (exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (Peano.lt (NUMERAL 0) y0))).
Definition term131 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1)) y0)).
Definition term130 := @eq Prop ((exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (~ (Peano.lt (NUMERAL 0) y1))) \/ (exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (Peano.lt (NUMERAL 0) y1))).
Definition term129 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (~ (Peano.lt (NUMERAL 0) y2))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (Peano.lt (NUMERAL 0) y2)) y0)).
